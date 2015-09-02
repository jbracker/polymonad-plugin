
-- | The functions that actually solve the wanted polymonad constraints.
module Control.Polymonad.Plugin.Solve
  ( topologicalTyConOrder
  , solve
  ) where

import Data.Maybe ( fromJust )
import Data.List ( nubBy, find )
import Data.Graph.Inductive
  ( Graph(..), Gr
  , Node, LNode, LEdge )
import Data.Graph.Inductive.Graph
  ( delNode, insEdges, delEdge, delEdges
  , indeg, gelem
  , edges
  , nmap
  , out, inn )

import Control.Arrow ( (***) )

import Type ( TyVar, Type, eqType, getTyVar_maybe, getTyVar, mkTyVarTy )
import TcRnTypes ( Ct(..), CtLoc, CtEvidence(..) )

import Control.Polymonad.Plugin.Utils ( isAmbiguousType, removeDup )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , assert
  , throwPluginError
  , printObj )
import Control.Polymonad.Plugin.PrincipalJoin ( principalJoinFor )
import Control.Polymonad.Plugin.Constraint ( mkDerivedTypeEqCt', constraintPolymonadTyArgs' )
import Control.Polymonad.Plugin.GraphView

substToCts :: CtLoc -> [(TyVar, Type)] -> [Ct]
substToCts loc = fmap (uncurry $ mkDerivedTypeEqCt' loc)

-- | Given the set of wanted constraints that shall be solved this produces
--   a set of derived constraints that link the ambiguous type variables to
--   their principal joins.
solve :: [Ct] -> PmPluginM [Ct]
solve [] = return []
solve wantedCts = do
  -- Order in which we shall process the ambiguous type variables.
  topoOrder <- filter isAmbiguousType <$> topologicalTyConOrder (mkGraphView wantedCts)
  subst <- calcSubst [] $ fmap (getTyVar "solve: Not a type variable") topoOrder
  return $ substToCts (ctev_loc . cc_ev . head $ wantedCts) subst
  where
    -- Involved type constructors
    constraintTys :: [(Ct, Type, Type, Type)]
    constraintTys = constraintPolymonadTyArgs' wantedCts

    inTypes :: TyVar -> [(Type, Type)]
    inTypes t = (\(_, t0, t1, _) -> (t0, t1)) <$>
      filter (\(_, _, _, t2) -> eqType t2 (mkTyVarTy t)) constraintTys

    outTypes :: TyVar -> [Type]
    outTypes t = nubBy eqType $ (\(_, _, _, t2) -> t2) <$>
      filter (\(_, t0, t1, _) -> eqType t0 (mkTyVarTy t) || eqType t1 (mkTyVarTy t)) constraintTys

    -- Applies the given substitution to a given type.
    -- Only substitutes if the given type is a type variables.
    -- Does not look inside of type constructors.
    applySubst :: [(TyVar, Type)] -> Type -> Type
    applySubst [] t = t
    applySubst ((tvSub, tSub):substs) t = case getTyVar_maybe t of
      Just tv -> if tv == tvSub then tSub else applySubst substs t
      Nothing -> t

    calcSubst :: [(TyVar, Type)] -> [TyVar] -> PmPluginM [(TyVar, Type)]
    calcSubst subst [] = return subst
    calcSubst subst (tv:tvs) = do
      -- Get the outgoing types of the current type.
      let outTys -- Make sure that if there are is another ambiguous type variables
                 -- among the outgoing types to remove it. This is important,
                 -- because that other ambigous type variable will never match
                 -- any instances. FIXME: This is a hack. I do not know if this is the right thing to do.
                 = filter (\t -> not (isAmbiguousType t && not (eqType t $ mkTyVarTy tv)))
                   -- Get the outgoing types of the current type.
                 $ (applySubst subst) <$> outTypes tv
      -- Check of there are exactly one or two outgoing types.
      assert (length outTys == 1 || length outTys == 2)
        "solve: There are either no or more then two outgoing types of a type variable."
      let inTys = (applySubst subst *** applySubst subst) <$> inTypes tv
      -- Calculate the principal join. Be sure the
      -- already solved type variables are replaced with their solution
      -- before calculating the principal join.
      mJoin <- principalJoinFor (Just tv) inTys outTys
      case mJoin of
        Just join -> do
          -- We found a principal join, proceed solving the other variables.
          restSubst <- calcSubst ((tv, join) : subst) tvs
          -- Returns the full subtitution.
          return $ (tv, join) : restSubst
        Nothing -> throwPluginError "solve: Could not find a principal join."


-- | Calculate the topological order of the type constructors involved with
--   the given polymonad constraints. The given constraints should be the
--   wanted polymonad constraints.
topologicalTyConOrder :: GraphView -> PmPluginM [Type]
topologicalTyConOrder gv = printObj (labNodes collapsedGraph, labEdges collapsedGraph) >> orderNodes collapsedGraph
  where
    collapsedGraph = removeReflEdges -- Now we have a lot of loop that need removing.
                   $ collapseUnifEdges -- Collapse all nodes linked by unification edges into a single node
                   $ convNodeTypes -- Label nodes with their type
                   $ gvGraph gv -- Look at the graph

    orderNodes :: Gr Type EdgeType -> PmPluginM [Type]
    orderNodes gr = if isEmpty gr
      then return []
      else case find (\(n, _) -> indeg gr n == 0) $ labNodes gr of
        Just (n, ty) -> do
          restTys <- orderNodes $ delNode n gr
          return $ ty : restTys
        Nothing -> throwPluginError "topologicalTyConOrder: No nodes with zero in-degree. There was a cycle!"

    removeReflEdges :: Gr a b -> Gr a b
    removeReflEdges g = delEdges (filter (uncurry (==)) $ edges g) g

    convNodeTypes :: Gr PiNode e -> Gr Type e
    convNodeTypes = nmap (fromJust . piNodeType gv)

    collapseUnifEdges :: Gr Type EdgeType -> Gr Type EdgeType
    collapseUnifEdges gr = foldr collapseUnifEdge gr (labEdges gr)

    collapseUnifEdge :: LEdge EdgeType -> Gr Type EdgeType -> Gr Type EdgeType
    collapseUnifEdge (_, _, Bind) g = g
    collapseUnifEdge (n, m, Unif) g = if gelem n g && gelem m g
      then
        let mEdges = out g m ++ inn g m -- All adjacent edges of m
            -- Replace all occurences of m in the adjacent edges with n.
            newNEdges = (\(k, l, e) -> (if k == m then n else l, if l == m then n else l, e)) <$> mEdges
        in delNode m -- At last, remove m and with it all adjacent edges.
         $ insEdges newNEdges -- Then link all nodes currently linked with m to n
         $ delEdge (n, m) g -- First, remove the unification edge
      else g
