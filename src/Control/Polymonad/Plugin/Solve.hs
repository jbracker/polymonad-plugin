
module Control.Polymonad.Plugin.Solve
  ( topologicalTyConOrder
  , solve
  ) where

import Data.Maybe ( catMaybes )
import Data.List ( nubBy, find )
import Data.Graph.Inductive
  ( Graph(..), Gr
  , Node, LNode, LEdge )
import Data.Graph.Inductive.Graph
  ( delNode
  , indeg )

import Control.Arrow ( (***) )

import Type ( TyVar, Type, eqType, getTyVar_maybe, getTyVar, mkTyVarTy )
import TcRnTypes ( Ct(..), CtLoc, CtEvidence(..) )

import Control.Polymonad.Plugin.Utils ( isAmbiguousType, removeDup )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , printObj
  , getCurrentPolymonad
  , throwPluginError )
import Control.Polymonad.Plugin.PrincipalJoin ( principalJoinFor )
import Control.Polymonad.Plugin.Constraint ( mkDerivedTypeEqCt', constraintPolymonadTyArgs' )

substToCts :: CtLoc -> [(TyVar, Type)] -> [Ct]
substToCts loc = fmap (uncurry $ mkDerivedTypeEqCt' loc)

-- Given the set of wanted constraints that shall be solved this produces
-- a set of derived constraints that link the ambiguous type variables to
-- their principal joins.
solve :: [Ct] -> PmPluginM [Ct]
solve [] = return []
solve wantedCts = do
  -- Order in which we shall process the ambiguous type variables.
  topoOrder <- filter isAmbiguousType <$> topologicalTyConOrder wantedCts
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
      let outTys = (applySubst subst) <$> outTypes tv
      -- Check of there are exactly one or two outgoing types.
      if null outTys || length outTys > 2
        then
          throwPluginError "solve: There are either no or more then two outgoing types of a type variable."
        else do
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
topologicalTyConOrder :: [Ct] -> PmPluginM [Type]
topologicalTyConOrder wantedCts = orderNodes topoGraph
  where
    -- Involved type constructors
    constraintTys :: [(Ct, Type, Type, Type)]
    constraintTys = constraintPolymonadTyArgs' wantedCts

    nodes :: [LNode Type]
    nodes = zip [0..] -- with node ids added
          $ nubBy eqType -- without duplicates
          $ concatMap (\(_, t0, t1, t2) -> [t0, t1, t2]) constraintTys -- as a list

    nodeForTy :: Type -> Node
    nodeForTy ty = case find (\(_, ty') -> eqType ty ty') nodes of
      Just (n, _) -> n
      Nothing -> error "nodeForTy: Impossible, we should always find a node by construction."

    edges :: [LEdge ()]
    edges = filter (\(n, n', _) -> n /= n') $ removeDup
          $ concatMap (\(_, t0, t1, t2)
                -> [(nodeForTy t0, nodeForTy t2, ()), (nodeForTy t1, nodeForTy t2, ())]) constraintTys

    topoGraph :: Gr Type ()
    topoGraph = mkGraph nodes edges

    orderNodes :: Gr Type () -> PmPluginM [Type]
    orderNodes gr = if isEmpty gr
      then return []
      else case find (\(n, _) -> indeg gr n == 0) $ labNodes gr of
        Just (n, ty) -> do
          restTys <- orderNodes $ delNode n gr
          return $ ty : restTys
        Nothing -> throwPluginError "topologicalTyConOrder: No nodes with zero in-degree. There was a cycle!"
