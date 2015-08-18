
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


import Type ( TyVar, Type, eqType, getTyVar_maybe, getTyVar )
import TcRnTypes ( Ct(..), CtLoc, CtEvidence(..) )

import Control.Polymonad.Plugin.Utils ( isAmbiguousType, removeDup )
import Control.Polymonad.Plugin.GraphView ( GraphView )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , printObj
  , getCurrentPolymonad
  , throwPluginError )
import Control.Polymonad.Plugin.Constraint ( constraintPolymonadTyArgs' )
import Control.Polymonad.Plugin.PrincipalJoin ( principalJoin )
import Control.Polymonad.Plugin.Constraint ( mkDerivedTypeEqCt' )

substToCts :: CtLoc -> [(TyVar, Type)] -> [Ct]
substToCts loc subst = fmap (uncurry $ mkDerivedTypeEqCt' loc) subst

-- Given the set of wanted constraints that shall be solved this produces
-- a set of derived constraints that link the ambiguous type variables to
-- their principal joins.
solve :: [Ct] -> PmPluginM [Ct]
solve [] = return []
solve wantedCts = do
  -- Order in which we shall process the ambiguous type variables.
  topoOrder <- filter isAmbiguousType <$> topologicalTyConOrder wantedCts
  subst <- calcSubst [] topoOrder
  return $ substToCts (ctev_loc . cc_ev . head $ wantedCts) subst
  where
    -- Involved type constructors
    constraintTys :: [(Ct, Type, Type, Type)]
    constraintTys = constraintPolymonadTyArgs' wantedCts

    inTypes :: Type -> [(Type, Type)]
    inTypes t = (\(_, t0, t1, _) -> (t0, t1)) <$>
      filter (\(_, _, _, t2) -> eqType t2 t) constraintTys

    outTypes :: Type -> [Type]
    outTypes t = nubBy eqType $ (\(_, _, _, t2) -> t2) <$>
      filter (\(_, t0, t1, _) -> eqType t0 t || eqType t1 t) constraintTys

    -- Applies the given substitution to a given type.
    -- Only substitutes if the given type is a type variables.
    -- Does not look inside of type constructors.
    applySubst :: [(TyVar, Type)] -> Type -> Type
    applySubst [] t = t
    applySubst ((tvSub, tSub):substs) t = case getTyVar_maybe t of
      Just tv -> if tv == tvSub then tSub else t
      Nothing -> t

    calcSubst :: [(TyVar, Type)] -> [Type] -> PmPluginM [(TyVar, Type)]
    calcSubst subst [] = return subst
    calcSubst subst (tv:tvs) = do
      -- Get the available polymonad instances.
      (_, _, pmInsts, givenCts) <- getCurrentPolymonad
      -- Get the outgoing types of the current type.
      let outTys = fmap (applySubst subst) $ outTypes tv
      -- Check of there are exactly one or two outgoing types.
      if null outTys || length outTys > 2
        then do
          throwPluginError "solve: There are either no or more then two outgoing types of a type variable."
        else do
          let inTys = fmap (\(t0, t1) -> (applySubst subst t0, applySubst subst t1)) $ inTypes tv
          -- Calculate the principal join. Be sure the
          -- already solved type variables are replaced with their solution
          -- before calculating the principal join.
          printObj pmInsts
          printObj givenCts
          printObj inTys
          printObj outTys
          mJoin <- principalJoin (pmInsts, givenCts) inTys outTys
          case mJoin of
            Just join -> do
              -- We found a principal join, proceed solving the other variables.
              restSubst <- calcSubst ((getTyVar "solve: Converting type to type variable failed." tv, join) : subst) tvs
              -- Returns the full subtitution.
              return $ (getTyVar "solve: Converting type to type variable failed." tv, join) : restSubst
              undefined
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
