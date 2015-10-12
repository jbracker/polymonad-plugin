
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
import Name ( NamedThing( getName, getOccName ) )
import Unique ( Uniquable( getUnique ) )
import Var ( varType, varUnique, varName )

import Control.Polymonad.Plugin.Utils ( isAmbiguousType, removeDup )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , assert
  , throwPluginError
  , printObj, printMsg )
import Control.Polymonad.Plugin.PrincipalJoin ( principalJoinFor )
import Control.Polymonad.Plugin.Constraint ( mkDerivedTypeEqCt', constraintPolymonadTyArgs' )
import Control.Polymonad.Plugin.Topological ( topologicalTyConOrder )


substToCts :: CtLoc -> [(TyVar, Type)] -> [Ct]
substToCts loc = fmap (uncurry $ mkDerivedTypeEqCt' loc)

showVar :: TyVar -> PmPluginM ()
showVar tv = do
  printObj tv
  printObj (varName tv)
  printObj (varUnique tv)
  printObj (varType tv)

-- | Given the set of wanted constraints that shall be solved this produces
--   a set of derived constraints that link the ambiguous type variables to
--   their principal joins.
solve :: [Ct] -> PmPluginM [Ct]
solve [] = return []
solve wantedCts = do
  printMsg "SOLVE FOR:"
  printObj wantedCts
  -- Order in which we shall process the ambiguous type variables.
  topoOrder <- filter isAmbiguousType <$> topologicalTyConOrder wantedCts
  --printObj =<< topologicalTyConOrder wantedCts
  --printObj topoOrder
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
      let outTys -- Make sure that if there is another ambiguous type variable
                 -- among the outgoing types to remove it. This is important,
                 -- because that other ambigous type variable will never match
                 -- any instances. FIXME: This is a hack. I do not know if this is the right thing to do.
                 = filter (\t -> not (isAmbiguousType t && not (eqType t $ mkTyVarTy tv)))
                   -- Get the outgoing types of the current type.
                 $ applySubst subst <$> outTypes tv
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
