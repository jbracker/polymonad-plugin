
module Control.Polymonad.Plugin.Evaluate
  ( evaluateTypeEqualities
  ) where

import Data.Maybe ( catMaybes )
import Data.List ( find )

import Type
  ( Type, TyVar
  , getEqPredTys_maybe, splitAppTy_maybe, splitFunTy_maybe
  , isTyVarTy, getTyVar_maybe
  , mkFamilyTyConApp, mkAppTy, mkFunTy )
import TcRnTypes
  ( Ct(..), CtEvidence(..) )

-- | Try to apply the type equality constraints given in the pair of arguments
--   to the given type. This will ignore non type equalities in the first
--   argument.
--
--   This is not a full-blown evaluator it just supports type equalities that
--   relate a type variable to a type and tries to apply them until the given type
--   does not change anymore. Other kinds of equalities are going to be ignored.
--
--   There is no check for contradictory type equalities.
--   This may run into an infinite loop of expansions if the equalities form
--   a loop.
evaluateTypeEqualities :: ([Ct], [Type]) -> Type -> Type
evaluateTypeEqualities (cts, ts) = evalTypeEqs
  where
    evalTypeEqs :: Type -> Type
    evalTypeEqs t =
      case getTyVar_maybe t of
        Just tv -> case find (\(tv', _) -> tv' == tv) tyEqs of
          Just (_, repTy) ->
            let evalTy = evalTypeEqs repTy
            in if evalTy == repTy then evalTy else evalTypeEqs evalTy
          Nothing -> t
        Nothing -> case splitAppTy_maybe t of
          Just (tFun, tArg) -> mkAppTy (evalTypeEqs tFun) (evalTypeEqs tArg)
          Nothing -> case splitFunTy_maybe t of
            Just (tArg, tRes) -> mkFunTy (evalTypeEqs tArg) (evalTypeEqs tRes)
            Nothing -> t

    -- Only keep those type equalities that associate a type variable with another type.
    tyEqs =  catMaybes (fmap makeTyEqPairFromCt cts)
          ++ catMaybes (fmap makeTyEqPairFromType ts)

    makeTyEqPairFromType :: Type -> Maybe (TyVar, Type)
    makeTyEqPairFromType t = do
      (_, ta, tb) <- getEqPredTys_maybe t
      case (isTyVarTy ta, isTyVarTy tb) of
        (True, _) -> do
          tva <- getTyVar_maybe ta
          return (tva, tb)
        (_, True) -> do
          tvb <- getTyVar_maybe tb
          return (tvb, ta)
        _ -> Nothing

    makeTyEqPairFromCt :: Ct -> Maybe (TyVar, Type)
    makeTyEqPairFromCt ct@(CTyEqCan {}) = Just (cc_tyvar ct, cc_rhs ct)
                                           -- FIXME: It may be necessary that
                                           -- this actually evaluates type functions properly.
    makeTyEqPairFromCt ct@(CFunEqCan {}) = Just (cc_fsk ct, mkFamilyTyConApp (cc_fun ct) (cc_tyargs ct))
    makeTyEqPairFromCt ct@(CNonCanonical {}) = makeTyEqPairFromType $ ctev_pred $ cc_ev ct
    makeTyEqPairFromCt _ = Nothing
