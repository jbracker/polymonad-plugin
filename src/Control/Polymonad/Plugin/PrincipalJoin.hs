
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoin
  ) where

import Data.Maybe ( isJust, catMaybes, listToMaybe )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( forM, guard, mzero, filterM )

import Type
  ( Type, TvSubst
  , mkTyConTy
  , eqTypes
  , substTy )
import InstEnv ( ClsInst(..), instanceBindFun )
import TcRnTypes
  ( Ct, TcPluginM
  , isGivenCt )
import Unify ( tcUnifyTys )

import Control.Polymonad.Plugin.Utils ( collectTopTyCons )
import Control.Polymonad.Plugin.Instance
  ( instanceTyCons, instanceTyArgs, instanceType
  , instancePolymonadTyArgs )
import Control.Polymonad.Plugin.Core ( pickPolymonadInstance )
import Control.Polymonad.Plugin.Detect ( getIdentityTyCon )
import Control.Polymonad.Plugin.Constraint
  ( constraintClassTyArgs, constraintClassType
  , constraintPolymonadTyArgs )

-- | Calculate the principal join of a set of type constructors.
--   For this to work properly all of the given types need to be
--   type constructors or partially applied type constructors.
--   The principal join is defined in definition 4 of the
--   "Polymonad Programming" paper.
--   TODO: UNFINISHED
--   @principalJoin insts f ms@
--   insts - Available polymonad instances
--   f     - The set to calculate the join for
--   ms    - The target constructors.
principalJoin :: ([ClsInst], [Ct]) -> [(Type, Type)] -> [Type] -> TcPluginM (Maybe Type)
principalJoin (insts, givenCts) f ms = if areGivenCts
  then do
    meetsPrecond <- checkPrincipalPrecondition
    if meetsPrecond
      then do
        joinCands <- findJoinCandidates
        joins <- filterM isPrincipalJoin joinCands
        return $ listToMaybe joins
      else return Nothing
  else return Nothing
  where
    -- Are all the constraints really given constraints.
    areGivenCts = all isGivenCt givenCts

    -- Check if the precondition for the existence of a principal join
    -- is met: For all (M, M') in 'f' and Mi in 'ms' there exists a (M, M')> Mi
    -- bind operation.
    checkPrincipalPrecondition :: TcPluginM Bool
    checkPrincipalPrecondition =
      fmap and $ forM f $ \(t0, t1) ->
        fmap and $ forM ms $ \t2 -> do
          isInstBind' <- isInstBind (t0, t1) t2
          return $ isInstBind' || isConstraintBind (t0, t1) t2

    -- Look for candidates that could be principal joins.
    findJoinCandidates :: TcPluginM [Type]
    findJoinCandidates = do
      -- Find candidates from instances
      possInstCand <- concat <$> forM f (possiblePolymonadInstBindResults insts)
      -- [(Type, [Type], ClsInst, TvSubst)]
      -- Find candidates from constraints
      let possCtCand = concat $ possiblePolymonadConstraintBindResults givenCts <$> f
      -- [(Type, Ct)]
      return $ fmap (\(x,_,_,_) -> x) possInstCand ++ fmap fst possCtCand

    -- Check if the given type is a principal join of f.
    isPrincipalJoin :: Type -> TcPluginM Bool
    isPrincipalJoin m = do
        hasOutMorphs <- and <$> forM ms (isMorphismBetween m)
        hasInMorphs  <- and <$> forM f (`isInstBind` m)
        return $ hasOutMorphs && hasInMorphs

    isMorphismBetween :: Type -> Type -> TcPluginM Bool
    isMorphismBetween t0 t2 = do
      mIdTC <- getIdentityTyCon
      case mIdTC of
        Just idTC -> isBind (t0, mkTyConTy idTC) t2
        Nothing -> return False

    isBind :: (Type, Type) -> Type -> TcPluginM Bool
    isBind (t0, t1) t2 = do
      isInstB <- isInstBind (t0, t1) t2
      return $ isInstB || isConstraintBind (t0, t1) t2

    isConstraintBind :: (Type, Type) -> Type -> Bool
    isConstraintBind (t0, t1) t2 = any (eqTypes [t0, t1, t2]) givenCtArgs
      where
        givenCtArgs :: [[Type]]
        givenCtArgs = catMaybes $ fmap constraintClassTyArgs givenCts


    isInstBind :: (Type, Type) -> Type -> TcPluginM Bool
    isInstBind (t0, t1) t2 = isJust <$> pickPolymonadInstance (t0, t1, t2)

-- | Looks at all the given instances and if they are polymonad instance
--   checks the given two types can be applied to the first two arguments.
--   Returns a list of the resulting thrid argument together with the
--   constraints this result would imply.
possiblePolymonadInstBindResults :: [ClsInst] -> (Type, Type)
                                 -> TcPluginM [(Type, [Type], ClsInst, TvSubst)]
possiblePolymonadInstBindResults insts (t0, t1) = fmap catMaybes $ forM insts $ \inst ->
  case instancePolymonadTyArgs inst of
    Just (m0, m1, m2) -> case tcUnifyTys instanceBindFun [m0, m1] [t0, t1] of
      Just subst -> do
        let (instCts, _, _, _) = instanceType inst
        return $ Just (substTy subst m2, substTy subst <$> instCts, inst, subst)
      _ -> return Nothing
    Nothing -> return Nothing

-- | Looks at all the given (given) constraints and if they are polymonad constraints
--   checks the given two types match the first two arguments.
--   Returns a list of the resulting thrid argument together with the.
possiblePolymonadConstraintBindResults :: [Ct] -> (Type, Type)
                                       -> [(Type, Ct)]
possiblePolymonadConstraintBindResults cts (t0, t1) = do
  ct <- cts
  guard $ isGivenCt ct
  case constraintPolymonadTyArgs ct of
    Just (m0, m1, m2) -> if eqTypes [m0, m1] [t0, t1]
      then return (m2, ct)
      else mzero
    Nothing -> mzero


{-
case constraintClassType ct of
  Just (ctTyCon, ctTys) -> do
    guard $ classTyCon (is_cls inst) == ctTyCon
    case tcUnifyTys instanceBindFun (is_tys inst) ctTys of
      Just subst -> return (inst, subst)
      Nothing -> mzero
  Nothing -> mzero

-}
