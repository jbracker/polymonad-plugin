
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoin
  , principalJoinFor
  ) where

import Data.List ( nubBy )
import Data.Maybe ( isJust, catMaybes, listToMaybe )
import qualified Data.Set as S

import Control.Monad ( forM, guard, mzero, filterM )
import Control.Arrow ( (***) )

import Type
  ( Type, TvSubst, TyVar
  , mkTyConTy
  , eqTypes, eqType
  , getTyVar_maybe
  , substTy )
import InstEnv ( ClsInst(..), instanceBindFun )
import TcRnTypes ( Ct, isGivenCt )
import Unify ( tcUnifyTys )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , throwPluginError
  , getCurrentPolymonad
  , getIdentityTyCon
  , printObj )
import Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars
  , instanceType, instancePolymonadTyArgs )
import Control.Polymonad.Plugin.Core ( pickPolymonadInstance, isInstanceOf )
import Control.Polymonad.Plugin.Constraint
  ( constraintClassTyArgs, constraintPolymonadTyArgs', constraintPolymonadTyArgs )

principalJoinFor :: TyVar -> [(Type, Type)] -> [Type] -> PmPluginM (Maybe Type)
principalJoinFor ambTv f m = do
  idT <- mkTyConTy <$> getIdentityTyCon
  (pmTyCons, pmTyVars, pmInsts, pmGivenCts) <- getCurrentPolymonad
  let joinCands = pmTyVars ++ (mkTyConTy <$> S.toList pmTyCons)
  mSuitableJoinCands <- forM joinCands $ \joinCand -> do
    -- FIXME: Check join precondition
    let substF = nubBy (\(t0, t1) (t0', t1') -> eqType t0 t0' && eqType t1 t1')
               $ (substTopTyVar (ambTv, joinCand) *** substTopTyVar (ambTv, joinCand)) <$> f
    let substM = nubBy eqType
               $ substTopTyVar (ambTv, joinCand) <$> m
    fMatches <- fmap and $ forM substF
              $ \(t0, t1) -> hasMatch (t0, t1, joinCand) (pmInsts, pmGivenCts)
    mMatches <- fmap and $ forM substM
              $ \t2 -> hasMatch (joinCand, idT, t2) (pmInsts, pmGivenCts)
    return $ if fMatches && mMatches then Just joinCand else Nothing
  let suitableJoinCands = catMaybes mSuitableJoinCands
  case length suitableJoinCands of
    0 -> return Nothing
    1 -> return $ Just $ head suitableJoinCands
    _ -> do
      throwPluginError "principalJoinFor: Found more then one join. FIXME"

  where
    substTopTyVar :: (TyVar, Type) -> Type -> Type
    substTopTyVar (tv, ty) t = case getTyVar_maybe t of
      Just tv' -> if tv == tv' then ty else t
      Nothing -> t

    isPolymonadCtMatch :: (Type, Type, Type) -> Ct -> Bool
    isPolymonadCtMatch (t0, t1, t2) ct
      = maybe False (\(t0', t1', t2') -> eqType t0 t0' && eqType t1 t1' && eqType t2 t2')
      $ constraintPolymonadTyArgs ct

    hasMatch :: (Type, Type, Type) -> ([ClsInst], [Ct]) -> PmPluginM Bool
    hasMatch tys@(t0, t1, t2) (pmInsts, pmCts) = do
      instanceMatches <- forM pmInsts $ \pmInst -> do
        case matchInstanceTyVars [t0, t1, t2] pmInst of
          Just args -> args `isInstanceOf` pmInst
          Nothing -> return False
      let constraintMatches = any (isPolymonadCtMatch tys) pmCts
      return $ or instanceMatches || constraintMatches

-- | Calculate the principal join of a set of unary type constructors.
--   For this to work properly all of the given types need to be
--   type constructors or partially applied type constructors.
--   The principal join is defined in definition 4 of the
--   "Polymonad Programming" paper.
--
--   @principalJoin (insts, givenCts) f ms@ calculates the principal join,
--   by assuming the given @insts@ and @givenCts@ are available bind operations
--   in Sigma. @f@ is the set of unary type constructor pairs and @ms@ is
--   the set of type constructors we want to arrive at ({M_1, M_2} subsetof Sigma).
--
--   According to communication with the authors of the paper @f@ should
--   never be empty. The original definition requires exactly one or two
--   type constructors in @ms@. The type constructors in these sets may also
--   be variables that appear as type constructors in the given constraints,
--   but it is the responsibility of the user to ensure that they actually
--   represent type constructors.
principalJoin :: ([ClsInst], [Ct]) -> [(Type, Type)] -> [Type] -> PmPluginM (Maybe Type)
principalJoin (_, _) _ [] = throwPluginError "principalJoin: Missing outgoing types for join"
principalJoin (_, _) [] _ = throwPluginError "principalJoin: Missing incoming types for join"
principalJoin (insts, givenCts) f ms = if areGivenCts
  then do
    meetsPrecond <- checkPrincipalPrecondition
    if meetsPrecond
      then do
        joinCands <- findJoinCandidates
        joins <- filterM isPrincipalJoin joinCands
        return $ listToMaybe joins
      else throwPluginError "principalJoin: Principality precondition not met"
  else throwPluginError "principalJoin: Constraints are not given constraints"
  where
    -- Are all the constraints really given constraints.
    areGivenCts = all isGivenCt givenCts

    -- Check if the precondition for the existence of a principal join
    -- is met: For all (M, M') in 'f' and Mi in 'ms' there exists a (M, M')> Mi
    -- bind operation.
    checkPrincipalPrecondition :: PmPluginM Bool
    checkPrincipalPrecondition =
      fmap and $ forM f $ \(t0, t1) ->
        fmap and $ forM ms $ \t2 -> do
          isInstBind' <- isInstBind (t0, t1) t2
          return $ isInstBind' || isConstraintBind (t0, t1) t2

    -- Look for candidates that could be principal joins.
    findJoinCandidates :: PmPluginM [Type]
    findJoinCandidates = do
      -- Find candidates from instances
      possInstCand <- concat <$> forM f (possiblePolymonadInstBindResults insts)
      -- [(Type, [Type], ClsInst, TvSubst)]
      -- Find candidates from constraints
      let possCtCand = concat $ possiblePolymonadConstraintBindResults givenCts <$> f
      -- [(Type, Ct)]
      return $ fmap (\(x,_,_,_) -> x) possInstCand ++ fmap fst possCtCand

    -- Check if the given type is a principal join of f.
    isPrincipalJoin :: Type -> PmPluginM Bool
    isPrincipalJoin m = do
        hasOutMorphs <- and <$> forM ms (isMorphismBetween m)
        hasInMorphs  <- and <$> forM f (`isInstBind` m)
        return $ hasOutMorphs && hasInMorphs

    isMorphismBetween :: Type -> Type -> PmPluginM Bool
    isMorphismBetween t0 t2 = do
      idTC <- getIdentityTyCon
      isBind (t0, mkTyConTy idTC) t2

    isBind :: (Type, Type) -> Type -> PmPluginM Bool
    isBind (t0, t1) t2 = do
      isInstB <- isInstBind (t0, t1) t2
      return $ isInstB || isConstraintBind (t0, t1) t2

    isConstraintBind :: (Type, Type) -> Type -> Bool
    isConstraintBind (t0, t1) t2 = any (eqTypes [t0, t1, t2]) givenCtArgs
      where
        givenCtArgs :: [[Type]]
        givenCtArgs = catMaybes $ fmap constraintClassTyArgs givenCts


    isInstBind :: (Type, Type) -> Type -> PmPluginM Bool
    isInstBind (t0, t1) t2 = isJust <$> pickPolymonadInstance (t0, t1, t2)

-- | Looks at all the given instances and if they are polymonad instance
--   checks the given two types can be applied to the first two arguments.
--   Returns a list of the resulting thrid argument together with the
--   constraints this result would imply.
possiblePolymonadInstBindResults :: [ClsInst] -> (Type, Type)
                                 -> PmPluginM [(Type, [Type], ClsInst, TvSubst)]
possiblePolymonadInstBindResults insts (t0, t1) = fmap catMaybes $ forM insts $ \inst -> do
  let (m0, m1, m2) = instancePolymonadTyArgs inst
  case tcUnifyTys instanceBindFun [m0, m1] [t0, t1] of
    Just subst -> do
      let (instCts, _, _, _) = instanceType inst
      return $ Just (substTy subst m2, substTy subst <$> instCts, inst, subst)
    _ -> return Nothing

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
