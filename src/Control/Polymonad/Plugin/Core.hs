
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( getPolymonadTyConsInScope
  , pickInstanceForAppliedConstraint
  , pickPolymonadInstance
  , selectPolymonadSubset
  ) where

import Data.Maybe ( isJust, isNothing, fromJust, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( guard, forM, unless, MonadPlus(..) )

import InstEnv
  ( ClsInst(..), InstEnvs
  , classInstances
  , instanceBindFun, instanceSig
  , lookupInstEnv
  , lookupUniqueInstEnv )
import TyCon ( TyCon )
import Type
  ( Type, TvSubst, TyVar
  , lookupTyVar, getClassPredTys_maybe
  , mkTopTvSubst, substTys )
import Unify ( tcUnifyTys )
import Class ( Class(..) )
import TcRnTypes ( Ct(..) )
import TcEvidence ( EvTerm(..) )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, getPolymonadClass, getPolymonadInstances, getInstEnvs )
import Control.Polymonad.Plugin.Constraint
  ( constraintClassType, constraintClassTyArgs
  , constraintTyCons
  , isClassConstraint, isFullyAppliedClassConstraint )
import Control.Polymonad.Plugin.Instance
  ( findInstanceTopTyCons, instanceTyCons, instanceClassTyCon, instanceTyArgs, instanceTcVars )
import Control.Polymonad.Plugin.Detect
  ( findPolymonadClass )
import Control.Polymonad.Plugin.Utils
  ( findConstraintOrInstanceTyCons, isGroundUnaryTyCon )

-- | Returns the set of all type constructors in the current scope
--   that are part of a polymonad in Haskell. Uses the polymonad
--   instances to search for type constructors.
getPolymonadTyConsInScope :: PmPluginM (Set TyCon)
getPolymonadTyConsInScope = do
  pmInsts <- getPolymonadInstances
  S.unions <$> mapM findInstanceTopTyCons pmInsts

-- | Find all instances that could possible be applied for a given constraint.
--   Returns the applicable instance together with the necessary substitution
--   for unification.
--   TODO: Is this function useful?
findMatchingInstancesForConstraint :: [ClsInst] -> Ct -> [(ClsInst, TvSubst)]
findMatchingInstancesForConstraint insts ct = do
  inst <- insts
  case constraintClassType ct of
    Just (ctTyCon, ctTys) -> do
      guard $ classTyCon (is_cls inst) == ctTyCon
      case tcUnifyTys instanceBindFun (is_tys inst) ctTys of
        Just subst -> return (inst, subst)
        Nothing -> mzero
    Nothing -> mzero



-- | Given a fully applied polymonad constraint it will pick the first instance
--   that matches it. This is ok to do, because for polymonads it does
--   not make a difference which bind-operation we pick if the type is equal.
pickInstanceForAppliedConstraint :: Ct -> PmPluginM (Maybe (EvTerm, Ct))
pickInstanceForAppliedConstraint ct = do
  -- Get the polymonad class constructor.
  pmCls <- getPolymonadClass
  case constraintClassTyArgs ct of
    -- We found the polymonad class constructor and the given constraint
    -- is a instance constraint.
    Just tyArgs
        -- Be sure to only proceed if the constraint is a polymonad constraint
        -- and is fully applied to concrete types.
        |  isClassConstraint pmCls ct
        && isFullyAppliedClassConstraint ct -> do
      -- Get the instance environment
      instEnvs <- getInstEnvs
      -- Find matching instance for our constraint.
      case lookupInstEnv instEnvs pmCls tyArgs of
        (matches, _, _) ->
          -- Only keep those matches that actually found a type for every argument.
          case filter (\(_, args) -> all isJust args) matches of
            -- If we found more then one instance, just use the first.
            -- Because we are talking about polymonad we can freely choose.
            (foundInst, foundInstArgs) : _ -> do
              -- Try to produce evidence for the instance we want to use.
              evTerm <- produceEvidenceFor foundInst (fromJust <$> foundInstArgs)
              return $ (\ev -> (ev, ct)) <$> evTerm
            _ -> return Nothing
        _ -> return Nothing
    _ -> return Nothing
  where
    -- | Apply the given instance dictionary to the given type arguments
    --   and try to produce evidence for the application.
    produceEvidenceFor :: ClsInst -> [Type] -> PmPluginM (Maybe EvTerm)
    produceEvidenceFor inst tys = do
      -- Get the instance type variables and constraints (by that we know the
      -- number of type arguments and dictionart arguments for the EvDFunApp)
      let (tyVars, cts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
      -- How the instance variables for the current instance are bound.
      let varSubst = mkTopTvSubst $ zip tyVars tys
      -- Global instance environment.
      instEnvs <- getInstEnvs
      -- Split the constraints into their class and arguments.
      -- We ignore constraints where this is not possible.
      -- Don't know if this is the right thing to do.
      let instCts = catMaybes $ fmap getClassPredTys_maybe cts
      -- Now go over each constraint and find a suitable instance and evidence.
      ctEvTerms <- forM instCts $ \(ctCls, ctArgs) -> do
        -- Substitute the variables to know what instance we are looking for.
        let substArgs = substTys varSubst ctArgs
        -- Look for suitable instance. Since we are not necessarily working
        -- with polymonads anymore we need to find a unique one.
        case lookupUniqueInstEnv instEnvs ctCls substArgs of
          -- No instance found, too bad...
          Left _err -> return Nothing
          -- We found one: Now we can produce evidence for the found instance.
          Right (clsInst, instArgs) -> produceEvidenceFor clsInst instArgs
      -- If we found a good instance and evidence for every constraint,
      -- we can create the evidence for this instance.
      return $ if any isNothing ctEvTerms
        then Nothing
        else Just $ EvDFunApp (is_dfun inst) tys (fromJust <$> ctEvTerms)



-- | Given a three ground unary type constructors it will pick the first
--   polymonad instance that matches these arguments. This is ok to do,
--   because for polymonads it does not make a difference which
--   bind-operation we pick if the type is equal.
pickPolymonadInstance :: (Type, Type, Type) -> PmPluginM (Maybe ClsInst)
pickPolymonadInstance (t0, t1, t2) = do
  let args = [t0, t1, t2]
  pmCls <- getPolymonadClass
  -- Get the current instance environment
  instEnvs <- getInstEnvs
  -- Make sure that all of the given arguments are ground unary type constructors
  if all isGroundUnaryTyCon args
    -- Find matching instance for our arguments.
    then case lookupInstEnv instEnvs pmCls args of
        (matches, _, _) ->
          -- Only keep those matches that actually found a type for every argument.
          case filter (all isJust . snd) matches of
            -- If we found more then one instance, just use the first.
            -- Because we are talking about polymonads we can freely choose.
            (foundInst, foundInstArgs) : _ -> do
              -- Check if the constraints of the instance hold for the given arguments.
              instCheck <- checkInstance foundInst (fromJust <$> foundInstArgs)
              return $ if instCheck then Just foundInst else Nothing
            _ -> return Nothing
        _ -> return Nothing
    else return Nothing

  where
    -- | Apply the given instance dictionary to the given type arguments
    --   and check if it meets is constraints.
    checkInstance :: ClsInst -> [Type] -> PmPluginM Bool
    checkInstance inst tys = do
      -- Get the instance type variables and constraints (by that we know
      -- the numner of type arguments)
      let (tyVars, cts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
      -- How the instance variables for the current instance are bound.
      let varSubst = mkTopTvSubst $ zip tyVars tys
      -- Split the constraints into their class and arguments.
      -- We ignore constraints where this is not possible.
      -- Don't know if this is the right thing to do.
      let instCts = catMaybes $ fmap getClassPredTys_maybe cts
      -- Now go over each constraint and find a suitable instance.
      fmap and $ forM instCts $ \(ctCls, ctArgs) -> do
        -- Substitute the variables to know what instance we are looking for.
        let substArgs = substTys varSubst ctArgs
        -- Get the current instance environment
        instEnvs <- getInstEnvs
        -- Look for suitable instance. Since we are not necessarily working
        -- with polymonads anymore we need to find a unique one.
        case lookupUniqueInstEnv instEnvs ctCls substArgs of
          -- No instance found, too bad...
          Left _err -> return False
          -- We found one: Now we also need to check the found instance for
          -- its preconditions.
          Right (clsInst, instArgs) -> checkInstance clsInst instArgs



-- | Subset selection algorithm to select the correct subset of
--   type constructor and bind instances that belong to the polymonad
--   being worked with in the list of constraints.
--
--   /Preconditions:/ For the algorithm to work correctly,
--   certain preconditions have to be meet:
--
--     * TODO
--
--   __TODO: Work in Progress / Unfinished__
selectPolymonadSubset :: [Ct] -> PmPluginM (Set TyCon, [ClsInst])
selectPolymonadSubset cts =
  -- TODO
  return undefined
  where
    c :: Int -> PmPluginM (Set TyCon , [ClsInst])
    c 0 = do
      let initialTcs = S.unions $ fmap constraintTyCons cts
      return (initialTcs, [])
    c n = do
      (initialTcs, _initialClsInsts) <- c (n - 1)

      return (initialTcs `S.union` undefined, undefined)

    appTC :: Set TyCon -> ClsInst -> TyVar -> PmPluginM (Set TyCon, [ClsInst])
    appTC tcsCn clsInst tcVarArg =
      if instanceTyCons clsInst `S.isSubsetOf` tcsCn
        then do
          let tcVarArgs = S.delete tcVarArg $ instanceTcVars clsInst
          -- TODO
          -- Substitute tycons (already collected ones) for the given argument
          -- Substitute all possible tycons for the rest of the arguments
          -- Find applicable instances and return the together with all of the substituted tycons
          return (undefined, undefined)
        else return (S.empty, [])
