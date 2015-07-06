
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( getPolymonadInstancesInScope
  , getPolymonadTyConsInScope
  , findMatchingInstancesForConstraint
  , selectPolymonadSubset
  ) where

import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( guard, MonadPlus(..) )

import InstEnv 
  ( ClsInst(..)
  , classInstances
  , instanceBindFun )
import TyCon ( TyCon )
import Type ( TvSubst, TyVar, lookupTyVar )
import Unify ( tcUnifyTys )
import Class ( Class(..) )
import TcRnTypes ( Ct(..) )
import TcPluginM

import Control.Polymonad.Plugin.Constraint
  ( constraintClassType, constraintTyCons )
import Control.Polymonad.Plugin.Instance
  ( findInstanceTopTyCons, instanceTyCons, instanceClassTyCon, instanceTyArgs, instanceTcVars )
import Control.Polymonad.Plugin.Detect
  ( getPolymonadClass )
import Control.Polymonad.Plugin.Utils
  ( findConstraintOrInstanceTyCons )

-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
getPolymonadInstancesInScope :: TcPluginM [ClsInst]
getPolymonadInstancesInScope = do
  mPolymonadClass <- getPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []

-- | Returns the set of all type constructors in the current scope 
--   that are part of a polymonad in Haskell. Uses the polymonad
--   instances to search for type constructors.
getPolymonadTyConsInScope :: TcPluginM (Set TyCon)
getPolymonadTyConsInScope = do
  pmInsts <- getPolymonadInstancesInScope
  fmap S.unions $ mapM findInstanceTopTyCons pmInsts

-- | Find all instances that could possible be applied for a given constraint.
--   Returns the applicable instance together with the necessary substitution
--   for unification.
findMatchingInstancesForConstraint :: [ClsInst] -> Ct -> [(ClsInst, TvSubst)]
findMatchingInstancesForConstraint insts ct = do
  inst <- insts
  case constraintClassType ct of
    Just (ctTyCon, ctTys) -> do
      guard $ classTyCon (is_cls inst) == ctTyCon
      case tcUnifyTys instanceBindFun (is_tys inst) ctTys of
        Just subst -> do
          return (inst, subst)
        Nothing -> mzero
    Nothing -> mzero

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
selectPolymonadSubset :: [Ct] -> TcPluginM (Set TyCon, [ClsInst])
selectPolymonadSubset cts = do
  -- TODO
  return $ undefined
  where
    c :: Int -> TcPluginM (Set TyCon , [ClsInst])
    c 0 = do
      let initialTcs = S.unions $ fmap constraintTyCons cts
      return (initialTcs, []) 
    c n = do
      (initialTcs, _initialClsInsts) <- c (n - 1)
      
      return (initialTcs `S.union` undefined, undefined)
      
    appTC :: Set TyCon -> ClsInst -> TyVar -> TcPluginM (Set TyCon, [ClsInst])
    appTC tcsCn clsInst tcVarArg = do
      case instanceTyCons clsInst `S.isSubsetOf` tcsCn of
        True  -> do
          let tcVarArgs = S.delete tcVarArg $ instanceTcVars clsInst
          -- TODO
          -- Substitute tycons (already collected ones) for the given argument
          -- Substitute all possible tycons for the rest of the arguments
          -- Find applicable instances and return the together with all of the substituted tycons
          return (undefined, undefined)
        False -> return (S.empty, [])


-- | Substitute some type variables in the head of the given instance and 
--   look if you can find instances that provide an implementation for the 
--   substituted instance. Also checks if the found instances actually
--   support evidence.
findApplicableInstances :: TvSubst -> ClsInst -> TcPluginM [(ClsInst, TvSubst)]
findApplicableInstances subst clsInst = do
  let substTcVars = S.filter (isJust . lookupTyVar subst) $ instanceTcVars clsInst
  applicableTyCons <- findConstraintOrInstanceTyCons substTcVars (instanceClassTyCon clsInst, instanceTyArgs clsInst)
  --associations 
  -- TODO
  return $ undefined

