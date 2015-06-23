
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( getPolymonadInstancesInScope
  , getPolymonadTyConsInScope
  , findMatchingInstancesForConstraint
  , selectPolymonadSubset
  ) where

import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( guard, MonadPlus(..) )

import InstEnv 
  ( ClsInst(..)
  , classInstances
  , instanceBindFun )
import TyCon ( TyCon )
import Type ( TvSubst )
import Unify ( tcUnifyTys )
import Class ( Class(..) )
import TcRnTypes ( Ct(..) )
import TcPluginM

import Control.Polymonad.Plugin.Constraint
  ( constraintClassType )
import Control.Polymonad.Plugin.Instance
  ( findInstanceTopTyCons )
import Control.Polymonad.Plugin.Detect
  ( getPolymonadClass )

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
    c_0 :: Set TyCon
    c_0 = undefined



