
-- | Core functions the plugin relies on to interact with GHCs API.
module Control.Polymonad.Plugin.Core
  ( getPolymonadInstancesInScope
  , getPolymonadTyConsInScope
  , findMatchingInstancesForConstraint
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
  ( constraintTyParams
  , constraintClassTyCon )
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

-- | TODO
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
  let ctTys = constraintTyParams ct
  guard $ classTyCon (is_cls inst) == constraintClassTyCon ct
  case tcUnifyTys instanceBindFun (is_tys inst) ctTys of
    Just subst -> do
      return (inst, subst)
    Nothing -> mzero