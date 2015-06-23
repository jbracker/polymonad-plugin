
-- | Functions and utilities to work with and inspect class instances
--   of the GHC API. 
module Control.Polymonad.Plugin.Instance
  ( instanceTyCons
  , instanceTcVars
  , findInstanceTopTyCons
  , findMatchingInstances
  ) where

import Data.Set ( Set )
import qualified Data.Set as S

import InstEnv 
  ( ClsInst(..), ClsInstLookupResult
  , instanceHead
  , instanceSig
  , lookupInstEnv )
import Type 
  ( TyVar, TvSubst
  , substTys )
import TyCon ( TyCon )
import TcPluginM

import Control.Polymonad.Plugin.Utils 
  ( collectTopTyCons
  , collectTopTcVars
  , findConstraintOrInstanceTyCons
  , splitTyConApps )

-- | Retrieve the type constructors involved in the instance head of the 
--   given instance. This only selects the top level type constructors 
--   (See 'collectTopTyCons').
--   /Example:/
--   
--   > instance Polymonad Identity m Identity where
--   > > { Identity }
instanceTyCons :: ClsInst -> Set TyCon
instanceTyCons inst = 
  let (_tvs, _cls, args) = instanceHead inst 
  in collectTopTyCons args

-- | Retrieve the type constructor variables involved in the instance head of the 
--   given instance. This only selects the top level type variables (See 'collectTopTcVars').
--   /Example:/
--   
--   > instance Polymonad (m a b) n Identity where
--   > > { m , n }
instanceTcVars :: ClsInst -> Set TyVar
instanceTcVars inst = 
  let (_tvs, _cls, args) = instanceHead inst
  in collectTopTcVars args

-- | Search for all possible type constructors that could be 
--   used in the top-level position of the instance arguments.
--   Delivers a set of type constructors.
findInstanceTopTyCons :: ClsInst -> TcPluginM (Set TyCon)
findInstanceTopTyCons clsInst = do
  -- Top level type constructors of the instance arguments
  let instTcs = instanceTyCons clsInst
  -- Type constructor variables of the instance arguments
  let instTcvs = instanceTcVars clsInst
  -- Get the constraints of the given instance
  let (_vars, cts, _cls, _instArgs) = instanceSig clsInst
  -- For each constraint find the type constructors in its instances as 
  -- long as they are substitutes for the type constructor variables in
  -- this instance
  foundTcs <- mapM (findConstraintOrInstanceTyCons instTcvs) (splitTyConApps cts)
  -- Collect all results
  return $ instTcs `S.union` S.unions foundTcs

-- | Substitute some type variables in the head of the given instance and 
--   look if you can find instances that provide and implementation for the 
--   substituted type.
findMatchingInstances :: TvSubst -> ClsInst -> TcPluginM ClsInstLookupResult
findMatchingInstances subst clsInst = do
  instEnvs <- getInstEnvs
  let cls = is_cls clsInst
  let tys = substTys subst $ is_tys clsInst
  return $ lookupInstEnv instEnvs cls tys