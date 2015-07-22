
-- | Functions and utilities to work with and inspect class instances
--   of the GHC API.
module Control.Polymonad.Plugin.Instance
  ( instanceClassTyCon
  , instanceTyArgs
  , instanceTyCons
  , instanceTcVars
  , instanceType
  , instancePolymonadTyArgs
  ) where

import Data.Set ( Set )

import InstEnv
  ( ClsInst(..)
  , instanceSig )
import Type
  ( Type, TyVar )
import Class ( Class, classTyCon )
import TyCon ( TyCon )

import Control.Polymonad.Plugin.Log
  ( missingCaseError )
import Control.Polymonad.Plugin.Utils
  ( collectTopTyCons
  , collectTopTcVars )

-- | Returns the type constructors of the class is instance instantiates.
instanceClassTyCon :: ClsInst -> TyCon
instanceClassTyCon inst = classTyCon $ is_cls inst

-- | Returns the arguments of the given instance head.
instanceTyArgs :: ClsInst -> [Type]
instanceTyArgs inst = args
  where (_, _, _, args) = instanceType inst

-- | Returns the class, naming type constructor and arguments of this instance.
instanceType :: ClsInst -> ([Type], Class, TyCon, [Type])
instanceType inst = (cts, cls, instanceClassTyCon inst, args)
  where (_tvs, cts, cls, args) = instanceSig inst

-- | Check if the given instance is a 'Polymonad' instance and
--   if so return the arguments types of the instance head.
instancePolymonadTyArgs :: ClsInst -> (Type, Type, Type)
instancePolymonadTyArgs inst = case instArgs of
    [t0, t1, t2] -> (t0, t1, t2)
    x -> missingCaseError "instancePolymonadTyArgs" (Just x)
  where (_, _instCls, _, instArgs) = instanceType inst

-- | Retrieve the type constructors involved in the instance head of the
--   given instance. This only selects the top level type constructors
--   (See 'collectTopTyCons').
--   /Example:/
--
--   > instance Polymonad Identity m Identity where
--   > > { Identity }
instanceTyCons :: ClsInst -> Set TyCon
instanceTyCons inst = collectTopTyCons $ instanceTyArgs inst

-- | Retrieve the type constructor variables involved in the instance head of the
--   given instance. This only selects the top level type variables (See 'collectTopTcVars').
--   /Example:/
--
--   > instance Polymonad (m a b) n Identity where
--   > > { m , n }
instanceTcVars :: ClsInst -> Set TyVar
instanceTcVars inst = collectTopTcVars $ instanceTyArgs inst
