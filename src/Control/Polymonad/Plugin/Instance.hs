
-- | Functions and utilities to work with and inspect class instances
--   of the GHC API.
module Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars
  , instanceClassTyCon
  , instanceTyArgs
  , instanceTyCons
  , instanceTcVars
  , instanceType
  , instancePolymonadTyArgs
  ) where

import Data.Set ( Set )

import InstEnv
  ( ClsInst(..)
  , instanceSig
  , instanceBindFun )
import Type
  ( Type, TyVar
  , mkTyVarTy
  , substTy )
import Class ( Class, classTyCon )
import TyCon ( TyCon )
import Unify ( tcUnifyTys, tcMatchTys )
import VarSet ( mkVarSet )

import Control.Polymonad.Plugin.Log
  ( missingCaseError )
import Control.Polymonad.Plugin.Utils
  ( collectTopTyCons
  , collectTopTcVars )

-- | Trys to see if the given arguments match the class instance
--   arguments by unification. This only works if the number of arguments
--   given is equal to the arguments taken by the class the instance is of.
--   If the given arguments match the class arguments, a list with a type for
--   each free variable in the instance is returned. This list is in the same
--   order as the list of free variables that can be retrieved from the instance.
--   This function is meant for use in conjunction with 'isInstanceOf'.
matchInstanceTyVars :: [Type] -> ClsInst -> Maybe [Type]
matchInstanceTyVars instArgs inst = do
  let (instVars, _cts, _cls, tyArgs) = instanceSig inst
  let instVarSet = mkVarSet instVars
  subst <- tcMatchTys instVarSet tyArgs instArgs
  --subst <- tcUnifyTys instanceBindFun instArgs tyArgs
  return $ substTy subst . mkTyVarTy <$> instVars

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
