
-- | Provides all kinds of functions that are needed by the plugin.
module Control.Polymonad.Plugin.Utils ( 
  -- * Plugin printing and debugging
    printppr
  , printM
  , pprToStr
  -- * Polymonad module and class recognition
  , getPolymonadModule
  , isPolymonadClass
  , getPolymonadClass
  , getPolymonadInstancesInScope
  , getAllPolymonadTypeConstructors
  -- * Constraint and type inspection
  , isClassConstraint
  , instanceTyCons
  , instanceTcVars
  , argumentTyCon
  , argumentTcVar
  , collectTyVars
  -- * General Utilities
  , atIndex
  ) where

import Data.Maybe ( listToMaybe, catMaybes )
import Data.Set ( Set )
import qualified Data.Set as S
import Control.Monad ( filterM )

import TcRnTypes
  ( Ct(..)
  , isCDictCan_Maybe
  , isWantedCt
  , imp_mods
  , tcg_imports, tcg_inst_env )
import TcPluginM
import Name 
  ( nameModule
  , getOccName )
import OccName ( occNameString )
import Module 
  ( Module(..)
  , mainPackageKey
  , moduleEnvKeys
  , moduleNameString )
import Class
  ( Class(..)
  , className, classArity )
import InstEnv 
  ( ClsInst(..)
  , instEnvElts
  , instanceHead
  , classInstances )
import Type 
  ( Type, TyVar
  , getTyVar_maybe
  , tyConAppTyCon_maybe
  , splitTyConApp_maybe
  , splitAppTys
  )
import TyCon ( TyCon )
import Outputable 
  ( Outputable( ppr )
  --, text, parens, (<>)
  , showSDocUnsafe )
  
-- -----------------------------------------------------------------------------
-- Plugin debug primitives
-- -----------------------------------------------------------------------------

-- | Print some generic outputable from the plugin (Unsafe).
printppr :: Outputable o => o -> TcPluginM ()
printppr = tcPluginIO . putStrLn . pprToStr

-- | Print a message from the plugin.
printM :: String -> TcPluginM ()
printM = tcPluginIO . putStrLn

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

-- -----------------------------------------------------------------------------
-- Polymonad module and class recognition
-- -----------------------------------------------------------------------------

polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

polymonadClassName :: String
polymonadClassName = "Polymonad"

-- | Checks of the module containing the 'Control.Polymonad' type class 
--   is imported and, if so, return the module.
getPolymonadModule :: TcPluginM (Maybe Module)
getPolymonadModule = do
  impMdls <- fmap (moduleEnvKeys . imp_mods . tcg_imports . fst) getEnvs
  foundMdls <- (flip filterM) impMdls $ \m -> do
    let pkgKey = modulePackageKey m
    let mdlName = moduleNameString $ moduleName m
    return $ pkgKey == mainPackageKey && mdlName == polymonadModuleName
  return $ case foundMdls of
    [m] -> Just m
    _ -> Nothing

-- | Checks if the given class matches the shape of the 'Control.Polymonad'
--   type class and is defined in the given module. Usually the given module 
--   should be the one delivered from 'getPolymonadModule'.
isPolymonadClass :: Module -> Class -> Bool
isPolymonadClass polymonadModule cls = 
  let clsName = className cls
      clsMdl = nameModule clsName
      clsNameStr = occNameString $ getOccName clsName
      clsArity = classArity cls
  in    clsMdl == polymonadModule 
     && clsNameStr == polymonadClassName
     && clsArity == 3

-- | Checks if a type class matching the shape and name of the 
--   'Control.Polymonad' type class is in scope and if it is part of the
--   polymonad module ('getPolymonadModule'). If so returns the class.
getPolymonadClass :: TcPluginM (Maybe Class)
getPolymonadClass = do
  mModule <- getPolymonadModule
  case mModule of
    Just polymonadModule -> do
      visibleInsts <- fmap (instEnvElts . tcg_inst_env . fst) getEnvs
      let foundInsts = (flip filter) visibleInsts $ isPolymonadClass polymonadModule . is_cls
      return $ case foundInsts of
        (inst : _) -> Just $ is_cls inst
        [] -> Nothing
    Nothing -> return Nothing

-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
getPolymonadInstancesInScope :: TcPluginM [ClsInst]
getPolymonadInstancesInScope = do
  mPolymonadClass <- getPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []

getAllPolymonadTypeConstructors :: TcPluginM (Set TyCon)
getAllPolymonadTypeConstructors = do
  pmInsts <- getPolymonadInstancesInScope
  return $ S.unions $ fmap instanceTyCons pmInsts

-- -----------------------------------------------------------------------------
-- Constraint and type inspection
-- -----------------------------------------------------------------------------

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct = 
  case isCDictCan_Maybe ct of
    Just cls -> cls == wantedClass && isWantedCt ct
    Nothing -> False

-- | Retrieve the type constructors involved in the instance head of the 
--   given instance. This only selects the top level type constructors.
--   If there are nested type constructors they are ignored.
--   /Example:/
--   
--   > instance Polymonad Identity m Identity where
--   > > { Identity }
instanceTyCons :: ClsInst -> Set TyCon
instanceTyCons inst = 
  let (_tvs, _cls, args) = instanceHead inst
      mTyCons = fmap tyConAppTyCon_maybe args
  in S.fromList $ catMaybes mTyCons

-- | Retrieve the type constructor variables involved in the instance head of the 
--   given instance. This only selects the top level type variables.
--   If there are nested type variables they are ignored. 
--   There is no actual check if the returned type variables are actually type
--   constructor variables.
--   /Example:/
--   
--   > instance Polymonad (m a b) n Identity where
--   > > { m , n }
instanceTcVars :: ClsInst -> Set TyVar
instanceTcVars inst = 
  let (_tvs, _cls, args) = instanceHead inst
      mTcVars = fmap (getTyVar_maybe . fst . splitAppTys) args
  in S.fromList $ catMaybes mTcVars

-- | @argumentTyCon n ct@ gets the type constructor of the n-th argument 
--   in the constraint (If an n-th argument exists and actually is a type 
--   constructor). Only works if the given constraint is a type class 
--   constraint.
argumentTyCon :: Int -> Ct -> Maybe TyCon
argumentTyCon n ct = do
  _ <- isCDictCan_Maybe ct
  let tyArgs = cc_tyargs ct
  tyArg <- tyArgs `atIndex` n
  tyConAppTyCon_maybe tyArg

-- | @argumentTyVar n ct@ gets the type variable of the n-th argument 
--   in the constraint (If an n-th argument exists and actually is a type 
--   variable). Only works if the given constraint is a type class 
--   constraint.
argumentTcVar :: Int -> Ct -> Maybe TyVar
argumentTcVar n ct = do
  _ <- isCDictCan_Maybe ct
  let tyArgs = cc_tyargs ct
  tyArg <- tyArgs `atIndex` n
  getTyVar_maybe tyArg

-- | Try to collect all type variables in a given expression.
--   Only works for nested type constructor applications and type variables.
--   If the given type is not supported an empty set is returned.
collectTyVars :: Type -> Set TyVar
collectTyVars t =
  case getTyVar_maybe t of
    Just tv -> S.singleton tv
    Nothing -> case splitTyConApp_maybe t of
      Just (_tc, args) -> S.unions $ fmap collectTyVars args
      Nothing -> S.empty

-- -----------------------------------------------------------------------------
-- General utilities
-- -----------------------------------------------------------------------------

-- | Get the element of a list at a given index (If that element exists).
atIndex :: [a] -> Int -> Maybe a
atIndex xs i = listToMaybe $ drop i xs

