
-- | Functions and utilities to detect the polymonad class and module.
module Control.Polymonad.Plugin.Detect
  ( -- * Polymonad
    getPolymonadModule
  , isPolymonadClass
  , getPolymonadClass
    -- * Identity
  , getIdentityModule
  ) where

import Control.Monad ( filterM )

import TcRnTypes
  ( imp_mods
  , tcg_imports, tcg_inst_env )
import TyCon ( TyCon )
import TcPluginM
import Name
  ( nameModule
  , getOccName )
import OccName ( occNameString )
import Module
  ( Module(..), PackageKey
  , mainPackageKey, basePackageKey
  , moduleEnvKeys
  , moduleNameString )
import Class
  ( Class(..)
  , className, classArity )
import InstEnv
  ( ClsInst(..)
  , instEnvElts )

polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

polymonadClassName :: String
polymonadClassName = "Polymonad"

identityModuleName :: String
identityModuleName = "Data.Functor.Identity"

identityTyConName :: String
identityTyConName = "Identity"

-- | Checks if the module with the given name is imported and,
--   if so, returns that module.
getModule :: PackageKey -> String -> TcPluginM (Maybe Module)
getModule pkgKeyToFind mdlNameToFind = do
  impMdls <- fmap (moduleEnvKeys . imp_mods . tcg_imports . fst) getEnvs
  foundMdls <- (flip filterM) impMdls $ \m -> do
    let pkgKey = modulePackageKey m
    let mdlName = moduleNameString $ moduleName m
    return $ pkgKey == pkgKeyToFind && mdlName == mdlNameToFind
  return $ case foundMdls of
    [m] -> Just m
    _ -> Nothing

-- | Checks if the module 'Control.Polymonad'
--   is imported and, if so, returns the module.
getPolymonadModule :: TcPluginM (Maybe Module)
getPolymonadModule = getModule mainPackageKey polymonadModuleName

-- | Checks if the module 'Data.Functor.Identity'
--   is imported and, if so, returns the module.
getIdentityModule :: TcPluginM (Maybe Module)
getIdentityModule = getModule basePackageKey identityModuleName

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

getIdentityTyCon :: TcPluginM (Maybe TyCon)
getIdentityTyCon = do
  mIdModule <- getIdentityModule
  case mIdModule of
    Just idModule -> do
      return undefined
    Nothing -> return Nothing
