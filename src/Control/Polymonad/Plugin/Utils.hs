 
module Control.Polymonad.Plugin.Utils
  ( importedPolymonadModule
  , getPolymonadClass
  ) where

import Control.Monad ( filterM )

import TcRnTypes
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
  , instEnvElts )

polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

polymonadClassName :: String
polymonadClassName = "Polymonad"

importedPolymonadModule :: TcPluginM (Maybe Module)
importedPolymonadModule = do
  impMdls <- fmap (moduleEnvKeys . imp_mods . tcg_imports . fst) getEnvs
  foundMdls <- (flip filterM) impMdls $ \m -> do
    let pkgKey = modulePackageKey m
    let mdlName = moduleNameString $ moduleName m
    return $ pkgKey == mainPackageKey && mdlName == polymonadModuleName
  return $ case foundMdls of
    [m] -> Just m
    _ -> Nothing

getPolymonadClass :: Module -> TcPluginM (Maybe Class)
getPolymonadClass mdl = do
  visibleInsts <- fmap (instEnvElts . tcg_inst_env . fst) getEnvs
  foundInsts <- (flip filterM) visibleInsts $ \inst -> do
    let cls = is_cls inst
    let clsName = className cls
    let clsMdl = nameModule clsName
    let clsNameStr = occNameString $ getOccName clsName
    let clsArity = classArity cls
    return $ clsMdl == mdl 
          && clsNameStr == polymonadClassName
          && clsArity == 3
  return $ case foundInsts of
    (inst : _) -> Just $ is_cls inst
    [] -> Nothing