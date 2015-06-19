 
module Control.Polymonad.Plugin.Utils
  -- Plugin printing and debugging
  ( printppr
  , printM
  , pprToStr
  -- Polymonad module and class recognition
  , getPolymonadModule
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
import Outputable 
  ( Outputable( ppr )
  --, text, parens, (<>)
  , showSDocUnsafe )
  
-- -----------------------------------------------------------------------------
-- Plugin debug primitives
-- -----------------------------------------------------------------------------
  
printppr :: Outputable o => o -> TcPluginM ()
printppr = tcPluginIO . putStrLn . pprToStr

printM :: String -> TcPluginM ()
printM = tcPluginIO . putStrLn

pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

-- -----------------------------------------------------------------------------
-- Polymonad module and class recognition
-- -----------------------------------------------------------------------------

polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

polymonadClassName :: String
polymonadClassName = "Polymonad"

-- | Checks of the module containing the 'Polymonad' type class 
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

-- | Checks if a type class matching the shape and name of the 
--   'Polymonad' type class is in scope and if it is part of the
--   polymonad module ('getPolymonadModule'). If so returns the class.
getPolymonadClass :: TcPluginM (Maybe Class)
getPolymonadClass = do
  mModule <- getPolymonadModule
  case mModule of
    Just mdl -> do
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
    Nothing -> return Nothing


