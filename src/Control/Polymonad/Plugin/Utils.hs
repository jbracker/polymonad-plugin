 
module Control.Polymonad.Plugin.Utils
  -- Plugin printing and debugging
  ( printppr
  , printM
  , pprToStr
  -- Polymonad module and class recognition
  , getPolymonadModule
  , isPolymonadClass
  , getPolymonadClass
  , getPolymonadInstancesInScope
  , isClassConstraint
  ) where

import Control.Monad ( filterM )

import TcRnTypes
  ( Ct
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
  , classInstances )
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

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct = 
  case isCDictCan_Maybe ct of
    Just cls -> cls == wantedClass && isWantedCt ct
    Nothing -> False






