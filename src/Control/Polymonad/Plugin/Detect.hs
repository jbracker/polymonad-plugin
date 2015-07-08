
-- | Functions and utilities to detect the importent modules, classes
--   and types of the plugin.
module Control.Polymonad.Plugin.Detect
  ( -- * Polymonad Class Detection
    getPolymonadModule
  , isPolymonadClass
  , getPolymonadClass
    -- * Identity Type Detection
  , getIdentityModule
  , getIdentityTyCon
  ) where

import Data.Maybe ( catMaybes, listToMaybe )

import Control.Monad ( filterM, forM, liftM )

import TcRnTypes
  ( imp_mods
  , TcGblEnv(..)
  , TcTyThing(..) )
import Type
  ( TyThing(..) )
import TyCon ( TyCon )
import TcPluginM
import Name
  ( nameModule
  , getOccName )
import OccName
  ( OccName
  , occNameString, mkTcOcc )
import RdrName
  ( GlobalRdrElt(..)
  , Parent( NoParent ), Provenance(..)
  , importSpecModule
  , lookupGlobalRdrEnv )
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

-- -----------------------------------------------------------------------------
-- Constant Names (Magic Numbers...)
-- -----------------------------------------------------------------------------

polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

polymonadClassName :: String
polymonadClassName = "Polymonad"

identityModuleName :: String
identityModuleName = "Data.Functor.Identity"

identityTyConName :: String
identityTyConName = "Identity"

-- -----------------------------------------------------------------------------
-- Polymonad Class Detection
-- -----------------------------------------------------------------------------

-- | Checks if the module 'Control.Polymonad'
--   is imported and, if so, returns the module.
getPolymonadModule :: TcPluginM (Maybe Module)
getPolymonadModule = getModule mainPackageKey polymonadModuleName

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
      let foundInsts = flip filter visibleInsts $ isPolymonadClass polymonadModule . is_cls
      return $ case foundInsts of
        (inst : _) -> Just $ is_cls inst
        [] -> Nothing
    Nothing -> return Nothing

-- -----------------------------------------------------------------------------
-- Identity Type Detection
-- -----------------------------------------------------------------------------

-- | Checks if the module 'Data.Functor.Identity'
--   is imported and, if so, returns the module.
getIdentityModule :: TcPluginM (Maybe Module)
getIdentityModule = getModule basePackageKey identityModuleName

getIdentityTyCon :: TcPluginM (Maybe TyCon)
getIdentityTyCon = do
  mIdModule <- getIdentityModule
  case mIdModule of
    Just idMdl -> findTyConByNameAndModule (mkTcOcc identityTyConName) idMdl
    Nothing -> return Nothing

-- -----------------------------------------------------------------------------
-- Local Utility Functions
-- -----------------------------------------------------------------------------

-- | Checks if the module with the given name is imported and,
--   if so, returns that module.
getModule :: PackageKey -> String -> TcPluginM (Maybe Module)
getModule pkgKeyToFind mdlNameToFind = do
  impMdls <- fmap (moduleEnvKeys . imp_mods . tcg_imports . fst) getEnvs
  foundMdls <- flip filterM impMdls $ \m -> do
    let pkgKey = modulePackageKey m
    let mdlName = moduleNameString $ moduleName m
    return $ pkgKey == pkgKeyToFind && mdlName == mdlNameToFind
  return $ case foundMdls of
    [m] -> Just m
    _ -> Nothing

-- | Try to find a type constructor given its name and the module it
--   was originally exported from.
findTyConByNameAndModule :: OccName -> Module -> TcPluginM (Maybe TyCon)
findTyConByNameAndModule occName mdl = do
  -- Look at the global environment of names that are in scope.
  rdrEnv <- tcg_rdr_env . fst <$> getEnvs
  -- Search for things that have the same name as what we are looking for.
  let envResultElem = lookupGlobalRdrEnv rdrEnv occName
  -- Only keep things that are originally from our module and have no parents,
  -- because type constructors are declared on top-level.
  let relResults = filter
        (\e -> (e `isOriginallyImportedFrom` mdl) && hasNoParent e)
        envResultElem
  -- Find all the typed things that have the same name as the stuff we found.
  -- Also directly convert them into type constructors if possible
  mTyCons <- forM relResults $ liftM tcTyThingToTyCon . tcLookup . gre_name
  -- Only keep those things that actually were type constructors.
  let tyCons = catMaybes mTyCons
  -- In theory, we should not find more then one type constructor,
  -- because that would lead to a name clash in the source module
  -- and we made sure to only look at one module.
  return $ listToMaybe tyCons

-- | Try to convert the given typed thing into a type constructor.
tcTyThingToTyCon :: TcTyThing -> Maybe TyCon
tcTyThingToTyCon (AGlobal (ATyCon tc)) = Just tc
tcTyThingToTyCon _ = Nothing

-- | Check if the given element has no parents.
hasNoParent :: GlobalRdrElt -> Bool
hasNoParent rdrElt = case gre_par rdrElt of
  NoParent -> True
  _ -> False

-- | Check if the given element has its origin in the given module.
isOriginallyImportedFrom :: GlobalRdrElt -> Module -> Bool
isOriginallyImportedFrom rdrElt mdl = case gre_prov rdrElt of
  LocalDef -> False
  Imported [] -> False -- Just for safety
  Imported impSpecs -> moduleName mdl == importSpecModule (last impSpecs)
