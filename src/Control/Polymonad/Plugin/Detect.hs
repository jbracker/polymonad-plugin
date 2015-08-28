
-- | Functions and utilities to detect the importent modules, classes
--   and types of the plugin.
module Control.Polymonad.Plugin.Detect
  ( -- * Polymonad Class Detection
    polymonadModuleName
  , polymonadClassName
  , findPolymonadModule
  , isPolymonadClass
  , isPolymonadModule
  , findPolymonadClass
    -- * Identity Type Detection
  , identityModuleName
  , identityTyConName
  , findIdentityModule
  , findIdentityTyCon
    -- * Other Utilities
  , findPolymonadInstancesInScope
  , selectPolymonadSubset
  ) where

import Data.Maybe ( catMaybes, listToMaybe )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( forM, liftM )

import TcRnTypes
  ( Ct
  , isGivenCt, isWantedCt, isDerivedCt
  , TcGblEnv(..)
  , TcTyThing(..) )
import Type
  ( Type, TyThing(..), TyVar
  , isTyVarTy, splitAppTys
  , splitFunTysN
  , mkTyConApp, mkTyVarTy, mkTyConTy )
import TyCon ( TyCon, tyConArity, tyConKind )
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
  , basePackageKey
  , mkModuleName )
import Class
  ( Class(..)
  , className, classArity )
import Unify ( tcUnifyTys )
import InstEnv
  ( ClsInst(..)
  , instEnvElts
  , instanceSig
  , instanceBindFun
  , classInstances )
import Outputable ( Outputable )

import Control.Polymonad.Plugin.Log ( pmDebugMsg, pmObjMsg, pmErrMsg, pprToStr )
import Control.Polymonad.Plugin.Utils ( associations )
import Control.Polymonad.Plugin.Instance ( instanceTcVars, instanceTyCons )
import Control.Polymonad.Plugin.Constraint
  ( constraintTyCons, constraintClassTyArgs, isClassConstraint )

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
findPolymonadModule :: TcPluginM (Either String Module)
findPolymonadModule = getModule Nothing {- mainPackageKey -} polymonadModuleName

-- | Check if the given module is the polymonad module.
isPolymonadModule :: Module -> Bool
isPolymonadModule = (mkModuleName polymonadModuleName ==) . moduleName

-- | Checks if the given class matches the shape of the 'Control.Polymonad'
--   type class and is defined in the given module. Usually the given module
--   should be the one delivered from 'getPolymonadModule'.
isPolymonadClass :: Class -> Bool
isPolymonadClass cls =
  let clsName = className cls
      clsMdl = nameModule clsName
      clsNameStr = occNameString $ getOccName clsName
      clsArity = classArity cls
  in    isPolymonadModule clsMdl
     && clsNameStr == polymonadClassName
     && clsArity == 3

-- | Checks if a type class matching the shape and name of the
--   'Control.Polymonad' type class is in scope and if it is part of the
--   polymonad module ('getPolymonadModule'). If so returns the class.
findPolymonadClass :: TcPluginM (Maybe Class)
findPolymonadClass = do
  visibleInsts <- fmap (instEnvElts . tcg_inst_env . fst) getEnvs
  let foundInsts = flip filter visibleInsts $ isPolymonadClass . is_cls
  return $ case foundInsts of
    (inst : _) -> Just $ is_cls inst
    [] -> Nothing

-- -----------------------------------------------------------------------------
-- Identity Type Detection
-- -----------------------------------------------------------------------------

-- | Checks if the module 'Data.Functor.Identity'
--   is imported and, if so, returns the module.
findIdentityModule :: TcPluginM (Either String Module)
findIdentityModule = getModule (Just basePackageKey) identityModuleName

findIdentityTyCon :: TcPluginM (Maybe TyCon)
findIdentityTyCon = do
  mIdModule <- findIdentityModule
  case mIdModule of
    Right idMdl -> findTyConByNameAndModule (mkTcOcc identityTyConName) idMdl
    Left _err -> return Nothing

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
findPolymonadInstancesInScope :: TcPluginM [ClsInst]
findPolymonadInstancesInScope = do
  mPolymonadClass <- findPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- TcPluginM.getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []

-- | Subset selection algorithm to select the correct subset of
--   type constructor and bind instances that belong to the polymonad
--   being worked with in the list of /given/ and /wanted/ constraints.
--
--   Currently we assume that the plugin is only used for standard and
--   parameterized monads. We also assume that the indices of parameterized
--   monads are phantom and do not incluence the runtime behaviour.
--   Because of these preconditions all polymonad instances together actually
--   form a principal polymonad and the selection of a subset is not necessary
--   and therefore currently not done.
--
--   FIXME: Work in Progress / Unfinished
selectPolymonadSubset :: TyCon -> Class -> [ClsInst] -> ([Ct], [Ct]) -> TcPluginM (Set TyCon, [Type], [ClsInst])
selectPolymonadSubset idTyCon pmCls pmInsts (givenCts, wantedCts) = do
  -- TODO: This is just a very naiv approach to get things up and running.
  let givenPmTyCons  = S.unions $ fmap constraintTyCons givenPmCts
  let wantedPmTyCons = S.unions $ fmap constraintTyCons wantedPmCts
  let pmTyCons = givenPmTyCons `S.union` wantedPmTyCons `S.union` S.singleton idTyCon
  let varTyCons = filter (isTyVarTy . fst . splitAppTys)
                $ concat $ catMaybes $ fmap constraintClassTyArgs givenPmCts
  relevantInsts <- filterApplicableInstances pmInsts pmTyCons
  return (pmTyCons, varTyCons, relevantInsts)
  where
    givenPmCts = filter (\ct -> isClassConstraint pmCls ct && (isDerivedCt ct || isGivenCt ct)) givenCts
    wantedPmCts = filter (\ct -> isClassConstraint pmCls ct && isWantedCt ct) wantedCts
    {-
    -- TODO
    c :: Int -> TcPluginM (Set TyCon , [ClsInst])
    c 0 = do
      let initialTcs = S.unions $ fmap constraintTyCons wantedPmCts
      return (initialTcs, [])
    c n = do
      (initialTcs, _initialClsInsts) <- c (n - 1)

      return (initialTcs `S.union` undefined, undefined)

    appTC :: Set TyCon -> ClsInst -> TyVar -> TcPluginM (Set TyCon, [ClsInst])
    appTC tcsCn clsInst tcVarArg =
      if instanceTyCons clsInst `S.isSubsetOf` tcsCn
        then do
          let tcVarArgs = S.delete tcVarArg $ instanceTcVars clsInst
          -- TODO
          -- Substitute tycons (already collected ones) for the given argument
          -- Substitute all possible tycons for the rest of the arguments
          -- Find applicable instances and return the together with all of the substituted tycons
          return (undefined, undefined)
        else return (S.empty, [])
    -}
-- | Filters the list of polymonads constraints, to only keep those
--   that can be applied to the given type constructors.
filterApplicableInstances :: [ClsInst] -> Set TyCon -> TcPluginM [ClsInst]
filterApplicableInstances pmInsts tcs = do
  appliedTyCons <- forM (S.toList tcs) $ \tc -> do
    let (indexKinds, _unaryKind) = splitFunTysN (tyConArity tc - 1) (tyConKind tc)
    if null indexKinds then do
      indexVars <- mapM newFlexiTyVar indexKinds
      return $ mkTyConApp tc $ mkTyVarTy <$> indexVars
    else
      return $ mkTyConTy tc
  filteredInsts <- forM pmInsts $ \pmInst -> do
    let (_instTvs, _instCtTys, _instCls, instArgs) = instanceSig pmInst
    --associations :: [(key , [value])] -> [[(key, value)]]
    let assocs = fmap snd <$> associations [(instArg, appliedTyCons) | instArg <- instArgs]
    mListInsts <- forM assocs $ \assoc -> case tcUnifyTys instanceBindFun instArgs assoc of
      Just _subst ->
        -- TODO: For now we just accept this, although superclasses might keep
        -- us from actually using this instance. In future we probably want to
        -- check instCtTys for matches.
        return $ Just pmInst
      Nothing -> return Nothing
    return $ catMaybes mListInsts
  return $ concat filteredInsts

-- | Internal function for printing from within the monad.
internalPrint :: String -> TcPluginM ()
internalPrint = tcPluginIO . putStr

printMsg :: String -> TcPluginM ()
printMsg = internalPrint . pmDebugMsg

printObj :: Outputable o => o -> TcPluginM ()
printObj = internalPrint . pmObjMsg . pprToStr

-- -----------------------------------------------------------------------------
-- Local Utility Functions
-- -----------------------------------------------------------------------------

-- | Checks if the module with the given name is imported and,
--   if so, returns that module.
getModule :: Maybe PackageKey -> String -> TcPluginM (Either String Module)
getModule pkgKeyToFind mdlNameToFind = do
  mdlResult <- findImportedModule (mkModuleName mdlNameToFind) Nothing
  case mdlResult of
    Found _mdlLoc mdl ->
      if maybe True (modulePackageKey mdl ==) pkgKeyToFind then
        return $ Right mdl
      else
        return $ Left $ pmErrMsg
          $  "Package key of found module (" ++ pprToStr (modulePackageKey mdl) ++ ")"
          ++ " does not match the requested key (" ++ pprToStr pkgKeyToFind ++ ")."
    NoPackage pkgKey -> return $ Left $ pmErrMsg
      $ "Found module, but missing its package: " ++ pprToStr pkgKey
    FoundMultiple mdls -> return $ Left $ pmErrMsg
      $ "Module " ++ mdlNameToFind ++ " appears in several packages:\n"
      ++ pprToStr (fmap snd mdls)
    NotFound {} -> return $ Left $ pmErrMsg "Module was not found."
{-
  impMdls <- fmap (moduleEnvKeys . imp_mods . tcg_imports . fst) getEnvs
  foundMdls <- flip filterM impMdls $ \m -> do
    let pkgKey = modulePackageKey m
    let mdlName = moduleNameString $ moduleName m
    return $ pkgKey == pkgKeyToFind && mdlName == mdlNameToFind
  return $ case foundMdls of
    [m] -> Just m
    _ -> Nothing
-}

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
