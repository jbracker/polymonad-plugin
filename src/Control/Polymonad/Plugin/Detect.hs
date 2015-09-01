
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
    -- * Subset Selection Algorithms
  , SubsetSelectionFunction
  , selectPolymonadByConnectedComponent
  , selectPolymonadSubset
  ) where

import Data.Maybe ( catMaybes, listToMaybe, fromJust )
import Data.List ( nubBy )
import Data.Tuple ( swap )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Graph.Inductive.Graph
  ( Node, mkGraph )
import Data.Graph.Inductive.PatriciaTree ( Gr )
import Data.Graph.Inductive.Query.DFS ( components )

import Control.Monad ( forM, liftM )

import TcRnTypes
  ( Ct, ctPred, ctLocSpan, ctLoc
  , isGivenCt, isWantedCt, isDerivedCt
  , TcGblEnv(..)
  , TcTyThing(..) )
import Type
  ( Type, TyThing(..)
  , isTyVarTy, splitAppTys
  , splitFunTysN, eqType
  , mkTyConApp, mkTyVarTy, mkTyConTy
  , tyConAppTyCon_maybe )
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
import InstEnv
  ( ClsInst(..)
  , instEnvElts
  , instanceSig
  , classInstances )
import Outputable ( Outputable )

import Control.Polymonad.Plugin.Log
  ( pmErrMsg, pmDebugMsg, pmObjMsg
  , pprToStr )
import Control.Polymonad.Plugin.Utils
  ( associations, lookupBy
  , isAmbiguousType )
import Control.Polymonad.Plugin.Constraint
  ( constraintTyCons, constraintClassTyArgs, constraintPolymonadTyArgs'
  , isClassConstraint )
import Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars, isInstantiatedBy, eqInstance )

-- -----------------------------------------------------------------------------
-- Debugging
-- -----------------------------------------------------------------------------

-- | Internal function for printing from within the monad.
internalPrint :: String -> TcPluginM ()
internalPrint = tcPluginIO . putStr

printMsg :: String -> TcPluginM ()
printMsg = internalPrint . pmDebugMsg

printObj :: Outputable o => o -> TcPluginM ()
printObj = internalPrint . pmObjMsg . pprToStr

-- -----------------------------------------------------------------------------
-- Constant Names (Magic Numbers...)
-- -----------------------------------------------------------------------------

-- | Name of the 'Control.Polymonad' module.
polymonadModuleName :: String
polymonadModuleName = "Control.Polymonad"

-- | Name of the 'Polymonad' type class.
polymonadClassName :: String
polymonadClassName = "Polymonad"

-- | Name of the 'Data.Functor.Identity' module.
identityModuleName :: String
identityModuleName = "Data.Functor.Identity"

-- | Name of the 'Identity' type constructor.
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

-- | Tries to find the identity type constructor in the imported
--   modules. Will accept the constructor if it is imported through
--   either 'Data.Functor.Identity' or 'Control.Polymonad'.
findIdentityTyCon :: TcPluginM (Maybe TyCon)
findIdentityTyCon = do
  mIdModule <- either (const Nothing) Just<$> findIdentityModule
  mPolymonadMdl <- either (const Nothing) Just <$> findPolymonadModule
  case (mIdModule, mPolymonadMdl) of
    (Nothing, Nothing) -> return Nothing
    _ -> findTyConByNameAndModule (mkTcOcc identityTyConName) $ catMaybes [mIdModule, mPolymonadMdl]

-- -----------------------------------------------------------------------------
-- Subset Selection
-- -----------------------------------------------------------------------------

type WantedCt = Ct
type GivenCt = Ct

-- | Type signature of a subset selection function.
--
--   @subsetSelectionFunction idTc pmCls pmInsts (givenDerivedCts, wantedCts)@
--
--   * @idTc@ - The 'Identity' type constructor.
--   * @pmCls@ - The 'Polymonad' class.
--   * @pmInsts@ - The available 'Polymonad' instances.
--   * @givenDerivedCts@ - The given and derived constraints
--     (all of them, not only polymonad constraints).
--   * @wantedCts@ - The wanted constraints.
--     (all of them, not only polymonad constraints).
--
--   Returns the (possibly partially applied) type constructors and type variables
--   together with class instances and given/derived constraints that
--   make up each detected polymonad.
--   Each polymonad is paired with the list of wanted constraints that need to
--   be solved with it.
type SubsetSelectionFunction =
  TyCon -> Class -> [ClsInst] -> ([GivenCt], [WantedCt]) -> TcPluginM [(([Type], [ClsInst], [GivenCt]), [WantedCt])]

selectPolymonadByConnectedComponent :: SubsetSelectionFunction
selectPolymonadByConnectedComponent idTc pmCls pmInsts (gdCts, wCts) = do
  let graphComps = components componentGraph
  let wCtComps = [ nubBy eqCt $ concat [ ctForNode compNode | compNode <- comp ] | comp <- graphComps ]
  forM wCtComps $ \wCtComp -> findPolymonadFor wCtComp >>= \pm -> return (pm, wCtComp)
  where
    findPolymonadFor :: [WantedCt] -> TcPluginM ([Type], [ClsInst], [GivenCt])
    findPolymonadFor wantedCts = do
      -- Collect all type constructors that are involved in the wanted constraints
      -- but remove that that are ambiguous.
      let tyCons = nubBy eqType $ (mkTyConTy idTc :) $ filter (not . isAmbiguous)
                 $ concat $ catMaybes $ constraintClassTyArgs <$> wantedCts
      -- filterApplicableInstances :: [GivenCt] -> [ClsInst] -> [Type] -> TcPluginM [ClsInst]
      -- Filter out the instances that are relevant to this polymonad.
      insts <- filterApplicableInstances gdCts pmInsts tyCons
      -- Return the polymonad.
      -- FIXME/TODO: Is it necessary to also filter the given and
      -- derived polymonad constraints?
      return (tyCons, insts, givenPmCts)

    -- The given and derived polymonad constraints.
    givenPmCts = filter (\ct -> isClassConstraint pmCls ct && (isDerivedCt ct || isGivenCt ct)) gdCts
    -- The wanted polymonad constraints.
    wantedPmCts = filter (\ct -> isClassConstraint pmCls ct && isWantedCt ct) wCts

    -- Try to compare two constraints for equality.
    -- Should suffice in this context.
    eqCt :: Ct -> Ct -> Bool
    eqCt ct0 ct1 = eqType (ctPred ct0) (ctPred ct1) && ctLocSpan (ctLoc ct0) == ctLocSpan (ctLoc ct1)

    -- List of wanted constraints together with their arguments
    -- types. Only contains polymonad constraints.
    wCtTypes :: [(WantedCt, Type, Type, Type)]
    wCtTypes = constraintPolymonadTyArgs' wantedPmCts

    wCtTyVarTypes :: [(Node, Type)]
    wCtTyVarTypes = zip [0..]
                  $ nubBy eqType
                  $ filter isNotIdentity
                  $ concatMap (\(_, t0, t1, t2) -> [t0, t1, t2]) wCtTypes

    wCtTyVarTypes' :: [(Type, Node)]
    wCtTyVarTypes' = swap <$> wCtTyVarTypes

    typeToNode :: Type -> Node
    typeToNode t = fromJust $ lookupBy eqType t wCtTyVarTypes'

    nodeToType :: Node -> Type
    nodeToType n = fromJust $ lookup n wCtTyVarTypes

    ctForNode :: Node -> [WantedCt]
    ctForNode n =
      let t = nodeToType n
      in (\(ct, _, _, _) -> ct) <$> filter (\(_, t0, t1, t2) -> eqType t t0 || eqType t t1 || eqType t t2) wCtTypes

    -- The nodes of our graph are ambiguous type variable. The edges are the
    -- constraints that created them.
    componentGraph :: Gr Type WantedCt
    componentGraph = mkGraph wCtTyVarTypes $
      [ (typeToNode t0, typeToNode t2, ct) | (ct, t0, _t1, t2) <- wCtTypes, isNotIdentity t0, isNotIdentity t2 ] ++
      [ (typeToNode t1, typeToNode t2, ct) | (ct, _t0, t1, t2) <- wCtTypes, isNotIdentity t1, isNotIdentity t2 ] -- Edges

    isNotIdentity :: Type -> Bool
    isNotIdentity t = maybe True (/= idTc) $ tyConAppTyCon_maybe t

    isAmbiguous :: Type -> Bool
    isAmbiguous t = isAmbiguousType t || isAmbiguousType (fst $ splitAppTys t)

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
  relevantInsts <- filterApplicableInstances' pmInsts pmTyCons
  return (pmTyCons, varTyCons, relevantInsts)
  where
    givenPmCts = filter (\ct -> isClassConstraint pmCls ct && (isDerivedCt ct || isGivenCt ct)) givenCts
    wantedPmCts = filter (\ct -> isClassConstraint pmCls ct && isWantedCt ct) wantedCts

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

-- | Filters the list of polymonads constraints, to only keep those
--   that can be applied to the given type constructors.
--   The given list of type constructors is assumed to only contain unary
--   type constructors. These type constructors are also assumed to not be
--   ambiguous.
--
--   The list of constraints contains the given and derived constraints that might be
--   needed when checking if a instance is instantiated. These constraints
--   should include non-polymonad constraints as well.
filterApplicableInstances :: [GivenCt] -> [ClsInst] -> [Type] -> TcPluginM [ClsInst]
filterApplicableInstances givenCts pmInsts appliedTyCons =
  fmap (nubBy eqInstance . concat) $ forM pmInsts $ \pmInst -> do
    -- Get the arguments of the instance we are looking at.
    let (_instTvs, _instCtTys, _instCls, instArgs) = instanceSig pmInst
    -- associations :: [(key , [value])] -> [[(key, value)]]
    -- Now create all associations between arguments and type constructors that are available.
    let assocs = fmap snd <$> associations [(instArg, appliedTyCons) | instArg <- instArgs]
    -- Look at each of those associations and check if it actually instantiates.
    mListInsts <- forM assocs $ \assoc -> case matchInstanceTyVars assoc pmInst of
      -- Association matches instance arguments, proceed...
      Just instTvArgs -> do
        -- Check if the given association actually instanctiates.
        eIsInst <- isInstantiatedBy givenCts instTvArgs pmInst
        -- Return instance if association instantiates.
        case eIsInst of
          Left err -> do
            printMsg err
            return Nothing
          Right isInst -> return $ if isInst then Just pmInst else Nothing
      -- Association does not even match instance arguments, so it will not instantiate.
      Nothing -> return Nothing
    -- Only keep those instances that actually are instantiated.
    return $ catMaybes mListInsts


-- | Returns a list of all 'Control.Polymonad' instances that are currently in scope.
findPolymonadInstancesInScope :: TcPluginM [ClsInst]
findPolymonadInstancesInScope = do
  mPolymonadClass <- findPolymonadClass
  case mPolymonadClass of
    Just polymonadClass -> do
      instEnvs <- TcPluginM.getInstEnvs
      return $ classInstances instEnvs polymonadClass
    Nothing -> return []

-- | Filters the list of polymonads constraints, to only keep those
--   that can be applied to the given type constructors.
-- TODO: Remove when unused.
filterApplicableInstances' :: [ClsInst] -> Set TyCon -> TcPluginM [ClsInst]
filterApplicableInstances' pmInsts tcs = do
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
    mListInsts <- forM assocs $ \assoc -> case matchInstanceTyVars assoc pmInst of
      Just instTvArgs -> do
        eIsInst <- isInstantiatedBy undefined instTvArgs pmInst
        case eIsInst of
          Left err -> do
            printMsg err
            return Nothing
          Right isInst -> return $ if isInst then Just pmInst else Nothing
      Nothing -> return Nothing
    return $ catMaybes mListInsts
  return $ concat filteredInsts

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

-- | Try to find a type constructor given its name and the modules it
--   is exported from. The type constructor needs to be imported from
--   one of these modules.
findTyConByNameAndModule :: OccName -> [Module] -> TcPluginM (Maybe TyCon)
findTyConByNameAndModule occName mdls = do
  -- Look at the global environment of names that are in scope.
  rdrEnv <- tcg_rdr_env . fst <$> getEnvs
  -- Search for things that have the same name as what we are looking for.
  let envResultElem = lookupGlobalRdrEnv rdrEnv occName
  -- Only keep things that are originally from our module and have no parents,
  -- because type constructors are declared on top-level.
  let relResults = filter
        (\e -> any (e `isImportedFrom`) mdls && hasNoParent e)
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

-- | Check if the given element is imported from the given module.
isImportedFrom :: GlobalRdrElt -> Module -> Bool
isImportedFrom rdrElt mdl = case gre_prov rdrElt of
  LocalDef -> False
  Imported [] -> False
  Imported impSpecs -> moduleName mdl == importSpecModule (last impSpecs)
