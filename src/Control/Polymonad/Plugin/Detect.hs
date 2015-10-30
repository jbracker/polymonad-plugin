
-- | Functions and utilities to detect the importent modules, classes
--   and types of the plugin.
module Control.Polymonad.Plugin.Detect
  ( -- * Polymonad Class Detection
    polymonadModuleName
  , polymonadClassName
  , findPolymonadModule
  , findPolymonadPreludeModule
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
  , pickInstanceForAppliedConstraint
  , produceEvidenceFor
  ) where

import Data.Maybe
  ( isNothing, isJust
  , catMaybes, listToMaybe
  , fromJust )
import Data.List ( nubBy )
import Data.Tuple ( swap )
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
  , splitAppTys, eqType
  , mkTyConTy, mkTopTvSubst
  , substTys
  , tyConAppTyCon_maybe
  , getClassPredTys_maybe )
import TyCon ( TyCon )
import TcPluginM
  ( TcPluginM
  , getEnvs, getInstEnvs
  , findImportedModule, FindResult(..)
  , tcLookup )
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
  , classInstances
  , lookupInstEnv
  , lookupUniqueInstEnv
  , ie_global )
import TcEvidence ( EvTerm(..) )

import Control.Polymonad.Plugin.Log
  ( pmErrMsg
  , printMsg
  , pprToStr )
import Control.Polymonad.Plugin.Utils
  ( associations, lookupBy
  , isAmbiguousType )
import Control.Polymonad.Plugin.Constraint
  ( GivenCt, WantedCt
  , constraintClassTyArgs, constraintPolymonadTyArgs'
  , isClassConstraint, isFullyAppliedClassConstraint )
import Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars, isInstantiatedBy, eqInstance )

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

polymonadPreudeModuleName :: String
polymonadPreudeModuleName = "Control.Polymonad.Prelude"

-- -----------------------------------------------------------------------------
-- Polymonad Class Detection
-- -----------------------------------------------------------------------------

-- | Checks if the module 'Control.Polymonad'
--   is imported and, if so, returns the module.
findPolymonadModule :: TcPluginM (Either String Module)
findPolymonadModule = do
  eitherMdl <- getModule Nothing polymonadModuleName
  case eitherMdl of
    Left _err -> findPolymonadPreludeModule
    Right mdl -> return $ Right mdl

-- | Checks if the module 'Control.Polymonad.Prelude'
--   is imported and, if so, returns the module.
findPolymonadPreludeModule :: TcPluginM (Either String Module)
findPolymonadPreludeModule = getModule Nothing polymonadPreudeModuleName

-- | Check if the given module is the polymonad module.
isPolymonadModule :: Module -> Bool
isPolymonadModule mdl = mdlName `elem` [pmMdlName, pmPrelName]
  where mdlName = moduleName mdl
        pmMdlName = mkModuleName polymonadModuleName
        pmPrelName = mkModuleName polymonadPreudeModuleName

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
  let isPmCls = isPolymonadClass . is_cls
  -- This is needed while compiling the package itself...
  foundInstsLcl <- filter isPmCls . instEnvElts . tcg_inst_env . fst <$> getEnvs
  -- This is needed while compiling an external package depending on it...
  foundInstsGbl <- filter isPmCls . instEnvElts . ie_global <$> getInstEnvs
  return $ case foundInstsLcl ++ foundInstsGbl of
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
  mdls <- findModules [findIdentityModule, findPolymonadModule, findPolymonadPreludeModule]
  case mdls of
    [] -> return Nothing
    _ -> findTyConByNameAndModule (mkTcOcc identityTyConName) mdls

-- -----------------------------------------------------------------------------
-- Subset Selection
-- -----------------------------------------------------------------------------

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

-- | Separates wanted constraints into different polymonads by looking
--   at the connected components that are created by the implied bind-operations.
--   Each component is assumed to be one polymonad.
selectPolymonadByConnectedComponent :: SubsetSelectionFunction
selectPolymonadByConnectedComponent idTc pmCls pmInsts (gdCts, wCts) = do
  let graphComps = components componentGraph
  -- Get all of the fully applied constraints from the wanted ones to re-add
  -- them later, because 'Polymonad Identity Identity Identity' will never be
  -- captured by the component algorithm but is part of every polymonad!
  let fullyAppliedWantedCts = filter isFullyAppliedClassConstraint wCts
  -- Now get the wanted constraint components that describe the different polymonads.
  -- Add the fully applied constraints to each one to make sure 'Polymonad Identity Identity Identity'
  -- is in every one.
  -- FIXME: Specifically select and re-add 'Polymonad Identity Identity Identity'.
  let wCtComps = [ nubBy eqCt $ concat [ ctForNode compNode | compNode <- comp ] ++ fullyAppliedWantedCts | comp <- graphComps ]
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
    mListInsts <- forM assocs $ \assoc ->
      case matchInstanceTyVars assoc pmInst of
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

-- -----------------------------------------------------------------------------
-- Selection of instance for fully applied constraints.
-- -----------------------------------------------------------------------------

-- | Given a fully applied polymonad constraint it will pick the first instance
--   that matches it. This is ok to do, because for polymonads it does
--   not make a difference which bind-operation we pick if the type is equal.
pickInstanceForAppliedConstraint :: Class -> WantedCt -> TcPluginM (Maybe (EvTerm, Ct))
pickInstanceForAppliedConstraint pmCls ct =
  case constraintClassTyArgs ct of
    -- We found the polymonad class constructor and the given constraint
    -- is a instance constraint.
    Just tyArgs
        -- Be sure to only proceed if the constraint is a polymonad constraint
        -- and is fully applied to concrete types.
        |  isClassConstraint pmCls ct
        && isFullyAppliedClassConstraint ct -> do
      -- Get the instance environment
      instEnvs <- getInstEnvs
      -- Find matching instance for our constraint.
      let (matches, _, _) = lookupInstEnv instEnvs pmCls tyArgs
      -- Only keep those matches that actually found a type for every argument.
      case filter (\(_, args) -> all isJust args) matches of
        -- If we found more then one instance, just use the first.
        -- Because we are talking about polymonad we can freely choose.
        (foundInst, foundInstArgs) : _ -> do
          -- Try to produce evidence for the instance we want to use.
          evTerm <- produceEvidenceFor foundInst (fromJust <$> foundInstArgs)
          return $ (\ev -> (ev, ct)) <$> evTerm
        _ -> return Nothing
    _ -> return Nothing


-- | Apply the given instance dictionary to the given type arguments
--   and try to produce evidence for the application.
--   The list of types has to match the number of open variables of the
--   given instance dictionary in length.
produceEvidenceFor :: ClsInst -> [Type] -> TcPluginM (Maybe EvTerm)
produceEvidenceFor inst tys = do
  -- Get the instance type variables and constraints (by that we know the
  -- number of type arguments and dictionart arguments for the EvDFunApp)
  let (tyVars, cts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
  -- How the instance variables for the current instance are bound.
  let varSubst = mkTopTvSubst $ zip tyVars tys
  -- Global instance environment.
  instEnvs <- getInstEnvs
  -- Split the constraints into their class and arguments.
  -- We ignore constraints where this is not possible.
  -- Don't know if this is the right thing to do.
  let instCts = catMaybes $ fmap getClassPredTys_maybe cts
  -- Now go over each constraint and find a suitable instance and evidence.
  ctEvTerms <- forM instCts $ \(ctCls, ctArgs) -> do
    -- Substitute the variables to know what instance we are looking for.
    let substArgs = substTys varSubst ctArgs
    -- Look for suitable instance. Since we are not necessarily working
    -- with polymonads anymore we need to find a unique one.
    case lookupUniqueInstEnv instEnvs ctCls substArgs of
      -- No instance found, too bad...
      Left _err -> return Nothing
      -- We found one: Now we can produce evidence for the found instance.
      Right (clsInst, instArgs) -> produceEvidenceFor clsInst instArgs
  -- If we found a good instance and evidence for every constraint,
  -- we can create the evidence for this instance.
  return $ if any isNothing ctEvTerms
    then Nothing
    else Just $ EvDFunApp (is_dfun inst) tys (fromJust <$> ctEvTerms)

-- -----------------------------------------------------------------------------
-- Local Utility Functions
-- -----------------------------------------------------------------------------

-- | Tries to find all of the given modules using the given search functions.
--   Returns the list of all found modules.
findModules :: [TcPluginM (Either String Module)] -> TcPluginM [Module]
findModules findMdls = do
  eitherMdls <- sequence findMdls
  return $ catMaybes $ fmap (either (const Nothing) Just) eitherMdls

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
