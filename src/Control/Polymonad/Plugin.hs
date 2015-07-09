-- | Provides the polymonad plugin for GHC.
module Control.Polymonad.Plugin
  ( plugin ) where

import Data.Maybe ( catMaybes )
import Data.List ( partition )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( guard, MonadPlus(..) )

import Debug.Trace ( trace )

import Plugins ( Plugin(tcPlugin), defaultPlugin )

import TcRnTypes
import TcPluginM

--import Unique ( getUnique, mkTcOccUnique )
import Name
  ( Name
  , getName )
import Type
  ( Type, TvSubst
  , EqRel(..)
  --, eqType
  --, isTyVarTy, isAlgType
  , substTys )
{-import Module
  ( Module(..)
  , mainPackageKey
  --, moduleEnvToList
  , moduleEnvKeys
  , moduleNameString )-}
import Class {-
  ( Class
  , className, classMethods, classArity
  , classTyVars, classTyCon ) -}
--import FastString ( mkFastString )
--import SrcLoc ( noSrcSpan )
--import HscTypes ( typeEnvTyCons )
import TcType
  ( isClassPred
  --, isDictLikeTy
  , tcTyConAppTyCon, tcTyConAppArgs
  , tcGetTyVar_maybe, tcSplitDFunTy
  , topTcLevel
  --, TvSubst
  , substTyVar, notElemTvSubst
  , TcTyVar, TcType )
--import TcEvidence ( EvTerm(..) )
import InstEnv
  ( ClsInst(..)
  --, InstEnvs(..)
  , DFunId
  --, instanceSig
  , instanceBindFun, instanceDFunId )
import Unify ( tcUnifyTys )
--import PrelNames ( monadClassName )
import Outputable ( Outputable )

import Control.Polymonad.Plugin.Utils
  ( printM, printppr, pprToStr )
import Control.Polymonad.Plugin.Detect
  ( getPolymonadClass
  , getIdentityModule
  , getIdentityTyCon )
import Control.Polymonad.Plugin.Constraint
  ( isClassConstraint, isFullyAppliedClassConstraint
  , mkDerivedTypeEqCt, constraintTopAmbiguousTyVars )
import Control.Polymonad.Plugin.Core
  ( getPolymonadInstancesInScope
  , getPolymonadTyConsInScope
  , pickInstanceForAppliedConstraint )
import Control.Polymonad.Plugin.Graph
  ( mkGraphView )
import Control.Polymonad.Plugin.Simplification
  ( simplifyAllUpDown , simplifiedTvsToConstraints )

-- -----------------------------------------------------------------------------
-- The Plugin
-- -----------------------------------------------------------------------------

-- | The polymonad type checker plugin for GHC.
plugin :: Plugin
plugin = defaultPlugin
  { tcPlugin = \_clos -> Just polymonadPlugin
  }

-- -----------------------------------------------------------------------------
-- Actual Plugin Code
-- -----------------------------------------------------------------------------

type PolymonadState = ()

polymonadPlugin :: TcPlugin
polymonadPlugin = TcPlugin
  { tcPluginInit  = polymonadInit
  , tcPluginSolve = polymonadSolve
  , tcPluginStop  = polymonadStop
  }

polymonadInit :: TcPluginM PolymonadState
polymonadInit = do
  printM ">>> Plugin Init..."
  printM ""
  return ()

polymonadSolve :: PolymonadState -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
polymonadSolve s given derived wanted = do
  printM ">>> Plugin Solve..."
  printppr given
  printppr derived
  printppr wanted
  printM ">>>>>>>>>>>>>>>>>>>"
  if not $ null wanted then do
    mPolymonadCls <- getPolymonadClass
    mIdTyCon <- getIdentityTyCon
    case (mPolymonadCls, mIdTyCon) of
      (Just polymonadCls, Just idTyCon) -> do
        printM ">>> Polymonad in scope, wanted constraints not empty, invoke solver..."
        let (wantedApplied, wantedIncomplete) = partition isFullyAppliedClassConstraint wanted
        --polymonadSolve' s polymonadCls (given, derived, wanted)
        printM ">>>>> Solve Wanted Incompletes"
        printppr wantedIncomplete
        let ambTvs = S.unions $ constraintTopAmbiguousTyVars <$> wantedIncomplete
        let eqCts = simplifiedTvsToConstraints $ simplifyAllUpDown idTyCon wantedIncomplete ambTvs
        printppr eqCts

        printM ">>>>> Solve Wanted Completes"
        printppr wantedApplied
        mWantedEvidence <- mapM pickInstanceForAppliedConstraint wantedApplied
        printppr mWantedEvidence
        return $ TcPluginOk (catMaybes mWantedEvidence) eqCts
      _ -> returnNoResult
  else do
    returnNoResult

polymonadStop :: PolymonadState -> TcPluginM ()
polymonadStop _state = do
  printM ">>> Plugin Stop..."
  printM ""

  return ()

-- -----------------------------------------------------------------------------
-- Solver of the Plugin
-- -----------------------------------------------------------------------------

polymonadSolve' :: PolymonadState -> Class -> ([Ct], [Ct], [Ct]) -> TcPluginM TcPluginResult
polymonadSolve' _s polymonadCls (_given, _derived, wanted) = do
  {-
  instEnv <- fmap (tcg_inst_env . fst) getEnvs
  let pmInsts = flip filter (instEnvElts instEnv) $ \inst -> is_cls inst == polymonadCls
  printppr instEnv
  -}
  {-
  printM ">>> CALLED"
  when (not $ null given) $ do
    printM "Given"
    printppr given
  when (not $ null derived) $ do
    printM "Derived"
    printppr derived
  when (not $ null wanted) $ do
    printM "Wanted"
    printppr wanted
  return $ TcPluginOk [] []
  -}
  --printM "> Available Polymonad instances"
  pmInsts <- getPolymonadInstancesInScope
  --printppr $ mapM mkPolymonadInst $ pmInsts

  --printM "> Wanted Constraints"
  --printppr wanted

  --printM "> Polymonad Constraints"
  -- [Ct]
  let pmCts = filter (isClassConstraint polymonadCls) wanted
  --printppr pmCts
  {-
  printM "> SOME INFO"
  sequence_ $ flip fmap pmCts $ \ct -> case ct of
    (CDictCan ev polymonadCls tya) -> do
      printM "CDictCan"
    (CNonCanonical (CtWanted pred evar loc)) -> do
      printM "CNonCanonical (Wanted)"
      printppr pred
      printppr evar
    _ -> printM "Other"
  -}
  -- [(Ct, [(ClsInst, TvSubst)])]
  ctMatches <- flip mapM pmCts $ \pmCt -> do
    --printM "> Matching Instances for..."
    --printppr pmCt
    --printppr $ findMatchingInstances pmInsts pmCt
    return (pmCt, findMatchingInstances' pmInsts pmCt)

  -- [Ct]
  derivedList <- fmap concat $ flip mapM ctMatches $ \(pmCt, ctSolutions) -> do
    case ctSolutions of
      [(clsInst, subst)] -> do
        let _ts = substTys subst (is_tys clsInst) :: [Type]
        let _instId = instanceDFunId clsInst :: DFunId
        -- [(EvTerm, Ct)]
        -- return [(EvDFunApp instId {-ts-} [] [], pmCt)]

        -- [Ct]
        mkEqCtsFromSubst pmCt subst
      _ -> return []

  let evidenceList = []
  printppr derivedList
  printM ""
  return $ TcPluginOk evidenceList derivedList


findMatchingInstances' :: [ClsInst] -> Ct -> [(ClsInst, TvSubst)]
findMatchingInstances' insts ct = do
  inst <- insts
  let ctTys = ctTyParams ct
  guard $ is_cls_nm inst == ctName ct
  case tcUnifyTys instanceBindFun (is_tys inst) ctTys of
    Just subst -> do
      return (inst, subst)
    Nothing -> mzero

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

mkEqCtsFromSubst :: Ct -> TvSubst -> TcPluginM [Ct]
mkEqCtsFromSubst wantedCt subst = do
  printM "=== mkEqCtsFromSubst ==="
  let wantedCtTy = ctPred wantedCt
  case isClassPred wantedCtTy of
    False -> do
      printM "=== No class pred"
      printppr wantedCtTy
      return []
    True -> do
      printM "=== Gen Eq for class"
      printppr wantedCtTy
      let (_vars, _, _cls, tyParams) = tcSplitDFunTy wantedCtTy
      let vars = catMaybes $ fmap tcGetTyVar_maybe tyParams
      printppr $ vars
      let inScopeVars = filter (\v -> not $ notElemTvSubst v subst) vars
      printppr inScopeVars
      flip mapM inScopeVars $ \var -> do -- type variables in
        return $ mkDerivedTypeEqCt wantedCt var (substTyVar subst var)

returnNoResult :: TcPluginM TcPluginResult
returnNoResult = return $ TcPluginOk [] []

ctName :: Ct -> Name
ctName ct = case ct of
  CDictCan _ cls _ -> className cls
  CNonCanonical evdnc -> ctEvidenceName evdnc
  v -> missingCaseError "ctName" $ Just v

ctEvidenceName :: CtEvidence -> Name
ctEvidenceName evdnc = case evdnc of
  CtWanted predTy _ _ -> getName (tcTyConAppTyCon predTy)
  v -> missingCaseError "ctEvidenceName" $ Just v

ctTyParams :: Ct -> [Type]
ctTyParams ct = case ct of
  CDictCan _ _ _ -> cc_tyargs ct
  CNonCanonical evdnc -> ctEvidenceTyParams evdnc
  v -> missingCaseError "ctTyParams" $ Just v

ctEvidenceTyParams :: CtEvidence -> [Type]
ctEvidenceTyParams evdnc = tcTyConAppArgs $ ctev_pred evdnc

missingCaseError :: (Outputable o) => String -> Maybe o -> a
missingCaseError funName (Just val) = error $ "Missing case in '" ++ funName ++ "' for " ++ pprToStr val
missingCaseError funName Nothing    = error $ "Missing case in '" ++ funName ++ "'"

-- -----------------------------------------------------------------------------
-- Notes
-- -----------------------------------------------------------------------------

{-

TcGblEnv.tcg_type_env:
Only contains type and data constructors (and classes?)
from the currently compiled module not the imported data.

TcGblEnv.tcg_inst_env:
Contains all locally defined and imported instances,
but not any derived instances.

TcGblEnv.tcg_insts:
All locally defined instances.

TcGblEnv.tcg_imports.imp_dep_mods:
Local (not from other packages) modules this module
depends on. This will also include modules imported by imported
modules.

TcGblEnv.tcg_imports.imp_dep_pkgs:
Packages this modules depends on.

TcGblEnv.tcg_imports.imp_mods.moduleEnvToList:
Modules directly imported by the current module.
[ ( Module - The imported module
  , [ ( ModuleName - Alias name of the module
      , Bool - Was import of form: import Foo ()
      , SrcSpan - Location of import declaration in file
      , IsSafeImport - Whatever a safe import is
      )
    ]
  )
]

-}
