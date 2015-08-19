-- | Provides the polymonad plugin for GHC.
module Control.Polymonad.Plugin
  ( plugin ) where

import Data.Maybe ( catMaybes )
import Data.List ( partition )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( guard, unless, MonadPlus(..) )

import Debug.Trace ( trace )

import Plugins ( Plugin(tcPlugin), defaultPlugin )

import TcRnTypes

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
import TcPluginM ( TcPluginM, tcPluginIO )

import Control.Polymonad.Plugin.Log ( pprToStr )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runPmPlugin
  , getIdentityTyCon, getPolymonadClass, getPolymonadInstances
  , getCurrentPolymonad
  , getWantedPolymonadConstraints, getGivenPolymonadConstraints
  , printMsg, printObj, printErr )
import Control.Polymonad.Plugin.Detect
  ( findPolymonadClass
  , findIdentityModule
  , findIdentityTyCon )
import Control.Polymonad.Plugin.Constraint
  ( isClassConstraint, isFullyAppliedClassConstraint
  , mkDerivedTypeEqCt, constraintTopAmbiguousTyVars )
import Control.Polymonad.Plugin.Core
  ( pickInstanceForAppliedConstraint )
import Control.Polymonad.Plugin.GraphView
  ( mkGraphView )
import Control.Polymonad.Plugin.Solve
  ( solve )
import Control.Polymonad.Plugin.Ambiguity
  ( isAllUnambigious )
import Control.Polymonad.Plugin.Simplification
  ( simplifyAllUpDown, simplifyAllJoin
  , simplifiedTvsToConstraints )

-- -----------------------------------------------------------------------------
-- The Plugin
-- -----------------------------------------------------------------------------

-- | The polymonad type checker plugin for GHC.
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \_clOpts -> Just polymonadPlugin }

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
polymonadInit = return ()

polymonadStop :: PolymonadState -> TcPluginM ()
polymonadStop _s = return ()

polymonadSolve :: PolymonadState -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
polymonadSolve s given derived wanted = do
  res <- runPmPlugin given wanted $ do
    unless (null derived) $ do
      printMsg "Derived constraints not empty:"
      printObj derived
    if not $ null wanted
      then do
        printMsg "SOLVE..."
        polymonadSolve' s
      else return noResult
  case res of
    Left errMsg -> do
      tcPluginIO $ putStrLn errMsg
      return noResult
    Right solve -> return solve

polymonadSolve' :: PolymonadState -> PmPluginM TcPluginResult
polymonadSolve' _s = do
  --printMsg "Given constraints:"
  --printObj given
  --printMsg "Wanted constraints:"
  --printObj wanted
  --printMsg "Selected Polymonad:"
  --printObj =<< getCurrentPolymonad
  -- Simplification ------------------------------------------------------------
  printMsg "Try simplification of constraints..."
  wanted <- getWantedPolymonadConstraints
  let (wantedApplied, wantedIncomplete) = partition isFullyAppliedClassConstraint wanted

  -- First, if we have any constraint that does not contain type variables,
  -- we are allowed to just pick an applicable instance, since we are talking
  -- about polymonads.
  --printMsg "Solve wanted completes:"
  --printObj wantedApplied
  wantedEvidence <- catMaybes <$> mapM pickInstanceForAppliedConstraint wantedApplied
  --printObj wantedEvidence

  -- Second, we have to look at those constraints that are not yet fully applied.
  -- We can now try to simplify these constraints using the S-Up and S-Down rules.
  --printMsg "Solve wanted incompletes:"
  --printObj wantedIncomplete
  let ambTvs = S.unions $ constraintTopAmbiguousTyVars <$> wantedIncomplete
  eqUpDownCtData <- simplifyAllUpDown wantedIncomplete ambTvs
  let eqUpDownCts = simplifiedTvsToConstraints eqUpDownCtData
  --printObj eqUpDownCts
  -- Calculate type variables that still require solving and then
  -- try to solve them using the S-Join rule.
  let ambTvs' = ambTvs S.\\ S.fromList (fmap fst eqUpDownCtData)
  eqJoinCts <- simplifiedTvsToConstraints <$> simplifyAllJoin wantedIncomplete ambTvs'
  --printObj eqJoinCts

  -- Lets see if we made progress through simplification or if we need to
  -- move on to actually trying to solve things.
  if null wantedEvidence && null eqUpDownCts && null eqJoinCts then do
    printMsg "Simplification could not solve all constraints."
    printMsg "Moving on to solving..."
    let ctGraph = mkGraphView wanted
    if isAllUnambigious ctGraph then do
      printMsg "Constraint graph is unambigious proceed with solving..."
      wantedCts <- getWantedPolymonadConstraints
      printMsg "Constraints to solve:"
      printObj wantedCts
      derivedSolution <- solve wantedCts
      printMsg "Derived solutions:"
      printObj derivedSolution
      return $ TcPluginOk [] derivedSolution
    else do
      printMsg "Constraint graph is ambigious, unable to solve polymonad constraints..."
      return noResult
  else do
    printMsg "Simplification made progress. Not solving."
    return $ TcPluginOk wantedEvidence (eqUpDownCts ++ eqJoinCts)

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

mkEqCtsFromSubst :: Ct -> TvSubst -> PmPluginM [Ct]
mkEqCtsFromSubst wantedCt subst = do
  printMsg "=== mkEqCtsFromSubst ==="
  let wantedCtTy = ctPred wantedCt
  case isClassPred wantedCtTy of
    False -> do
      printMsg "=== No class pred"
      printObj wantedCtTy
      return []
    True -> do
      printMsg "=== Gen Eq for class"
      printObj wantedCtTy
      let (_vars, _, _cls, tyParams) = tcSplitDFunTy wantedCtTy
      let vars = catMaybes $ fmap tcGetTyVar_maybe tyParams
      printObj $ vars
      let inScopeVars = filter (\v -> not $ notElemTvSubst v subst) vars
      printObj inScopeVars
      flip mapM inScopeVars $ \var -> do -- type variables in
        return $ mkDerivedTypeEqCt wantedCt var (substTyVar subst var)

noResult :: TcPluginResult
noResult = TcPluginOk [] []

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
