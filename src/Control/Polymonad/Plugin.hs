-- | Provides the polymonad plugin for GHC.
module Control.Polymonad.Plugin
  ( plugin ) where

import Data.Maybe ( catMaybes )
import Data.List ( partition, intercalate )
--import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( unless )

--import Debug.Trace ( trace )

import Plugins ( Plugin(tcPlugin), defaultPlugin )
import TcRnTypes
  ( Ct(..)
  , TcPlugin(..), TcPluginResult(..) )
import TcPluginM ( TcPluginM, tcPluginIO )

import Control.Polymonad.Plugin.Log ( groupFormatSrcSpans )
import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runPmPlugin
  , getWantedPolymonadConstraints, getGivenPolymonadConstraints
  , printMsg, printObj )
import Control.Polymonad.Plugin.Constraint
  ( isFullyAppliedClassConstraint
  , constraintTopAmbiguousTyVars
  , constraintSourceLocation )
import Control.Polymonad.Plugin.Core
  ( pickInstanceForAppliedConstraint )
import Control.Polymonad.Plugin.GraphView
  ( mkGraphView )
import Control.Polymonad.Plugin.Solve
  ( solve )
import Control.Polymonad.Plugin.Ambiguity
  ( isAllUnambiguous )
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
    Right slv -> return slv

polymonadSolve' :: PolymonadState -> PmPluginM TcPluginResult
polymonadSolve' _s = do
  --printMsg "Given constraints:"
  --printObj =<< getGivenPolymonadConstraints
  --printMsg "Wanted constraints:"
  --printObj =<< getWantedPolymonadConstraints
  --printMsg "Selected Polymonad:"
  --printObj =<< getCurrentPolymonad
  -- Simplification ------------------------------------------------------------
  printMsg "Try simplification of constraints..."
  wanted <- getWantedPolymonadConstraints
  printMsg $ "Wanted constraints from: " ++ (groupFormatSrcSpans . fmap constraintSourceLocation $ wanted)
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
  -- Note: It seems that non-empty evidence and empty derived constraints
  -- leads the constraint solver to stop asking for further help, though there
  -- still is ambiguity. Therefore we ignore the wanted evidence in this test
  -- and always deliver it.
  if null eqUpDownCts && null eqJoinCts then do
    printMsg "Simplification could not solve all constraints. Solving..."
    let ctGraph = mkGraphView wanted
    if isAllUnambiguous ctGraph then do
      printMsg "Constraint graph is unambiguous proceed with solving..."
      wantedCts <- getWantedPolymonadConstraints
      derivedSolution <- solve wantedCts
      unless (null derivedSolution) $ do
        printMsg "Derived solutions:"
        printObj derivedSolution
      return $ TcPluginOk wantedEvidence derivedSolution
    else do
      printMsg "Constraint graph is ambiguous, unable to solve polymonad constraints..."
      return $ TcPluginOk wantedEvidence []
  else do
    printMsg "Simplification made progress. Not solving."
    --printObj $ wantedEvidence
    --printObj $ eqUpDownCts ++ eqJoinCts
    return $ TcPluginOk wantedEvidence (eqUpDownCts ++ eqJoinCts)

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

noResult :: TcPluginResult
noResult = TcPluginOk [] []

{-
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
-}

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
