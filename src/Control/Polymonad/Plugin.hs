-- | Provides the polymonad plugin for GHC.
module Control.Polymonad.Plugin
  ( plugin ) where

import Data.List ( partition )
import Data.Maybe ( catMaybes )
import qualified Data.Set as S

import Control.Monad ( unless, forM )

import Plugins ( Plugin(tcPlugin), defaultPlugin )
import TcRnTypes
  ( Ct(..)
  , TcPlugin(..), TcPluginResult(..) )
import TcPluginM ( TcPluginM, tcPluginIO )
import TcEvidence ( EvTerm )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runPmPlugin
  , getWantedPolymonadConstraints, getGivenPolymonadConstraints
  , printDebug, printMsg
  --, printObj
  , printConstraints )
import Control.Polymonad.Plugin.Constraint
  ( constraintTopAmbiguousTyVars
  , isTyConAppliedClassConstraint
  , mkDerivedTypeEqCt )
import Control.Polymonad.Plugin.GraphView
  ( mkGraphView )
import Control.Polymonad.Plugin.Solve
  ( solve )
import Control.Polymonad.Plugin.Ambiguity
  ( isAllUnambiguous )
import Control.Polymonad.Plugin.Simplification
  ( simplifyAllUpDown, simplifyAllJoin
  , simplifiedTvsToConstraints )
import Control.Polymonad.Plugin.Core
  ( trySolveAmbiguousForAppliedTyConConstraint
  , detectOverlappingInstancesAndTrySolve )
import qualified Control.Polymonad.Plugin.Log as L
import qualified Control.Polymonad.Plugin.Debug as D

-- -----------------------------------------------------------------------------
-- The Plugin
-- -----------------------------------------------------------------------------

-- | The polymonad type checker plugin for GHC.
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \_clOpts -> Just polymonadPlugin }

-- -----------------------------------------------------------------------------
-- Static Flags
-- -----------------------------------------------------------------------------

-- | Enable solving of ambiguous indices in concrete type constructors
--   through unification with available instances. This only applies
--   if all type constructor of a constraint are not variable and there
--   is only one matching instance.
--
--   See 'trySolveAmbiguousForAppliedTyConConstraint' for what is done.
enableUnificationIndexSolving :: Bool
enableUnificationIndexSolving = True

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
  res <- runPmPlugin (given ++ derived) wanted $
    if not $ null wanted
      then do
        printMsg "Invoke polymonad plugin..."
        polymonadSolve' s
      else return noResult
  case res of
    Left errMsg -> do
      tcPluginIO $ putStrLn errMsg
      return noResult
    Right slv -> do
      --L.printObj $ any D.hasEvTermPattern $ getEvidence $ mergeResults slv
      return $ mergeResults slv

polymonadSolve' :: PolymonadState -> PmPluginM TcPluginResult
polymonadSolve' _s = do
  printDebug "Given constraints:"
  printConstraints True =<< getGivenPolymonadConstraints
  printDebug "Wanted constraints:"
  printConstraints True =<< getWantedPolymonadConstraints
  --printDebug "Selected Polymonad:"
  --printConstraints True =<< getCurrentPolymonad

  -- Derive Constraints --------------------------------------------------------
  -- Deriving constraints is ignored for now, because for some reason GHCs
  -- constraint solver throws some of the derived constraints away and says
  -- there are overlapping instances for them (which does not make sense?).
  -- This only makes definitions easier, since the programmer does not have
  -- to list all of the constraints necessary, but is not essential for the
  -- plugin.
  {-
  derivedPmCts <- derivePolymonadConstraints
  if not $ null derivedPmCts
    then do
      printMsg "Derived new polymonad constraints:"
      printObj derivedPmCts
      return $ TcPluginOk [] derivedPmCts
    else do
  -}

  -- Simplification ------------------------------------------------------------
  printDebug "Try simplification of constraints..."
  allWanted <- getWantedPolymonadConstraints
  --printObj allWanted
  -- Try to solve ambiguous indices in polymonad constraints that contain
  -- concrete type constructors, but still miss a solution for some of their
  -- indices. This should be valid as long as the possible solutions are unique,
  -- because we just narrow down the specific type constructor we actually want.
  -- FIXME: This should be done within the solver in addition to determining
  -- the concrete type constructor.
  let (tyConAppCts, wanted) = if enableUnificationIndexSolving
        then partition isTyConAppliedClassConstraint allWanted
        else ([], allWanted)
  solvedAmbIndices <- if enableUnificationIndexSolving
    then fmap concat $ forM tyConAppCts $ \tyConAppCt -> do
      mRes <- trySolveAmbiguousForAppliedTyConConstraint tyConAppCt
      case mRes of
        Just res@(_:_) -> return $ uncurry (mkDerivedTypeEqCt tyConAppCt) <$> res
        -- If there is no unfication to solve
        _ -> return []
    else return []

  -- If there are several instances that overlap for a already solved constraint
  -- and the constraint is free of ambiguous variables, we can check if only
  -- one of those instances actually instantiated the constraint. That
  -- means, for each of those overlapping instances we check if the super
  -- class constraints hold and if that is only the case for one of them,
  -- we provice evidence to pick that instance.
  solvedOverlaps <- if null solvedAmbIndices
    then fmap catMaybes $ forM tyConAppCts $ \tyConAppCt -> do
      mEv <- detectOverlappingInstancesAndTrySolve tyConAppCt
      return $ (\ev -> (ev, tyConAppCt)) <$> mEv
    else return []

  -- We can now try to simplify constraints using the S-Up and S-Down rules.
  let ambTvs = S.unions $ constraintTopAmbiguousTyVars <$> wanted
  eqUpDownCtData <- simplifyAllUpDown wanted ambTvs
  let eqUpDownCts = simplifiedTvsToConstraints eqUpDownCtData

  -- Calculate type variables that still require solving and then
  -- try to solve them using the S-Join rule.
  let ambTvs' = ambTvs S.\\ S.fromList (fmap fst eqUpDownCtData)
  eqJoinCts <- simplifiedTvsToConstraints <$> simplifyAllJoin wanted ambTvs'

  -- Lets see if we made progress through simplification or if we need to
  -- move on to actually trying to solve things.
  -- Note: It seems that non-empty evidence and empty derived constraints
  -- leads the constraint solver to stop asking for further help, though there
  -- still is ambiguity. Therefore we ignore the wanted evidence in this test
  -- and always deliver it.
  if null eqUpDownCts && null eqJoinCts && null solvedAmbIndices then do
    printDebug "Simplification could not solve all constraints. Solving..."
    let ctGraph = mkGraphView wanted
    if isAllUnambiguous ctGraph then do
      printDebug "Constraint graph is unambiguous proceed with solving..."
      wantedCts <- getWantedPolymonadConstraints
      derivedSolution <- solve wantedCts
      unless (null derivedSolution) $ do
        printDebug "Derived solutions:"
        printConstraints True derivedSolution
      --return $ TcPluginOk [] derivedSolution
      return $ TcPluginOk solvedOverlaps derivedSolution
    else do
      printDebug "Constraint graph is ambiguous, unable to solve polymonad constraints..."
      --return noResult
      return $ TcPluginOk solvedOverlaps []
  else do
    printDebug "Simplification made progress. Not solving."
    --printObj solvedAmbIndices
    --printObj solvedOverlaps
    --printObj eqUpDownCts
    --printObj eqJoinCts
    return $ TcPluginOk solvedOverlaps (eqUpDownCts ++ eqJoinCts ++ solvedAmbIndices)

-- -----------------------------------------------------------------------------
-- Utility Functions
-- -----------------------------------------------------------------------------

noResult :: TcPluginResult
noResult = TcPluginOk [] []

mergeResults :: [TcPluginResult] -> TcPluginResult
mergeResults [] = noResult
mergeResults (TcPluginOk evidence derived : rest) = case mergeResults rest of
  TcPluginOk restEv restDe -> TcPluginOk (evidence ++ restEv) (derived ++ restDe)
  TcPluginContradiction cts -> TcPluginContradiction cts
mergeResults (TcPluginContradiction cts : _) = TcPluginContradiction cts

getEvidence :: TcPluginResult -> [EvTerm]
getEvidence (TcPluginOk evs _dc) = fmap fst evs
getEvidence _ = []



