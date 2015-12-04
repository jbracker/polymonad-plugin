 
module MinimalPlugin ( plugin ) where

import Data.List ( partition )
import Data.Maybe ( catMaybes, listToMaybe )
import qualified Data.Set as S

import Control.Monad ( unless, forM, liftM )

import Type ( TyThing(..) )
import Plugins ( Plugin(tcPlugin), defaultPlugin )
import InstEnv
  ( ClsInst(..)
  , instEnvElts, ie_global )
import Class
  ( Class(..)
  , className, classArity )
import TyCon ( TyCon )
import RdrName ( GlobalRdrElt(..), lookupGlobalRdrEnv )
import OccName ( occNameString, mkTcOcc )
import Name ( getOccName )
import TcRnTypes
  ( Ct(..)
  , TcGblEnv(..), TcTyThing(..)
  , TcPlugin(..), TcPluginResult(..) )
import TcPluginM 
  ( TcPluginM
  , tcPluginIO, tcLookup
  , getEnvs, getInstEnvs )
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
polymonadSolve _s _g _d [] = return $ TcPluginOk [] []
polymonadSolve s given derived wanted = do
  mPmCls <- findPolymonadClass
  mIdTyCon <- findIdentityTyCon
  case (mPmCls, mIdTyCon) of
    (Just pmCls, Just idTyCon) -> do
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
          let mergedRes = mergeResults slv
          case mergedRes of
            TcPluginOk solved derive -> do
              L.printObj wanted
              L.printObj derive
              L.printObj $ fmap snd solved
          return $ mergedRes
    r -> do
      L.printMsg "ERROR: Could not find polymonad class or id tycon."
      L.printObj r
      return noResult

polymonadSolve' :: PolymonadState -> PmPluginM TcPluginResult
polymonadSolve' _s = do
  -- Simplification ------------------------------------------------------------
  printDebug "Try simplification of constraints..."
  allWanted <- getWantedPolymonadConstraints
  
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
  
  solvedOverlaps <- if null solvedAmbIndices
    then fmap catMaybes $ forM tyConAppCts $ \tyConAppCt -> do
      mEv <- detectOverlappingInstancesAndTrySolve tyConAppCt
      return $ (\ev -> (ev, tyConAppCt)) <$> mEv
    else return []
  
  let ambTvs = S.unions $ constraintTopAmbiguousTyVars <$> wanted
  eqUpDownCtData <- simplifyAllUpDown wanted ambTvs
  let eqUpDownCts = simplifiedTvsToConstraints eqUpDownCtData
  
  let ambTvs' = ambTvs S.\\ S.fromList (fmap fst eqUpDownCtData)
  eqJoinCts <- simplifiedTvsToConstraints <$> simplifyAllJoin wanted ambTvs'
  
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
      return $ TcPluginOk solvedOverlaps derivedSolution
    else do
      printDebug "Constraint graph is ambiguous, unable to solve polymonad constraints..."
      return $ TcPluginOk solvedOverlaps []
  else do
    printDebug "Simplification made progress. Not solving."
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

-- -----------------------------------------------------------------------------
-- Detection
-- -----------------------------------------------------------------------------

polymonadClassName :: String
polymonadClassName = "Polymonad"

identityTyConName :: String
identityTyConName = "Identity"

isPolymonadClass :: Class -> Bool
isPolymonadClass cls 
  =  (occNameString $ getOccName $ className cls) == polymonadClassName
  && classArity cls == 3

findPolymonadClass :: TcPluginM (Maybe Class)
findPolymonadClass = do
  let isPmCls = isPolymonadClass . is_cls
  envs <- fst <$> getEnvs
  let foundInstsLcl =  (filter isPmCls . instEnvElts . tcg_inst_env $ envs)
                    ++ (filter isPmCls . tcg_insts $ envs)
  foundInstsGbl <- filter isPmCls . instEnvElts . ie_global <$> getInstEnvs
  return $ case foundInstsLcl ++ foundInstsGbl of
    (inst : _) -> Just $ is_cls inst
    [] -> Nothing

findIdentityTyCon :: TcPluginM (Maybe TyCon)
findIdentityTyCon = do
  let idOccName = mkTcOcc identityTyConName
  rdrEnv <- tcg_rdr_env . fst <$> getEnvs
  let envResultElem = lookupGlobalRdrEnv rdrEnv idOccName
  mTyCons <- forM envResultElem $ liftM tcTyThingToTyCon . tcLookup . gre_name
  return $ listToMaybe $ catMaybes mTyCons

tcTyThingToTyCon :: TcTyThing -> Maybe TyCon
tcTyThingToTyCon (AGlobal (ATyCon tc)) = Just tc
tcTyThingToTyCon _ = Nothing



  