
module Control.Polymonad.Plugin.Evidence
  ( produceEvidenceFor
  ) where

import Data.Maybe
  ( isNothing, fromJust )
import Data.List ( find )

import Control.Monad ( forM )

import Type
  ( Type
  , mkTopTvSubst, substTys
  , eqType
  , getClassPredTys_maybe
  , getEqPredTys_maybe
  , splitTyConApp_maybe )
import TyCon ( isTupleTyCon )
import InstEnv
  ( ClsInst(..)
  , instanceSig
  , lookupUniqueInstEnv )
import TcRnTypes ( isGivenCt, ctPred, ctEvidence, ctEvTerm )
import TcEvidence ( EvTerm(..), TcCoercion(..) )
import TcPluginM
  ( TcPluginM
  , getInstEnvs )
import Outputable ( showSDocUnsafe )

import Control.Polymonad.Plugin.Log
  ( printMsg, printObj )
import Control.Polymonad.Plugin.Evaluate ( evaluateType )
import Control.Polymonad.Plugin.Constraint ( GivenCt )

-- | Apply the given instance dictionary to the given type arguments
--   and try to produce evidence for the application.
--   The list of types has to match the number of open variables of the
--   given instance dictionary in length.
produceEvidenceFor :: ClsInst -> [Type] -> TcPluginM (Maybe EvTerm)
produceEvidenceFor inst tys = do
  -- Get the instance type variables and constraints (by that we know the
  -- number of type arguments and dictionart arguments for the EvDFunApp)
  let (tyVars, instCts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
  -- How the instance variables for the current instance are bound.
  let varSubst = mkTopTvSubst $ zip tyVars tys
  -- Now go over each constraint and find a suitable instance and evidence.
  -- Don't forget to substitute all variables for their actual values,
  ctEvTerms <- forM (substTys varSubst instCts) $ produceEvidenceForCt []
  -- If we found a good instance and evidence for every constraint,
  -- we can create the evidence for this instance.
  return $ if any isNothing ctEvTerms
    then Nothing
    else Just $ EvDFunApp (is_dfun inst) tys (fromJust <$> ctEvTerms)

produceEvidenceForCt :: [GivenCt] -> Type -> TcPluginM (Maybe EvTerm)
produceEvidenceForCt givenCts ct = do
  let checkedGivenCts = filter isGivenCt givenCts
  -- Evaluate their contained synonyms and families.
  (ctCoercion, normCt) <- evaluateType ct
  mEvTerm <- case getClassPredTys_maybe normCt of
    -- Do we have a class constraint?
    Just (ctCls, ctArgs) -> do
      -- Global instance environment.
      instEnvs <- getInstEnvs
      -- Look for suitable instance. Since we are not necessarily working
      -- with polymonads anymore we need to find a unique one.
      case lookupUniqueInstEnv instEnvs ctCls ctArgs of
        -- No instance found, too bad...
        Left err -> do
          printMsg "Can't produce evidence for this class constraint:"
          printObj normCt
          printMsg "Lookup error:"
          printMsg $ showSDocUnsafe err
          return Nothing
        -- We found one: Now we can produce evidence for the found instance.
        Right (clsInst, instArgs) -> produceEvidenceFor clsInst instArgs
    -- We do not have a class constraint...
    Nothing ->
      case getEqPredTys_maybe normCt of
        -- Do we have a type equality constraint?
        Just (r, ta, tb) -> do
          -- We only do the simplest kind of equality constraint solving and
          -- evidence construction.
          if eqType ta tb
            then
              return $ Just $ EvCoercion $ TcRefl r normCt
            else do
              printMsg "Can't produce evidence for this type equality constraint:"
              printObj normCt
              return Nothing
        -- We do not have a type equality constraint either...
        Nothing ->
          case splitTyConApp_maybe normCt of
            -- Do we have a tuple of constraints? (Probably resulting from evaluation)
            Just (tc, tcArgs) | isTupleTyCon tc -> do
              -- Produce evidence for each element of the tuple
              tupleEvs <- forM tcArgs $ produceEvidenceForCt checkedGivenCts
              return $ if any isNothing tupleEvs
                then Nothing
                -- And put together evidence for the complete tuple.
                else Just $ EvTupleMk $ fmap fromJust tupleEvs
            -- We don't have a tuple constraint...
            _ -> case find (eqType normCt . ctPred) checkedGivenCts of
              -- Check if there is some given constraint that provides evidence
              -- for our constraint.
              Just foundGivenCt ->
                return $ Just $ ctEvTerm (ctEvidence foundGivenCt)
              -- Nothing delivered a result, give up...
              Nothing -> do
                printMsg "Can't produce evidence for this constraint:"
                printObj normCt
                return Nothing
  -- Finally we have to coerce the found evidence according to the coercion
  -- that resulted from evaluating the evidence.
  let coerEv :: EvTerm -> EvTerm
      coerEv ev = EvCast ev (TcCoercion ctCoercion)
  return $ coerEv <$> mEvTerm
