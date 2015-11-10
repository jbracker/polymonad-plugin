
module Control.Polymonad.Plugin.Evidence
  ( produceEvidenceFor
  ) where

import Data.Either ( isLeft )
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
import Outputable ( ($$) )
import qualified Outputable as O

import Control.Polymonad.Plugin.Evaluate ( evaluateType )
import Control.Polymonad.Plugin.Constraint ( GivenCt )
import Control.Polymonad.Plugin.Utils ( fromLeft, fromRight )

-- | Apply the given instance dictionary to the given type arguments
--   and try to produce evidence for the application.
--
--   The list of types has to match the number of open variables of the
--   given instance dictionary in length. They need to match up with
--   the list of free type variables given for the class instance ('is_tvs').
--   The list can be created using 'matchInstanceTyVars'.
--
--   The first argument is a list of given constraints that can be used
--   to produce evidence for otherwise not fulfilled constraints. Be aware that
--   only actually /given/ constraints (as in 'isGivenCt') are useful here,
--   because only those produce evidence for themselves. All other constraints
--   will be ignored.
produceEvidenceFor :: [GivenCt] -> ClsInst -> [Type] -> TcPluginM (Either O.SDoc EvTerm)
produceEvidenceFor givenCts inst tys = do
  -- Get the instance type variables and constraints (by that we know the
  -- number of type arguments and dictionart arguments for the EvDFunApp)
  let (tyVars, instCts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
  -- How the instance variables for the current instance are bound.
  let varSubst = mkTopTvSubst $ zip tyVars tys
  -- Now go over each constraint and find a suitable instance and evidence.
  -- Don't forget to substitute all variables for their actual values,
  ctEvTerms <- forM (substTys varSubst instCts) $ produceEvidenceForCt givenCts
  -- If we found a good instance and evidence for every constraint,
  -- we can create the evidence for this instance.
  return $ if any isLeft ctEvTerms
    then Left
      $ O.text "Can't produce evidence for instance:"
      $$ O.ppr inst
      $$ O.text "Reason:"
      $$ O.vcat (fromLeft <$> filter isLeft ctEvTerms)
    else Right $ EvDFunApp (is_dfun inst) tys (fromRight <$> ctEvTerms)

produceEvidenceForCt :: [GivenCt] -> Type -> TcPluginM (Either O.SDoc EvTerm)
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
        Left err ->
          return $ Left
            $ O.text "Can't produce evidence for this class constraint:"
            $$ O.ppr normCt
            $$ O.text "Lookup error:"
            $$ err
        -- We found one: Now we can produce evidence for the found instance.
        Right (clsInst, instArgs) -> produceEvidenceFor checkedGivenCts clsInst instArgs
    -- We do not have a class constraint...
    Nothing ->
      case getEqPredTys_maybe normCt of
        -- Do we have a type equality constraint?
        Just (r, ta, tb) ->
          -- We only do the simplest kind of equality constraint solving and
          -- evidence construction.
          if eqType ta tb
            then
              return $ Right $ EvCoercion $ TcRefl r normCt
            else
              return $ Left
                $ O.text "Can't produce evidence for this type equality constraint:"
                $$ O.ppr normCt
        -- We do not have a type equality constraint either...
        Nothing ->
          case splitTyConApp_maybe normCt of
            -- Do we have a tuple of constraints? (Probably resulting from evaluation)
            Just (tc, tcArgs) | isTupleTyCon tc -> do
              -- Produce evidence for each element of the tuple
              tupleEvs <- forM tcArgs $ produceEvidenceForCt checkedGivenCts
              return $ if any isLeft tupleEvs
                then Left
                  $ O.text "Can't find evidence for this tuple constraint:"
                  $$ O.ppr normCt
                  $$ O.text "Reason:"
                  $$ O.vcat (fromLeft <$> filter isLeft tupleEvs)
                -- And put together evidence for the complete tuple.
                else Right $ EvTupleMk $ fmap fromRight tupleEvs
            -- We don't have a tuple constraint...
            _ -> case find (eqType normCt . ctPred) checkedGivenCts of
              -- Check if there is some given constraint that provides evidence
              -- for our constraint.
              Just foundGivenCt ->
                return $ Right $ ctEvTerm (ctEvidence foundGivenCt)
              -- Nothing delivered a result, give up...
              Nothing ->
                return $ Left
                  $ O.text "Can't produce evidence for this constraint:"
                  $$ O.ppr normCt
  -- Finally we have to coerce the found evidence according to the coercion
  -- that resulted from evaluating the evidence.
  let coerEv :: EvTerm -> EvTerm
      coerEv ev = EvCast ev (TcCoercion ctCoercion)
  return $ coerEv <$> mEvTerm
