
module Control.Polymonad.Plugin.Evidence
  ( produceEvidenceFor
  ) where

import Data.Maybe
  ( catMaybes
  , isNothing, fromJust )

import Control.Monad ( forM )

import Type
  ( Type
  , mkTopTvSubst, substTys
  , getClassPredTys_maybe )
import InstEnv
  ( ClsInst(..)
  , instanceSig
  , lookupUniqueInstEnv )
import TcEvidence ( EvTerm(..) )
import TcPluginM
  ( TcPluginM
  , getInstEnvs )

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
