
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
  , eqType
  , getClassPredTys_maybe
  , getEqPredTys_maybe
  , splitTyConApp_maybe )
import TyCon ( isTupleTyCon )
import InstEnv
  ( ClsInst(..)
  , instanceSig
  , lookupUniqueInstEnv, lookupInstEnv
  , classInstances )
import TcEvidence ( EvTerm(..), TcCoercion(..) )
import TcPluginM
  ( TcPluginM
  , getInstEnvs )
import Outputable ( showSDocUnsafe )

import Control.Polymonad.Plugin.Log ( printObj, printMsg )
import Control.Polymonad.Plugin.Evaluate ( evaluateType )

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
  -- Global instance environment.
  instEnvs <- getInstEnvs
  -- Substitute all variables for their actual values, evaluate their
  -- contained synonyms and families and finally flatten tuples of constraints.
  normInstCts <- flattenTuples <$> forM (substTys varSubst instCts) (\x -> snd <$> evaluateType x)
  -- Now go over each constraint and find a suitable instance and evidence.
  ctEvTerms <- forM normInstCts $ \normInstCt ->
    case getClassPredTys_maybe normInstCt of
      -- Do we have a class constraint?
      Just (ctCls, ctArgs) -> do
        -- Substitute the variables to know what instance we are looking for.
        let substArgs = substTys varSubst ctArgs
        -- Look for suitable instance. Since we are not necessarily working
        -- with polymonads anymore we need to find a unique one.
        case lookupUniqueInstEnv instEnvs ctCls substArgs of
          -- No instance found, too bad...
          Left err -> do
            printMsg "Can't produce evidence for this class constraint:"
            printObj normInstCt
            printMsg "Lookup error:"
            printMsg $ showSDocUnsafe err
            return Nothing
          -- We found one: Now we can produce evidence for the found instance.
          Right (clsInst, instArgs) -> produceEvidenceFor clsInst instArgs
      -- We do not have a class constraint...
      Nothing ->
        case getEqPredTys_maybe normInstCt of
          -- Do we have a type equality constraint?
          Just (r, ta, tb) -> do
            -- FIXME: No idea what the role does. Lets hope for the best.
            let isEq = eqType ta tb
            if isEq
              then
                return $ Just $ EvCoercion $ TcRefl r normInstCt
              else do
                printMsg "Can't produce evidence for this type equality constraint:"
                printObj normInstCt
                return Nothing
          -- We do not have a type equality constraint either...
          Nothing -> do
            printMsg "Can't produce evidence for this constraint:"
            printObj normInstCt
            return Nothing
  -- If we found a good instance and evidence for every constraint,
  -- we can create the evidence for this instance.
  return $ if any isNothing ctEvTerms
    then Nothing
    else Just $ EvDFunApp (is_dfun inst) tys (fromJust <$> ctEvTerms)

{-

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
-}

flattenTuples :: [Type] -> [Type]
flattenTuples [] = []
flattenTuples (t : ts) = case splitTyConApp_maybe t of
  Just (tc, tcArgs) -> if isTupleTyCon tc
    then flattenTuples tcArgs ++ flattenTuples ts
    else t : flattenTuples ts
  Nothing -> t : flattenTuples ts
