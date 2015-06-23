
-- | Functions and utilities to work with and inspect constraints
--   of the GHC API.
module Control.Polymonad.Plugin.Constraint
  ( isClassConstraint
  , constraintTyParams
  , constraintClassTyCon
  , constraintTyCons
  , constraintTcVars
  ) where

import Data.Set ( Set )

import TcRnTypes
  ( Ct(..), CtEvidence(..)
  , isCDictCan_Maybe
  , isWantedCt
  , ctev_pred )
import Class ( Class(..) )
import Type 
  ( Type, TyVar
  , splitTyConApp_maybe
  )
import TyCon ( TyCon )

import Control.Polymonad.Plugin.Utils
  ( missingCaseError
  , collectTopTyCons
  , collectTopTcVars )

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct = 
  case isCDictCan_Maybe ct of
    Just cls -> cls == wantedClass && isWantedCt ct
    Nothing -> False

-- | Retrieves the arguments of the given type class constraints.
--   Unclear what happens if the given evidence does not contain a type 
--   application.
constraintEvidenceTyParams :: CtEvidence -> [Type]
constraintEvidenceTyParams evdnc = case splitTyConApp_maybe $ ctev_pred evdnc of
  Just (_tc, args) -> args
  Nothing -> missingCaseError "constraintEvidenceTyParams" $ Just (ctev_pred evdnc)

-- | Retrieves the arguments of the given constraints.
--   Only works if the constraint is a type class constraint.
--   Emits and error in case the constraint is not supported.
constraintTyParams :: Ct -> [Type]
constraintTyParams ct = case ct of
  CDictCan _ _ _ -> cc_tyargs ct
  CNonCanonical evdnc -> constraintEvidenceTyParams evdnc
  v -> missingCaseError "constraintTyParams" $ Just v

-- | Retrieves the type constructor of the given type class constraint.
--   Only works if the constraint is a type class constraint.
--   Emits and error in case the constraint is not supported.
constraintClassTyCon :: Ct -> TyCon
constraintClassTyCon ct = case ct of
  CDictCan _ _ _ -> classTyCon (cc_class ct)
  CNonCanonical evdnc -> constraintEvidenceClassTyCon evdnc
  v -> missingCaseError "constraintTyCon" $ Just v

-- | Retrieves the type constructor of the given type class constraints.
--   Only works if the constraint is a type class constraint.
--   Emits and error in case the constraint is not supported.
constraintEvidenceClassTyCon :: CtEvidence -> TyCon
constraintEvidenceClassTyCon evdnc = case splitTyConApp_maybe $ ctev_pred evdnc of
  Just (tc, _args) -> tc
  Nothing -> missingCaseError "constraintEvidenceClassTyCon" $ Just (ctev_pred evdnc)

-- | Collects the type constructors in the arguments of the constraint. 
--   Only works if the given constraint is a type class constraint. 
--   Only collects those on the top level (See 'collectTopTyCons').
constraintTyCons :: Ct -> Set TyCon
constraintTyCons ct = collectTopTyCons $ constraintTyParams ct
  
-- | Collects the type variables in the arguments of the constraint. 
--   Only works if the given constraint is a type class constraint.
--   Only collects those on the top level (See 'collectTopTcVars').
constraintTcVars :: Ct -> Set TyVar
constraintTcVars ct = collectTopTcVars $ constraintTyParams ct