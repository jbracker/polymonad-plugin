
-- | Functions and utilities to work with and inspect constraints
--   of the GHC API.
module Control.Polymonad.Plugin.Constraint
  ( -- * Constraint Creation
    mkDerivedTypeEqCt
  , mkDerivedTypeEqCt'
    -- * Constraint inspection
  , isClassConstraint
  , constraintClassType
  , constraintClassTyArgs
  , constraintClassTyCon
  , constraintTyCons
  , constraintTcVars
  , findConstraintTopTyCons
  ) where

import Data.Set ( Set )
import qualified Data.Set as S

import TcRnTypes
  ( Ct(..), CtLoc, CtEvidence(..)
  , isCDictCan_Maybe
  , isWantedCt
  , ctev_pred
  , mkNonCanonical )
import Class ( Class(..) )
import Type
  ( Type, TyVar
  , splitTyConApp_maybe
  , mkTyVarTy
  )
import TyCon ( TyCon )
import TcPluginM
import TcType ( mkTcEqPred )

import Control.Polymonad.Plugin.Utils
  ( collectTopTyCons
  , collectTopTcVars
  , findConstraintOrInstanceTyCons )

-- -----------------------------------------------------------------------------
-- Constraint Creation
-- -----------------------------------------------------------------------------

mkDerivedTypeEqCt :: Ct -> TyVar -> Type -> Ct
mkDerivedTypeEqCt ct = mkDerivedTypeEqCt' (constraintLocation ct)

mkDerivedTypeEqCt' :: CtLoc -> TyVar -> Type -> Ct
mkDerivedTypeEqCt' loc tv ty = mkNonCanonical CtDerived
  { ctev_pred = mkTcEqPred (mkTyVarTy tv) ty
  , ctev_loc = loc }

-- -----------------------------------------------------------------------------
-- Constraint Inspection
-- -----------------------------------------------------------------------------

-- | Check if the given constraint is a class constraint of the given class.
isClassConstraint :: Class -> Ct -> Bool
isClassConstraint wantedClass ct =
  case isCDictCan_Maybe ct of
    Just cls -> cls == wantedClass && isWantedCt ct
    Nothing -> False

-- | Retrieves the type constructor and type arguments of the given
--   type class constraint.
--   Only works if the constraint is a type class constraint, otherwise
--   returns 'Nothing'.
constraintClassType :: Ct -> Maybe (TyCon, [Type])
constraintClassType ct = case ct of
  CDictCan {} -> Just (classTyCon (cc_class ct), cc_tyargs ct)
  CNonCanonical evdnc -> splitTyConApp_maybe $ ctev_pred evdnc
  _ -> Nothing

-- | Retrieves the arguments of the given constraints.
--   See 'constraintClassType'.
constraintClassTyArgs :: Ct -> Maybe [Type]
constraintClassTyArgs = fmap snd . constraintClassType


-- | Retrieves the type constructor of the given type class constraint.
--   See 'constraintClassType'.
constraintClassTyCon :: Ct -> Maybe TyCon
constraintClassTyCon = fmap fst . constraintClassType

-- | Collects the type constructors in the arguments of the constraint.
--   Only works if the given constraint is a type class constraint.
--   Only collects those on the top level (See 'collectTopTyCons').
constraintTyCons :: Ct -> Set TyCon
constraintTyCons ct = maybe S.empty collectTopTyCons $ constraintClassTyArgs ct

-- | Collects the type variables in the arguments of the constraint.
--   Only works if the given constraint is a type class constraint.
--   Only collects those on the top level (See 'collectTopTcVars').
constraintTcVars :: Ct -> Set TyVar
constraintTcVars ct = maybe S.empty collectTopTcVars $ constraintClassTyArgs ct

-- | Search for all possible type constructors that could be
--   used in the top-level position of the constraint arguments.
--   Delivers a set of type constructors.
findConstraintTopTyCons :: Ct -> TcPluginM (Set TyCon)
findConstraintTopTyCons ct = case constraintClassType ct of
  Just (tyCon, tyArgs) -> do
    let tcs = constraintTyCons ct
    foundTcs <- findConstraintOrInstanceTyCons (constraintTcVars ct) (tyCon, tyArgs)
    return $ tcs `S.union` foundTcs
  Nothing -> return S.empty

-- | Retrieve the source location the given constraint originated from.
constraintLocation :: Ct -> CtLoc
constraintLocation ct = ctev_loc $ cc_ev ct
