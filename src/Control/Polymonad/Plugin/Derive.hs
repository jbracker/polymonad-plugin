
-- | Code to derive new polymonad constraints from existing ones.
module Control.Polymonad.Plugin.Derive
  ( derivePolymonadConstraints ) where

import Data.Maybe ( catMaybes, isNothing )
import Data.List ( nubBy, find )

import TcRnTypes
  ( Ct, CtLoc
  , ctPred
  , isDerivedCt
  )
import Type
  ( Type
  , eqType
  , getTyVar_maybe
  , splitAppTys
  , mkTyConTy )
import TcType ( isAmbiguousTyVar )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , assert
  , getGivenPolymonadConstraints
  , getIdentityTyCon, getPolymonadClass )
import Control.Polymonad.Plugin.Constraint
  ( WantedCt, DerivedCt
  , isClassConstraint
  , mkDerivedClassCt
  , constraintLocation, constraintPolymonadTyArgs )

-- | Tries to derive a given wanted constraint from the given and already
--   derived constraints. A constraint can only be derived if there
--   is a polymonad laws that guards it being derived from already given
--   or derived constraints.
--
--   This function is limited in its functionality. It will only perform a
--   one level search of polymonad law applications onto the given derived
--   constraints.
--
--   FIXME/TODO: Not all polymonad laws are currently supported.
tryDerivePolymonadConstraint :: WantedCt -> PmPluginM (Maybe DerivedCt)
tryDerivePolymonadConstraint wantedPmCt = do
  -- Ensure the given wanted constraint is a polymonad constraint.
  pmCls <- getPolymonadClass
  assert (isClassConstraint pmCls wantedPmCt) "tryDerivePolymonadConstraint: Wanted constraint is not a polymonad constraint!"
  -- Take a look at the given an derived constraints to see if we can derive
  -- the wanted constraint from them.
  givenPmCts <- getGivenPolymonadConstraints

  -- TODO/FIXME
  return Nothing

-- | Derives polymonad constraints that need to exists by the definition
--   of polymonads from the set of given constraints.
--   Only returns the newly derived constraints. The argument constraints
--   need to be given polymonad constraints.
--
--   Note: Currently only functor constraints are derived. The existance of these
--   instances is given by the functor law for each polymonad.
derivePolymonadConstraints :: PmPluginM [Ct]
derivePolymonadConstraints =  do
  -- Get the given polymonad constraints to derive from.
  givenCts <- getGivenPolymonadConstraints
  -- Only proceed of there are no derived constraints yet.
  if any isDerivedCt givenCts
    then return []
    else do
      -- Get a list of all unary (partially applied) unambigous type constructors
      -- in the given constraints, e.g., @n a b@ or @m@. Also delivers the location
      -- of the constraints they were extracted from.
      let tcvs = nubBy eqTy $ concat $ catMaybes
               $ fmap constraintPolymonadUnambiguousUnaryTyConVars givenCts
      -- Get the identity type constructor and the polymonad class.
      idTc <- mkTyConTy <$> getIdentityTyCon
      pmCls <- getPolymonadClass
      -- Create derived functor constraints for each unique (duplicates already removed)
      -- type constructor.
      let derivedFunctorCts = fmap (\(t, loc) -> mkDerivedClassCt loc pmCls [t, idTc, t]) tcvs
      -- Filter constraints that were created but already existed in the set of
      -- given constraints.
      return $ filter (\dCt -> isNothing $ find (eqClassCt dCt) givenCts) derivedFunctorCts
      where
        eqTy :: (Type, a) -> (Type, b) -> Bool
        eqTy (t0, _) (t1, _) = eqType t0 t1

        eqClassCt :: Ct -> Ct -> Bool
        eqClassCt ct0 ct1 = eqType (ctPred ct0) (ctPred ct1)


-- | Returns the unary type constructor variables and partially applied
--   unary type constructor variables. The type constructor variables
--   returned this way are ensured not to be ambiguous.
--   /Example:/
--
--   > constraintPolymonadUnaryTyConVars (Polymonad (m a b) Identity n)
--   > > { (m a b), n } -- m and n are not ambiguous.
constraintPolymonadUnambiguousUnaryTyConVars :: Ct -> Maybe [(Type, CtLoc)]
constraintPolymonadUnambiguousUnaryTyConVars ct = do
  (t0, t1, t2) <- constraintPolymonadTyArgs ct
  let loc = constraintLocation ct
  return $ (\t -> (t, loc)) <$> filter f [t0, t1, t2]
  where
    f :: Type -> Bool
    f t = case getTyVar_maybe $ fst $ splitAppTys t of
      Just tv -> not $ isAmbiguousTyVar tv
      Nothing -> False
