
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoinFor
  ) where

import Data.List ( nubBy )
import Data.Maybe ( catMaybes )
import qualified Data.Set as S

import Control.Monad ( forM, when )
import Control.Arrow ( (***) )

import Type
  ( Type, TyVar
  , mkTyConTy
  , eqType
  , getTyVar_maybe )
import InstEnv ( ClsInst(..) )
import TcRnTypes ( Ct )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM
  , throwPluginError
  , getCurrentPolymonad
  , getIdentityTyCon
  , printObj )
import Control.Polymonad.Plugin.Instance ( matchInstanceTyVars )
import Control.Polymonad.Plugin.Core ( isInstanceOf )
import Control.Polymonad.Plugin.Constraint ( constraintPolymonadTyArgs )

-- | Calculate the principal join of a set of unary type constructors.
--   For this to work properly all of the given types need to be
--   type constructors or partially applied type constructors.
--   The principal join is defined in definition 4 of the
--   "Polymonad Programming" paper.
--
--   @principalJoin tv f m@ calculates the principal join.
--   @f@ is the set of unary type constructor pairs and @m@ is
--   the set of type constructors we want to arrive at ({M_1, M_2} subsetof Sigma).
--   @tv@ may be a ambiguous type variable that will be replaced with the
--   join candidate while searching.
--
--   According to communication with the authors of the paper @f@ should
--   never be empty. The original definition requires exactly one or two
--   type constructors in @m@. The type constructors in these sets may also
--   be variables that appear as type constructors in the given constraints,
--   but it is the responsibility of the user to ensure that they actually
--   represent type constructors.
principalJoinFor :: Maybe TyVar -> [(Type, Type)] -> [Type] -> PmPluginM (Maybe Type)
principalJoinFor mAmbTv f m = do
  -- Assert
  when (null f) $ throwPluginError "principalJoinFor: F is empty"
  when (null m) $ throwPluginError "principalJoinFor: m is empty"
  when (length m > 2) $ throwPluginError "principalJoinFor: m contains more then two elements"
  -- Get the type of the identity type constructor
  idT <- mkTyConTy <$> getIdentityTyCon
  -- The polymonad we want to work with
  (pmTyCons, pmTyVars, pmInsts, pmGivenCts) <- getCurrentPolymonad
  -- Collect all of the possible joins.
  -- For now we assume it is one of the known type constructors.
  -- FIXME: Does this work for type constructors with arity greater one?
  let joinCands = pmTyVars ++ (mkTyConTy <$> S.toList pmTyCons)
  -- Go through all of the candidates and check if they fulfill the conditions
  -- of a principal join.
  mSuitableJoinCands <- forM joinCands $ \joinCand -> do
    -- FIXME: Check join precondition
    -- Remove duplicates and substitute the top level ambiguous type variable
    -- if it is there.
    let substF = nubBy (\(t0, t1) (t0', t1') -> eqType t0 t0' && eqType t1 t1')
               $ maybe f (\ambTv -> (substTopTyVar (ambTv, joinCand) *** substTopTyVar (ambTv, joinCand)) <$> f) mAmbTv
    let substM = nubBy eqType
               $ maybe m (\ambTv -> substTopTyVar (ambTv, joinCand) <$> m) mAmbTv
    -- Check if all the incoming binds are actually there
    fMatches <- fmap and $ forM substF
              $ \(t0, t1) -> hasMatch (t0, t1, joinCand) (pmInsts, pmGivenCts)
    -- Check if all the outgoing binds are actually there
    mMatches <- fmap and $ forM substM
              $ \t2 -> hasMatch (joinCand, idT, t2) (pmInsts, pmGivenCts)
    -- If everything works out, keep the current join candidate
    return $ if fMatches && mMatches then Just joinCand else Nothing
  let suitableJoinCands = catMaybes mSuitableJoinCands
  case length suitableJoinCands of
    0 -> return Nothing
    1 -> return $ Just $ head suitableJoinCands
    _ -> do
      printObj suitableJoinCands
      throwPluginError "principalJoinFor: Found more then one join. FIXME"

  where
    substTopTyVar :: (TyVar, Type) -> Type -> Type
    substTopTyVar (tv, ty) t = case getTyVar_maybe t of
      Just tv' -> if tv == tv' then ty else t
      Nothing -> t

    isPolymonadCtMatch :: (Type, Type, Type) -> Ct -> Bool
    isPolymonadCtMatch (t0, t1, t2) ct
      = maybe False (\(t0', t1', t2') -> eqType t0 t0' && eqType t1 t1' && eqType t2 t2')
      $ constraintPolymonadTyArgs ct

    hasMatch :: (Type, Type, Type) -> ([ClsInst], [Ct]) -> PmPluginM Bool
    hasMatch tys@(t0, t1, t2) (pmInsts, pmCts) = do
      instanceMatches <- forM pmInsts $ \pmInst ->
        case matchInstanceTyVars [t0, t1, t2] pmInst of
          Just args -> args `isInstanceOf` pmInst
          Nothing -> return False
      let constraintMatches = any (isPolymonadCtMatch tys) pmCts
      return $ or instanceMatches || constraintMatches
