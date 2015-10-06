
-- | Functions to calculate the principal join.
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoinFor
  ) where

import Data.List ( nubBy )
import Data.Maybe ( catMaybes, fromJust, isJust )
--import qualified Data.Set as S

import Control.Monad ( forM ) --, when )
import Control.Arrow ( (***), second )

import Type
  ( Type, TyVar
  , mkTyConTy
  , eqType
  , getTyVar_maybe
  , substTy )
import TcType ( isAmbiguousTyVar )
import InstEnv ( ClsInst(..), instanceSig, instanceBindFun )
import TcRnTypes ( Ct )
import Unify ( tcUnifyTy, tcUnifyTys )
import Unique ( unpkUnique, getUnique )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , assert
  , throwPluginError
  , getCurrentPolymonad
  , getIdentityTyCon
  , printObj, printMsg )
import Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars, isInstantiatedBy )
import Control.Polymonad.Plugin.Core ( isInstanceOf )
import Control.Polymonad.Plugin.Constraint
  ( GivenCt, constraintPolymonadTyArgs )
import Control.Polymonad.Plugin.Utils
  ( allM, anyM )

--   Assumes that there are no ambiguous type constructors in the set @f@.
principalJoin :: [(Type, Type)] -> [Type] -> PmPluginM (Maybe Type)
principalJoin f m = do
  printMsg "CUSTOM JOIN BEGIN"
  -- Assert
  assert (not $ null f) "principalJoinFor: F is empty"
  --assert (not $ null m) "principalJoinFor: m is empty"
  --assert (length m <= 2) "principalJoinFor: m contains more then two elements"
  -- The polymonad we want to work with
  (_pmTyVarsAndCons, pmInsts, pmGivenCts) <- getCurrentPolymonad

  -- Look at each pair of incoming types
  -- [[(Either ClsInst GivenCt, Type)]]
  foundMatchingInstances <- forM f $ \(m1, m2) -> do
    -- Match them against the polymonad instances
    instMatchResult <- forM pmInsts $ \pmInst -> do
      -- Look at the current instance arguments
      mInstM3 <- case instanceSig pmInst of -- ([TyVar], [Type], Class, [Type])
        (_instVars, _cts, _cls, [im1, im2, im3]) ->
          -- Unify the first two arguments
          case tcUnifyTys instanceBindFun [im1, im2] [m1, m2] of
            -- Determine the third argument using the unification substitution
            Just subst -> do
              let m3 = substTy subst im3
              return $ Just m3
            -- They don't match up, therefore there is not suitable third argument
            Nothing -> return Nothing
        -- This should never happen if instances were filtered correctly by the environment.
        _ -> throwPluginError "principalJoin: Polymonad instance does not have exactly three arguments."
      return (Left pmInst, mInstM3)

    cnstrMatchResult <- forM pmGivenCts $ \pmGivenCt -> do
      -- Look at the current instance arguments
      mCnstrM3 <- case constraintPolymonadTyArgs pmGivenCt of -- ([TyVar], [Type], Class, [Type])
        Just (im1, im2, im3) ->
          -- Unify the first two arguments
          case tcUnifyTys instanceBindFun [im1, im2] [m1, m2] of
            -- Determine the third argument using the unification substitution
            Just subst -> do
              let m3 = substTy subst im3
              return $ Just m3
            -- They don't match up, therefore there is not suitable third argument
            Nothing -> return Nothing
        -- This should never happen if instances were filtered correctly by the environment.
        _ -> throwPluginError "principalJoin: Polymonad given constraints do not have exactly three arguments."
      return (Right pmGivenCt, mCnstrM3)

    -- Only keep those match results that actually matched.
    -- Also remove entries that produce the same type. This is legitimate,
    -- since we talk about two instances that are applied to exactly the same
    -- arguments, and therefore, need to be semantically equal.
    return $ removeDuplicateTypes snd
           $ second fromJust <$> filter (\(_, m3) -> isJust m3) (instMatchResult ++ cnstrMatchResult)
  -- Check if we have a unique type constructor for each pair.
  if all ((1 ==) . length) foundMatchingInstances
    -- There is a unique solution for each pair, now check if
    -- they all fit together and return that solution.
    then return $ allUnifiable $ fmap (snd . head) foundMatchingInstances
    -- There is no unique solution. Maybe we don't have a solution at all?
    else if any ((0 ==) . length) foundMatchingInstances
      then return Nothing
      -- There have to be several different solutions for some paires.
      -- Figure out which one to use.
      else pickSolution foundMatchingInstances

  where
    pickSolution :: [[(Either ClsInst GivenCt, Type)]] -> PmPluginM (Maybe Type)
    pickSolution foundMatchingJoins = do
      printMsg "M:"
      printObj m
      idTC <- mkTyConTy <$> getIdentityTyCon
      (_, pmInsts, pmGivenCts) <- getCurrentPolymonad
      _ <- forM foundMatchingJoins $ \joinPairs -> do
        let possibleJoins = nubBy eqType $ snd <$> joinPairs
        printObj possibleJoins
        mCheckedJoins <- forM possibleJoins $ \possibleJoin -> do
          allOutBinds <- allM (\m3 -> printObj (possibleJoin, idTC, m3) >> hasMatch (possibleJoin, idTC, m3) (pmInsts, pmGivenCts)) m
          return $ if allOutBinds then Just possibleJoin else Nothing
        let checkedJoins = catMaybes mCheckedJoins
        printObj checkedJoins
        --undefined
      return Nothing
      --throwPluginError "principalJoin: There are several possible solutions for one of the join pairs."

    -- hasMatch :: (Type, Type, Type) -> ([ClsInst], [Ct]) -> PmPluginM Bool


    removeDuplicateTypes :: (a -> Type) -> [a] -> [a]
    removeDuplicateTypes _ [] = []
    removeDuplicateTypes p (a : as)
      = a : removeDuplicateTypes p
              (filter (\a' -> not $ eqType (p a') (p a)) as)

    -- | Check of all of the given types are unifiable with each other and
    --   returns the most general type that all of them can agree on.
    allUnifiable :: [Type] -> Maybe Type
    allUnifiable [] = Nothing
    allUnifiable [t] = return t
    allUnifiable (t : ts) = do
      let unifSubsts = fmap (tcUnifyTy t) ts
      if all isJust unifSubsts
        then do
          resT' <- allUnifiable ts
          subst <- tcUnifyTy t resT'
          return $ substTy subst t
        else Nothing

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
principalJoinFor mAmbTv f m = --do
  principalJoin f m {-}
  -- Assert
  {-
  assert (not $ null f) "principalJoinFor: F is empty"
  assert (not $ null m) "principalJoinFor: m is empty"
  assert (length m <= 2) "principalJoinFor: m contains more then two elements"
  -}
  -- Get the type of the identity type constructor
  idT <- mkTyConTy <$> getIdentityTyCon
  -- The polymonad we want to work with
  (pmTyVarsAndCons, pmInsts, pmGivenCts) <- getCurrentPolymonad
  -- Collect all of the possible joins.
  -- For now we assume it is one of the known type constructors.
  -- FIXME: Does this work for type constructors with arity greater one?
  let joinCands = pmTyVarsAndCons
  -- Go through all of the candidates and check if they fulfill the conditions
  -- of a principal join.
  printObj joinCands
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
  case suitableJoinCands of
    [] -> return Nothing
    [sjc] -> return $ Just sjc
    _ -> do
      printObj suitableJoinCands
      throwPluginError "principalJoinFor: Found more then one join. FIXME"

  where
    substTopTyVar :: (TyVar, Type) -> Type -> Type
    substTopTyVar (tv, ty) t = case getTyVar_maybe t of
      Just tv' -> if tv == tv' then ty else t
      Nothing -> t
-}

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
