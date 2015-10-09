
-- | Functions to calculate the principal join.
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoinFor
  ) where

import Data.List ( nubBy, find )
import Data.Maybe ( catMaybes, fromJust, isJust )
import qualified Data.Set as S
--import qualified Data.Set as S

import Control.Monad ( forM ) --, when )
import Control.Arrow ( (***), second )

import BasicTypes ( Arity )
import Kind ( Kind )
import Type
  ( Type, TyVar
  , mkTyConTy, mkTyVarTy, mkAppTys
  , eqType
  , getTyVar_maybe, getTyVar
  , splitAppTys
  , substTy )
import TyCon ( TyCon )
import TcType ( isAmbiguousTyVar )
import InstEnv ( ClsInst(..), instanceSig, instanceBindFun )
import TcRnTypes ( Ct )
import TcPluginM ( newFlexiTyVar )
import Unify ( tcUnifyTy, tcUnifyTys, tcMatchTys, BindFlag(..) )
import Unique ( unpkUnique, getUnique )
import VarSet ( mkVarSet )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , assert
  , throwPluginError
  , getCurrentPolymonad
  , getWantedPolymonadConstraints
  , getIdentityTyCon
  , printObj, printMsg )
import Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars
  , instancePolymonadTyArgs
  , isInstantiatedBy )
import Control.Polymonad.Plugin.Core ( isInstanceOf )
import Control.Polymonad.Plugin.Constraint
  ( GivenCt, constraintPolymonadTyArgs )
import Control.Polymonad.Plugin.Utils
  ( allM, anyM, isAmbiguousType, collectTyVars )
import Control.Polymonad.Plugin.Topological
  ( topologicalTyConOrder )

-- Assumes that there are no ambiguous type constructors in the set @f@.
principalJoin :: [(Type, Type)] -> [Type] -> PmPluginM (Maybe Type)
principalJoin f mWithAmbVars = do
  printMsg "PRICIPAL JOIN"
  -- Assert
  assert (not $ null f) "principalJoinFor: F is empty"
  --assert (not $ null m) "principalJoinFor: m is empty"
  --assert (length m <= 2) "principalJoinFor: m contains more then two elements"
  -- The polymonad we want to work with
  (pmTyVarsAndCons, pmInsts, pmGivenCts) <- getCurrentPolymonad
  printObj pmTyVarsAndCons
  -- Look at each pair of incoming types
  -- [[(Either ClsInst GivenCt, Type)]]
  foundMatchingInstances <- forM f $ \(m1, m2) -> do
    xs <- forM pmTyVarsAndCons $ \m3TcTv -> do
      (m3, _m3TyVars) <- applyTyCon m3TcTv
      -- Match them against the polymonad instances to find possible joins
      instMatchResult <- forM pmInsts $ \pmInst -> do
        -- Look at the current instance arguments
        mInstM3 <- case instanceSig pmInst of -- ([TyVar], [Type], Class, [Type])
          -- Try to find a join candidate based on the current instance.
          -- Looking at an instance we may not keep one of its variables as a
          -- possible candidate, since they are quantified within the instance only.
          (instVars, _cts, _cls, [im1, im2, im3]) -> findJoinCandidate instVars (im1, im2, im3) (m1, m2, m3)
          -- This should never happen if instances were filtered correctly by the environment.
          _ -> throwPluginError "principalJoin: Polymonad instance does not have exactly three arguments."
        return (Left pmInst, mInstM3)
      -- Match them against the given olymonad constraints to find possible joins
      cnstrMatchResult <- forM pmGivenCts $ \pmGivenCt -> do
        -- Look at the current instance arguments
        mCnstrM3 <- case constraintPolymonadTyArgs pmGivenCt of
          -- Try to find a join candidate based on the current constraint.
          Just (im1, im2, im3) -> findJoinCandidate [] (im1, im2, im3) (m1, m2, m3)
          -- This should never happen if instances were filtered correctly by the environment.
          _ -> throwPluginError "principalJoin: Polymonad given constraints do not have exactly three arguments."
        return (Right pmGivenCt, mCnstrM3)

      -- Only keep those match results that actually matched.
      -- Also remove entries that produce the same type. This is legitimate,
      -- since we talk about two instances that are applied to exactly the same
      -- arguments, and therefore, need to be semantically equal.
      return $ removeDuplicateTypes snd
             $ second fromJust <$> filter (\(_, p) -> isJust p) (instMatchResult ++ cnstrMatchResult)
    return $ concat xs
  printMsg "Matches:"
  printObj $ zip f foundMatchingInstances
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
    m :: [Type]
    m = filter (not . isAmbiguousType) mWithAmbVars

    pickSolution :: [[(Either ClsInst GivenCt, Type)]] -> PmPluginM (Maybe Type)
    pickSolution foundMatchingJoins = do
      idTC <- mkTyConTy <$> getIdentityTyCon
      (_pmTyCons, pmInsts, pmGivenCts) <- getCurrentPolymonad
      let possibleJoins = nubBy eqType $ concatMap (fmap snd) foundMatchingJoins
      mCheckedJoins <- forM possibleJoins $ \possibleJoin -> do
        allOutBinds <- allM (\m3 -> hasMatch (possibleJoin, idTC, m3) (pmInsts, pmGivenCts)) m
        return $ if allOutBinds then Just possibleJoin else Nothing
      let checkedJoins = catMaybes mCheckedJoins
      case checkedJoins of
        [] -> return Nothing
        [join] -> return $ Just join
        _ -> do
          wantedCts <- getWantedPolymonadConstraints
          topoOrder <- filter (not . isAmbiguousType) <$> topologicalTyConOrder wantedCts
          let orderedJoins = filter (`elem` checkedJoins) topoOrder
          assert (length orderedJoins == length checkedJoins) "principalJoin: Ordering of joins led to missing joins."
          return $ Just $ head orderedJoins
      --throwPluginError "principalJoin: There are several possible solutions for one of the join pairs."

    -- hasMatch :: (Type, Type, Type) -> ([ClsInst], [Ct]) -> PmPluginM Bool

    findJoinCandidate :: [TyVar] -> (Type, Type, Type) -> (Type, Type, Type) -> PmPluginM (Maybe Type)
    findJoinCandidate invalidVars (im1, im2, im3) (m1, m2, m3) = do
      printMsg $ "findJoinCandidate " ++ if null invalidVars then "constraint" else "instance"
      printObj (im1, im2, im3)
      printObj (m1, m2, m3)
      -- Unify the first two arguments
      case tcMatchTys (mkVarSet $ invalidVars ++ fmAmbVars) [im1, im2, im3] [m1, m2, m3] of -- instanceBindFun
        -- Determine the third argument using the unification substitution
        Just subst -> do
          printObj subst
          let p = substTy subst m3
          printObj p
          -- Incase we have type constructor variables that may not leave the scope
          -- be sure to filter them out.
          return $ case getTyVar_maybe $ fst (splitAppTys m3) of
            Just tv -> if tv `elem` invalidVars then Nothing else Just p
            Nothing -> Just p
        -- They don't match up, therefore there is not suitable third argument
        Nothing -> return Nothing

    removeDuplicateTypes :: (a -> Type) -> [a] -> [a]
    removeDuplicateTypes _ [] = []
    removeDuplicateTypes p (a : as)
      = a : removeDuplicateTypes p
              (filter (\a' -> not $ eqType (p a') (p a)) as)

    fmAmbVars :: [TyVar]
    fmAmbVars = nubBy (==)
              $ fmap (getTyVar "fmAmbVars: There should not be a non-type variable in here.")
              $ filter isAmbiguousType
              $ m ++ concatMap (\(a, b) -> [a, b]) f

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
principalJoinFor mAmbTv f m = do
  --principalJoin f m {-}
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
  -- Go through all of the candidates and check if they fulfill the conditions
  -- of a principal join.
  mSuitableJoinCands <- forM pmTyVarsAndCons $ \tyVarAndCons -> do
    (joinCand, joinCandVars) <- applyTyCon tyVarAndCons
    -- FIXME: Check join precondition
    -- Remove duplicates and substitute the top level ambiguous type variable
    -- if it is there.
    let substF = nubBy (\(t0, t1) (t0', t1') -> eqType t0 t0' && eqType t1 t1')
               $ maybe f (\ambTv -> (substTopTyVar (ambTv, joinCand) *** substTopTyVar (ambTv, joinCand)) <$> f) mAmbTv
    let substM = nubBy eqType
               $ maybe m (\ambTv -> substTopTyVar (ambTv, joinCand) <$> m) mAmbTv
    -- Check if all the incoming binds are actually there
    fMatches <- fmap and $ forM substF $ \(t0, t1) -> do
                _ <- determineJoinCandidates tyVarAndCons (pmInsts, pmGivenCts) (t0, t1)
                hasMatch (t0, t1, joinCand) (pmInsts, pmGivenCts)
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

-- | Applies the given type constructor or type constructor variables to enought
--   correctly kinded variables to make it a partially applied unary type
--   constructor. The partially applied unary type constructor is returned
--   together with the variables that were applied to it.
--
--   Will throw an error if there are to few kind arguments. If supposed to be
--   used in conjunction with the first part of 'getCurrentPolymonad'.
applyTyCon :: (Either TyCon TyVar, [Kind]) -> PmPluginM (Type, [TyVar])
applyTyCon (_    , []) = throwPluginError "applyTyCon: Type constructor should have at least one argument"
applyTyCon (eTcTv, ks) = do
  let ks' = init ks
  tyVarArgs <- forM ks' (runTcPlugin . newFlexiTyVar)
  let t = either mkTyConTy mkTyVarTy eTcTv
  return (mkAppTys t $ fmap mkTyVarTy tyVarArgs, tyVarArgs)

isPolymonadCtMatch :: (Type, Type, Type) -> Ct -> Bool
isPolymonadCtMatch (t0, t1, t2) ct
  = maybe False (\(t0', t1', t2') -> eqType t0 t0' && eqType t1 t1' && eqType t2 t2')
  $ constraintPolymonadTyArgs ct

instance Show BindFlag where
  show Skolem = "Skolem"
  show BindMe = "BindMe"

determineJoinCandidates :: (Either TyCon TyVar, [Kind]) -> ([ClsInst], [Ct]) -> (Type, Type) -> PmPluginM [Type]
determineJoinCandidates tyVarOrCons (pmInsts, pmCnstrs) (t0, t1) = do
  printMsg "DETERMINE JOIN CAND:"
  (joinCand, joinCandVars) <- applyTyCon tyVarOrCons
  printObj (t0, t1, joinCand)
  let dontBindTvs = either (const []) (: []) $ fst $ tyVarOrCons
  instanceCands <- forM pmInsts $ \pmInst -> do
    let (instVars, _cts, _cls, instTys@[it0, it1, it2]) = instanceSig pmInst
    printMsg "INST"
    printObj instTys
    case tcUnifyTys (skolemVarsBindFun dontBindTvs) instTys [t0, t1, joinCand] of
      Just subst -> do
        printObj (t0, t1, substTy subst joinCand)
        return $ Just $ substTy subst joinCand
      Nothing -> return Nothing
  constraintCands <- forM pmCnstrs $ \pmCnstr ->
    case constraintPolymonadTyArgs pmCnstr of
      Just ctTys@(ct0, ct1, ct2) -> do
        let ctVars = S.toList $ S.unions $ fmap collectTyVars [ct0, ct1, ct2]
        printMsg "CT"
        printObj ctTys
        case tcUnifyTys (skolemVarsBindFun $ dontBindTvs ++ ctVars) [ct0, ct1, ct2] [t0, t1, joinCand] of
          Just subst -> do
            printObj (t0, t1, substTy subst joinCand)
            return $ Just $ substTy subst joinCand
          Nothing -> return Nothing
      Nothing -> return Nothing
  printMsg "CANDS"
  printObj $ nubBy eqType $ catMaybes $ instanceCands ++ constraintCands
  return $ nubBy eqType $ catMaybes $ instanceCands ++ constraintCands

-- | Override the standard bind flag of a given list of variables to 'Skolem'.
--   The standard bind flad is determined using 'instanceBindFun'.
skolemVarsBindFun :: [TyVar] -> TyVar -> BindFlag
skolemVarsBindFun tvs var = case find (var ==) tvs of
  Just _ -> Skolem
  Nothing -> instanceBindFun var

hasMatch :: (Type, Type, Type) -> ([ClsInst], [Ct]) -> PmPluginM Bool
hasMatch tys@(t0, t1, t2) (pmInsts, pmCts) = do
  instanceMatches <- forM pmInsts $ \pmInst ->
    case matchInstanceTyVars [t0, t1, t2] pmInst of
      Just args -> args `isInstanceOf` pmInst
      Nothing -> return False
  let constraintMatches = any (isPolymonadCtMatch tys) pmCts
  return $ or instanceMatches || constraintMatches
