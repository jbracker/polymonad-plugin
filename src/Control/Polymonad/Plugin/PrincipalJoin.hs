
-- | Functions to calculate the principal join.
module Control.Polymonad.Plugin.PrincipalJoin
  ( principalJoinFor ) where

import Data.List ( nubBy )
import Data.Maybe ( catMaybes, isJust )
import qualified Data.Set as S

import Control.Monad ( forM ) --, when )
import Control.Arrow ( (***) )

import Kind ( Kind )
import Type
  ( Type, TyVar
  , mkTyConTy, mkTyVarTy, mkAppTys
  , eqType
  , mkTopTvSubst
  , substTy )
import TyCon ( TyCon )
import InstEnv ( ClsInst(..), instanceSig )
import TcRnTypes ( Ct )
import TcPluginM ( newFlexiTyVar )
import Unify ( tcUnifyTy, tcUnifyTys )

import Control.Polymonad.Plugin.Environment
  ( PmPluginM, runTcPlugin
  , assert
  , throwPluginError
  , printObj --, printMsg
  , getCurrentPolymonad )
import Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars )
import Control.Polymonad.Plugin.Core ( isInstanceOf )
import Control.Polymonad.Plugin.Constraint
  ( GivenCt, constraintPolymonadTyArgs )
import Control.Polymonad.Plugin.Utils
  ( collectTyVars, skolemVarsBindFun )
import Control.Polymonad.Plugin.Evaluate ( evaluateTypeEqualities )

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
principalJoinFor mAmbTv f _m = do
  --principalJoin f m {-}
  -- Assert
  assert (not $ null f) "principalJoinFor: F is empty"
  -- assert (not $ null m) "principalJoinFor: m is empty"
  -- assert (length m <= 2) "principalJoinFor: m contains more then two elements"
  -- Get the type of the identity type constructor
  -- idT <- mkTyConTy <$> getIdentityTyCon
  -- The polymonad we want to work with
  (pmTyVarsAndCons, pmInsts, pmGivenCts) <- getCurrentPolymonad
  joinCands <- determineCommonJoinCandidates pmTyVarsAndCons (pmInsts, pmGivenCts) f
  -- Go through all of the candidates and check if they fulfill the conditions
  -- of a principal join.
  mSuitableJoinCands <- forM joinCands $ \joinCand -> do
    let ambSubst ambTv = mkTopTvSubst [(ambTv, joinCand)]
    -- Remove duplicates and substitute the top level ambiguous type variable
    -- if it is there.
    let substF = nubBy (\(t0, t1) (t0', t1') -> eqType t0 t0' && eqType t1 t1')
               $ maybe f (\ambTv -> (substTy (ambSubst ambTv) *** substTy (ambSubst ambTv)) <$> f) mAmbTv
    -- let substM = nubBy eqType
    --            $ maybe m (\ambTv -> substTopTyVar (ambTv, joinCand) <$> m) mAmbTv
    -- Check if all the incoming binds are actually there
    fMatches <- fmap and $ forM substF
              $ \(t0, t1) -> hasMatch (t0, t1, joinCand) (pmInsts, pmGivenCts)
    -- Check if all the outgoing binds are actually there
    -- mMatches <- fmap and $ forM substM
    --           $ \t2 -> hasMatch (joinCand, idT, t2) (pmInsts, pmGivenCts)
    -- If everything works out, keep the current join candidate
    return $ if fMatches {-&& mMatches-} then Just joinCand else Nothing
  let suitableJoinCands = catMaybes mSuitableJoinCands
  case suitableJoinCands of
    [] -> return Nothing
    [sjc] -> return $ Just sjc
    _ -> do
      printObj suitableJoinCands
      throwPluginError "principalJoinFor: Found more then one join. FIXME"

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

-- | Check if the given combination of types matches the given constraints
--   arguments.
isPolymonadCtMatch :: (Type, Type, Type) -> Ct -> Bool
isPolymonadCtMatch (t0, t1, t2) ct
  = maybe False (\(t0', t1', t2') -> eqType t0 t0' && eqType t1 t1' && eqType t2 t2')
  $ constraintPolymonadTyArgs ct

-- | Check if there is a common join candidate for all of the given
--   type constructors, variables and input type pairs. Details
--   of determining a join candidate can be seen in 'determineJoinCandidates'.
determineCommonJoinCandidates :: [(Either TyCon TyVar, [Kind])] -> ([ClsInst], [GivenCt]) -> [(Type, Type)] -> PmPluginM [Type]
determineCommonJoinCandidates tyVarOrCons (pmInsts, pmCts) f = do
  joinCandList <- forM tyVarOrCons $ \tyVarOrCon -> do
    joinCandList <- forM f $ determineJoinCandidates tyVarOrCon (pmInsts, pmCts)
    return $ catMaybes $ allUnifiable <$> oneOfAll joinCandList
  return $ nubBy eqType $ concat joinCandList

-- | Determine the join candidates that result from the given type constructor
--   or variable using the given set of instances and given constraints and
--   and the given pair of input types.
determineJoinCandidates :: (Either TyCon TyVar, [Kind]) -> ([ClsInst], [GivenCt]) -> (Type, Type) -> PmPluginM [Type]
determineJoinCandidates tyVarOrCons (pmInsts, pmCts) (t0, t1) = do
  -- We apply our current candidate to temporary variables
  (joinCand, _joinCandVars) <- applyTyCon tyVarOrCons
  -- Remember that we do not want to substitute our candidate if it is a type variable
  let dontBindTvs = either (const []) (: []) $ fst tyVarOrCons
  -- Now look at each instance and see of unification with out desired
  -- triplet of arguments delivers a match. If so substitute the temporary
  -- type variables and keep the substituted type constructor as possible condidate
  instanceCands <- forM pmInsts $ \pmInst -> do
    let (_instVars, superCts, _cls, instArgTys) = instanceSig pmInst
    case tcUnifyTys (skolemVarsBindFun dontBindTvs) instArgTys [t0, t1, joinCand] of
      Just subst -> do
        -- Substitute the correct matchings in our candidate.
        let substJoinCand = substTy subst joinCand
        -- Now also evaluate type equalities to some extent.
        -- This is necessary, because there are some type classes with type
        -- equality constraints on them (see the effect monad example). We
        -- need to evaluate these so we do not end up looking at our temporarly
        -- generated variables.
        let evalJoinCand = evaluateTypeEqualities ([], fmap (substTy subst) superCts) substJoinCand
        return $ Just evalJoinCand
      Nothing -> return Nothing
  -- Repeat the same process for given constraints.
  constraintCands <- forM pmCts $ \pmCt ->
    case constraintPolymonadTyArgs pmCt of
      Just (ct0, ct1, ct2) -> do
        -- Here we have to make sure that type variable constructors from
        -- the given constraints are not substituted
        let ctVars = S.toList $ S.unions $ fmap collectTyVars [ct0, ct1, ct2]
        case tcUnifyTys (skolemVarsBindFun $ dontBindTvs ++ ctVars) [ct0, ct1, ct2] [t0, t1, joinCand] of
          Just subst -> return $ Just $ substTy subst joinCand
          Nothing -> return Nothing
      Nothing -> return Nothing
  -- Finally return all found candidates and remove and duplicates among them.
  return $ nubBy eqType $ catMaybes $ instanceCands ++ constraintCands

-- | Checks if there is a matching instance or given constraints that matches
--   the given combination of arguments.
hasMatch :: (Type, Type, Type) -> ([ClsInst], [GivenCt]) -> PmPluginM Bool
hasMatch tys@(t0, t1, t2) (pmInsts, pmCts) = do
  instanceMatches <- forM pmInsts $ \pmInst -> do
    case matchInstanceTyVars [t0, t1, t2] pmInst of
      Just args ->
        args `isInstanceOf` pmInst
      Nothing ->
        return False
  let constraintMatches = any (isPolymonadCtMatch tys) pmCts
  return $ or instanceMatches || constraintMatches

-- | Create all lists that contain exactly one element from each given list.
--   All lists are unique if the elements being worked with are unique.
--
--   /Examples/:
--
-- >>> oneOfAll [ [1,2], [3], [4] ]
-- [ [1,3,4], [2,3,4] ]
--
-- >>> oneOfAll [ [2], [], [5] ]
-- []
--
-- >>> oneOfAll [ [1,2], [3], [4,5] ]
-- [ [1,3,4], [1,3,5], [2,3,4], [2,3,5] ]
oneOfAll :: [[a]] -> [[a]]
oneOfAll [] = [[]]
oneOfAll ([] : _xxs) = []
oneOfAll ([x] : xxs) = fmap (x :) (oneOfAll xxs)
oneOfAll ((x : xs) : xxs) = fmap (x :) (oneOfAll xxs) ++ oneOfAll (xs : xxs)

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
