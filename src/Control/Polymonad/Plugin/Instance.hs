
-- | Functions and utilities to work with and inspect class instances
--   of the GHC API.
module Control.Polymonad.Plugin.Instance
  ( matchInstanceTyVars
  , eqInstance
  , instanceClassTyCon
  , instanceTyArgs
  , instanceTyCons
  , instanceTcVars
  , instanceType
  , instancePolymonadTyArgs
  , isInstantiatedBy
  ) where

import Data.Maybe ( catMaybes, isJust )
import Data.List ( find )
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad ( forM, liftM2 )

import InstEnv
  ( ClsInst(..), IsOrphan(..)
  , instanceSig
  , lookupUniqueInstEnv )
import Type
  ( Type, TyVar
  , mkTyVarTy
  , substTy, substTys
  , mkTopTvSubst
  , getClassPredTys_maybe
  , eqTypes )
import Class ( Class, classTyCon )
import TyCon ( TyCon )
import Unify ( tcUnifyTys )
--import VarSet ( mkVarSet )
import TcPluginM ( TcPluginM, getInstEnvs )
import TcRnTypes ( Ct )
import TcType ( isAmbiguousTyVar )

import Control.Polymonad.Plugin.Log
  ( missingCaseError, printObjTrace )
import Control.Polymonad.Plugin.Utils
  ( collectTopTyCons
  , collectTopTcVars
  , collectTyVars
  , skolemVarsBindFun )
import Control.Polymonad.Plugin.Constraint
  ( constraintClassType )

-- | Check as best as possible if two class instances are equal.
eqInstance :: ClsInst -> ClsInst -> Bool
eqInstance instA instB
  =  is_cls_nm instA == is_cls_nm instB
  && is_tcs instA == is_tcs instB
  && is_tvs instA == is_tvs instB
  && is_cls instA == is_cls instB
  && length (is_tys instA) == length (is_tys instB)
  && eqTypes (is_tys instA) (is_tys instB)
  && is_dfun instA == is_dfun instB
  && is_flag instA == is_flag instB
  && eqOrphan (is_orphan instA) (is_orphan instB)

-- | Check equality of two 'IsOrphan' values.
eqOrphan :: IsOrphan -> IsOrphan -> Bool
eqOrphan IsOrphan IsOrphan = True
eqOrphan (NotOrphan nameA) (NotOrphan nameB) = nameA == nameB
eqOrphan _ _ = False

-- | Trys to see if the given arguments match the class instance
--   arguments by unification. This only works if the number of arguments
--   given is equal to the arguments taken by the class the instance is of.
--   If the given arguments match the class arguments, a list with a type for
--   each free variable in the instance is returned. This list is in the same
--   order as the list of free variables that can be retrieved from the instance.
--   This function is meant for use in conjunction with 'isInstanceOf'.
matchInstanceTyVars :: [Type] -> ClsInst -> Maybe [Type]
matchInstanceTyVars instArgs inst = do
  let (instVars, _cts, _cls, tyArgs) = instanceSig inst
  -- Old Version:
  -- let instVarSet = printObjTrace $ mkVarSet instVars
  -- subst <- printObjTrace $ tcMatchTys instVarSet tyArgs instArgs
  let ctVars = filter (not . isAmbiguousTyVar) $ S.toList $ S.unions $ fmap collectTyVars instArgs
  subst <- tcUnifyTys (skolemVarsBindFun ctVars) tyArgs instArgs
  return $ substTy subst . mkTyVarTy <$> instVars

-- | Returns the type constructors of the class is instance instantiates.
instanceClassTyCon :: ClsInst -> TyCon
instanceClassTyCon inst = classTyCon $ is_cls inst

-- | Returns the arguments of the given instance head.
instanceTyArgs :: ClsInst -> [Type]
instanceTyArgs inst = args
  where (_, _, _, args) = instanceType inst

-- | Returns the class, naming type constructor and arguments of this instance.
instanceType :: ClsInst -> ([Type], Class, TyCon, [Type])
instanceType inst = (cts, cls, instanceClassTyCon inst, args)
  where (_tvs, cts, cls, args) = instanceSig inst

-- | Check if the given instance is a 'Polymonad' instance and
--   if so return the arguments types of the instance head.
instancePolymonadTyArgs :: ClsInst -> (Type, Type, Type)
instancePolymonadTyArgs inst = case instArgs of
    [t0, t1, t2] -> (t0, t1, t2)
    x -> missingCaseError "instancePolymonadTyArgs" (Just x)
  where (_, _instCls, _, instArgs) = instanceType inst

-- | Retrieve the type constructors involved in the instance head of the
--   given instance. This only selects the top level type constructors
--   (See 'collectTopTyCons').
--   /Example:/
--
--   > instance Polymonad Identity m Identity where
--   > > { Identity }
instanceTyCons :: ClsInst -> Set TyCon
instanceTyCons inst = collectTopTyCons $ instanceTyArgs inst

-- | Retrieve the type constructor variables involved in the instance head of the
--   given instance. This only selects the top level type variables (See 'collectTopTcVars').
--   /Example:/
--
--   > instance Polymonad (m a b) n Identity where
--   > > { m , n }
instanceTcVars :: ClsInst -> Set TyVar
instanceTcVars inst = collectTopTcVars $ instanceTyArgs inst

-- | Checks if the given arguments types to the free variables in the
--   class instance actually form a valid instantiation of that instance.
--   The given arguments need to match up with the list of free type variables
--   given for the class instance ('is_tvs').
--
--   The second argument can be created using 'matchInstanceTyVars'.
--
--   The first argument is a list of given and derived constraints
--   that can be used to check of they fulfill a superclass, in case
--   there are no instances that can fulfill them.
--
--   Caveat: This currently only matches class constraints, but not type
--   equality or type function constraints properly.
isInstantiatedBy :: [Ct] -> [Type] -> ClsInst -> TcPluginM (Either String Bool)
isInstantiatedBy givenCts tys inst = do
  -- Get the instance type variables and constraints (by that we know
  -- the numner of type arguments)
  let (instVars, cts, _cls, _tyArgs) = instanceSig inst -- ([TyVar], [Type], Class, [Type])
  -- Assert: We have a type for each variable in the instance.
  if length tys /= length instVars then
    return $ Left "isInstantiatedBy: Number of type arguments does not match number of variables in instance"
  else do
    -- How the instance variables for the current instance are bound.
    let varSubst = mkTopTvSubst $ zip instVars tys
    -- Split the constraints into their class and arguments.
    -- FIXME: We ignore constraints where this is not possible.
    -- Don't know if this is the right thing to do.
    let instCts = catMaybes $ fmap getClassPredTys_maybe cts
    -- Now go over each constraint and find a suitable instance.
    results <- forM instCts $ \(ctCls, ctArgs) -> do
      -- Substitute the variables to know what instance we are looking for.
      let substArgs = substTys varSubst ctArgs
      -- Get the current instance environment
      instEnvs <- getInstEnvs
      -- Look for suitable instance. Since we are not necessarily working
      -- with polymonads anymore we need to find a unique one.
      case lookupUniqueInstEnv instEnvs ctCls substArgs of
        -- No instance found, but maybe a given constraint will do the deed...
        Left _err -> do
          -- Split the given constraints into their class and arguments.
          -- FIXME: We ignore constraints where this is not possible.
          let givenInstCts = catMaybes $ fmap constraintClassType givenCts
          -- Define the predicate to check if a given constraint matches
          -- the constraint we want to fulfill.
          -- We are assuming thet there are no ambiguous type variables
          -- in a given constraint
          let eqInstCt (givenCls, givenArgs) = ctCls == givenCls && eqTypes substArgs givenArgs
          -- If we find a given constraint that fulfills the constraint we are
          -- searching for, return true, otherwise false.
          return $ Right $ isJust $ find eqInstCt givenInstCts
        -- We found one: Now we also need to check the found instance for
        -- its preconditions.
        Right (clsInst, instArgs) -> isInstantiatedBy givenCts instArgs clsInst
    return $ foldr (liftM2 (&&)) (Right True) results
