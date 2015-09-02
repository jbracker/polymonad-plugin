
-- Needed to specify constraint context that contain 'Identity'.
{-# LANGUAGE FlexibleContexts #-}
-- Needed to use polymonads instead of standard monads.
{-# LANGUAGE RebindableSyntax #-}
-- To defer errors of ambiguity in utility function to their use-sight.
--{-# LANGUAGE AllowAmbiguousTypes #-}
-- Not sure if this is needed yet. Sometimes useful.
--{-# LANGUAGE ScopedTypeVariables #-}

-- Plugin ----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

-- -----------------------------------------------------------------------------
-- | Collection of the ported monad-based functions for polymonads.
--   For a more detailed description of these functions refer to
--   the 'Control.Monad' module.
--
--   Most functions are generalized to suite the setting of polymonads better.
--
--   This module is thought as a replacement for the "Control.Monad" module.
module Control.Polymonad.Functions
  ( -- * @Control.Monad@ replacements
    -- ** Basic @Polymonad@ functions
    mapM, mapM_
  , forM, forM_
  , sequence, sequence_
  , (=<<)
  , (>=>), (<=<)
  , forever, void
    -- ** Generalizations of list functions
  , join
  -- , msum, mfilter -- FIXME: Requires an alternative of 'MonadPlus'.
  , filterM
  , mapAndUnzipM
  , zipWithM, zipWithM_
  , foldM, foldM_
  , replicateM, replicateM_
    -- ** Conditional execution of monadic expressions
  -- , guard -- FIXME: Requires an alternative of 'Alternative'
  , when, unless
    -- ** Monadic lifting operators
  , liftM, liftM2, liftM3
  -- , liftM4, liftM5 -- TODO
  , ap
    -- ** Strict monadic functions
  , (<$!>)
    -- * Additional generalized polymonad functions
  , (<$>)
  ) where

import qualified Prelude as P
import Prelude
  ( Bool(..)
  , (.), ($)
  , id
  --, const
  , flip
  --, otherwise
  , not )
--import Data.Foldable ( Foldable(..) )

import Control.Polymonad

infixr 1 =<<
infixr 1 >=>
infixr 1 <=<

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _f = t
ifThenElse False _t f = f

-- | Same as '>>=', but with the arguments interchanged.
(=<<) :: Polymonad m n p => (a -> n b) -> m a -> p b
f =<< ma = ma >>= f

-- | Left-to-right Kleisli composition.
(>=>) :: Polymonad m n p => (a -> m b) -> (b -> n c) -> a -> p c
(>=>) f g x = f x >>= g

-- | Right-to-left Kleisli composition.
(<=<) :: Polymonad m n p => (b -> n c) -> (a -> m b) -> a -> p c
(<=<) g f x = f x >>= g

-- | When the condition is true do the given action.
when :: (Polymonad n Identity m, Polymonad Identity Identity m) => Bool -> n () -> m ()
when True  s = void s
when False _ = return ()

-- | When the condition is false do the given action.
unless :: (Polymonad n Identity m, Polymonad Identity Identity m) => Bool -> n () -> m ()
unless b = when (not b)

-- | Map the given function on each element of the list and collect the results.
mapM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => (a -> m b) -> [a] -> n [b]
mapM f = P.foldr k (return [])
  where
    k a r = do
      x <- f a
      xs <- r
      return (x : xs)

-- | 'flip'ped version of 'mapM'.
forM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => [a] -> (a -> m b) -> n [b]
forM = flip mapM

-- | Execute all computations in the list in order and returns the list of results.
sequence :: ( Polymonad Identity Identity n, Polymonad n Identity n
            , Polymonad m n n, Polymonad n n n)
         => [m b] -> n [b]
sequence = mapM id

-- | Monadic join operation.
join :: (Polymonad m n p) => m (n a) -> p a
join k = k >>= id

-- | Ignore the result of a computation.
void :: (Polymonad m Identity n) => m a -> n ()
void = (>> return ())

-- | 'mapM' ignoring the result.
mapM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
         , Polymonad m n n, Polymonad n n n)
      => (a -> m b) -> [a] -> n ()
mapM_ f = void . mapM f

-- | 'forM' ignoring the result.
forM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => [a] -> (a -> m b) -> n ()
forM_ xs = void . forM xs

-- | 'sequence' ignoring the result.
sequence_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
             , Polymonad m n n, Polymonad n n n)
          => [m b] -> n ()
sequence_ = void . sequence

-- | Execute the given computation repeatedly forever.
forever :: Polymonad m m m => m a -> m b
forever ma = ma >> forever ma

-- | Like @filter@ but with a monadic predicate and result.
filterM :: ( Polymonad n m m, Polymonad m m m
           , Polymonad Identity Identity m, Polymonad m Identity m)
        => (a -> n Bool) -> [a] -> m [a]
filterM _f [] = return []
filterM f (x : xs) = do
  keep <- f x
  if keep
    then filterM f xs >>= (return . (x :))
    else filterM f xs

mapAndUnzipM :: ( Polymonad Identity Identity n, Polymonad n Identity n
                , Polymonad m n n, Polymonad n n n)
             => (a -> m (b, c)) -> [a] -> n ([b], [c])
mapAndUnzipM f xs = liftM P.unzip (forM xs f)

zipWithM :: ( Polymonad Identity Identity n, Polymonad n Identity n
            , Polymonad m n n, Polymonad n n n)
         => (a -> b -> m c) -> [a] -> [b] -> n [c]
zipWithM f xs ys = sequence $ P.zipWith f xs ys

zipWithM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
             , Polymonad m n n, Polymonad n n n)
          => (a -> b -> m c) -> [a] -> [b] -> n ()
zipWithM_ f xs ys = void $ zipWithM f xs ys

foldM :: ( P.Foldable t
         , Polymonad Identity Identity m, Polymonad m Identity m
         , Polymonad m m m)
      => (b -> a -> m b) -> b -> t a -> m b
foldM f e = P.foldl f'(return e)
  where f' mb a = mb >>= \b -> f b a
        -- :: (Polymonad m m m) => m b -> a -> m b

foldM_ :: ( P.Foldable t
          , Polymonad Identity Identity m, Polymonad m Identity m
          , Polymonad m m m)
       => (b -> a -> m b) -> b -> t a -> m ()
foldM_ f e = void . foldM f e

replicateM :: (Polymonad m Identity n) => Int -> m a -> n [a]
replicateM n _ma | n <= 0 = return []
replicateM n ma = do
  a <- ma
  as <- replicateM (n - 1) ma
  return $ a : as

replicateM_ :: ()
replicateM_ = P.undefined

-- | Make arguments and result of a pure function monadic.
liftM :: (Polymonad m Identity n) => (a -> b) -> m a -> n b
liftM f ma = ma >>= (return . f)

-- | Make arguments and result of a pure function monadic.
liftM2 :: (Polymonad m n p, Polymonad n Identity n) => (a -> b -> c) -> m a -> n b -> p c
liftM2 f ma nb = do
  a <- ma
  b <- nb
  return $ f a b

-- | Make arguments and result of a pure function monadic.
liftM3 :: (Polymonad m q q, Polymonad n p q, Polymonad p Identity p, Polymonad q Identity q)
       => (a -> b -> c -> d) -> m a -> n b -> p c -> q d
liftM3 f ma nb pc = do --ma >>= (\a -> nb >>= (\b -> pc >>= (\c -> return $ f a b c)))
  a <- ma
  b <- nb
  c <- pc
  return $ f a b c

-- | Make the resulting function a monadic function.
ap :: (Polymonad m n p, Polymonad n Identity n) => m (a -> b) -> n a -> p b
ap mf na = do
  f <- mf
  a <- na
  return $ f a

-- | Apply the given function to the result of a computation.
(<$>) :: (Polymonad m Identity n) => (a -> b) -> m a -> n b
f <$> m = do
  x <- m
  return (f x)

-- | Strict version of '<$>'.
(<$!>) :: (Polymonad m Identity n) => (a -> b) -> m a -> n b
f <$!> m = do
  x <- m
  let z = f x
  z `P.seq` return z

-- TODO: Generalize all the other functions in Control.Monad.
