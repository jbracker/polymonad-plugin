
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
-- | Collection of the ported monad-based prelude functions for polymonads.
module Control.Polymonad.Functions
  ( (=<<)
  , (>=>), (<=<)
  , mapM, mapM_
  , forM, forM_
  , sequence, sequence_
  , when, unless
  , liftM, liftM2, liftM3
  , join, ap
  , forever
  , filterM
  , (<$!>)
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

(>=>) :: Polymonad m n p => (a -> m b) -> (b -> n c) -> a -> p c
(>=>) f g x = f x >>= g

(<=<) :: Polymonad m n p => (b -> n c) -> (a -> m b) -> a -> p c
(<=<) g f x = f x >>= g

when :: (Polymonad n Identity m, Polymonad Identity Identity m) => Bool -> n () -> m ()
when True  s = void s
when False _ = return ()

unless :: (Polymonad n Identity m, Polymonad Identity Identity m) => Bool -> n () -> m ()
unless b = when (not b)

mapM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => (a -> m b) -> [a] -> n [b]
mapM f = P.foldr k (return [])
  where
    k a r = do
      x <- f a
      xs <- r
      return (x : xs)

forM :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => [a] -> (a -> m b) -> n [b]
forM = flip mapM

sequence :: ( Polymonad Identity Identity n, Polymonad n Identity n
            , Polymonad m n n, Polymonad n n n)
         => [m b] -> n [b]
sequence = mapM id

join :: (Polymonad m n p) => m (n a) -> p a
join k = k >>= id

void :: (Polymonad m Identity n) => m a -> n ()
void = (>> return ())

mapM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
         , Polymonad m n n, Polymonad n n n)
      => (a -> m b) -> [a] -> n ()
mapM_ f = void . mapM f

forM_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
        , Polymonad m n n, Polymonad n n n)
     => [a] -> (a -> m b) -> n ()
forM_ xs = void . forM xs

sequence_ :: ( Polymonad Identity Identity n, Polymonad n Identity n
             , Polymonad m n n, Polymonad n n n)
          => [m b] -> n ()
sequence_ = void . sequence

forever :: Polymonad m m m => m a -> m b
forever ma = ma >> forever ma

filterM :: ( Polymonad n m m, Polymonad m m m
           , Polymonad Identity Identity m, Polymonad m Identity m)
        => (a -> n Bool) -> [a] -> m [a]
filterM _f [] = return []
filterM f (x : xs) = do
  keep <- f x
  if keep
    then filterM f xs >>= (return . (x :))
    else filterM f xs

liftM :: (Polymonad m Identity n) => (a -> b) -> m a -> n b
liftM f ma = ma >>= (return . f)

liftM2 :: (Polymonad m n p, Polymonad n Identity n) => (a -> b -> c) -> m a -> n b -> p c
liftM2 f ma nb = do
  a <- ma
  b <- nb
  return $ f a b

liftM3 :: (Polymonad m q q, Polymonad n p q, Polymonad p Identity p, Polymonad q Identity q)
       => (a -> b -> c -> d) -> m a -> n b -> p c -> q d
liftM3 f ma nb pc = do --ma >>= (\a -> nb >>= (\b -> pc >>= (\c -> return $ f a b c)))
  a <- ma
  b <- nb
  c <- pc
  return $ f a b c

ap :: (Polymonad m n p, Polymonad n Identity n) => m (a -> b) -> n a -> p b
ap mf na = do
  f <- mf
  a <- na
  return $ f a

(<$!>) :: (Polymonad m Identity n) => (a -> b) -> m a -> n b
f <$!> m = do
  x <- m
  let z = f x
  z `P.seq` return z

-- TODO: Generalize all the other functions in Control.Monad.
