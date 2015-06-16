
-- General Polymomnads ---------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
--{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}

-- -----------------------------------------------------------------------------

module Control.Polymonad
  ( Identity(..)
  , fail
  , Polymonad(..)
  --, Unit(..)
  --, Apply(..)
  --, return, app, pmap
  , Functor(..)
  ) where

import Prelude 
  ( error, undefined
  , Functor(..)
  , (.)
  , Bool(..)
  )
import qualified Prelude as P

import Data.Functor.Identity ( Identity( Identity, runIdentity ) )

fail = error

-- -----------------------------------------------------------------------------
-- Polymonads
-- -----------------------------------------------------------------------------

class Polymonad m n p where
  (>>=) :: m a -> (a -> n b) -> p b
  (>>) :: m a -> n b -> p b
  ma >> mb = ma >>= \_ -> mb

instance Polymonad Identity Identity Identity where
  (Identity a) >>= f = f a

{-
-- Prelude instance for backwards compatability.
instance P.Monad m => Polymonad m m m where
  (>>=) = (P.>>=)
-}

-- -----------------------------------------------------------------------------
-- Functors
-- -----------------------------------------------------------------------------
{-
pmap :: (Polymonad f Identity f) => (a -> b) -> f a -> f b
pmap f fa = fa >>= (Identity . f)
-}


-- For now remove these additional classes 
-- and instances to simplify the plugin.
-- We want it this way around to be backwards compatible.
instance Functor f => Polymonad f Identity f where
  m >>= f = fmap (runIdentity . f) m
instance Polymonad Identity f f where
  (Identity a) >>= f = f a
  
instance P.Monad m => Polymonad m m m where
  m >>= f = m P.>>= f

instance P.Monad m => Polymonad Identity Identity m where
  (Identity a) >>= f = let Identity b = f a in P.return b


{-
-- The other way around would also work.
instance (Polymonad f Identity f) => Functor f where
  fmap f m = m >>= (Identity . f)
  -}
{-
instance (Polymonad Identity Identity m , Polymonad m m m) => P.Monad m where
  (>>=) = (>>=)
  return x = Identity x >>= Identity
  -}
{-
instance P.Monad m => Polymonad m m m where
  (>>=) = (P.>>=)

instance P.Monad m => Polymonad Identity Identity m where
  (Identity a) >>= f = let Identity b = f a in P.return b
  -}
-- -----------------------------------------------------------------------------
-- Units / Returns
-- -----------------------------------------------------------------------------
{-
return :: (Polymonad Identity Identity m) => a -> m a
return x = Identity x >>= Identity
-}
{- For now remove these additional classes 
-- and instances to simplify the plugin.
class Unit m where
  return :: a -> m a

-- We want the chain of instances for backwards compatability.
-- P.Applicative would be enough for this, once it is an actual 
-- dependency of the P.Monad class.
instance P.Monad m => Unit m where
  return = P.return

instance Unit m => Polymonad Identity Identity m where
  (Identity a) >>= f = (return . runIdentity . f) a
-}

{- The other way around would also work.
instance (Polymonad Identity Identity p) => Unit p where
  -- (Polymonad Identity Identity p) => a -> p a
  return x = Identity x >>= Identity
-}

-- -----------------------------------------------------------------------------
-- Apply
-- -----------------------------------------------------------------------------
{-
app :: (Polymonad Identity m p) => a -> (a -> m b) -> p b
app x f = Identity x >>= f
-}
{- For now remove these additional classes 
-- and instances to simplify the plugin.
class Apply m p where
  app :: a -> (a -> m b) -> p b

instance Apply m p => Polymonad Identity m p where
  (Identity x) >>= f = x `app` f
-}

{- The other way around would also work
instance Polymonad Identity m p => Apply m p where
  app x f = Identity x >>= f
-}

-- -----------------------------------------------------------------------------
-- Applicative
-- -----------------------------------------------------------------------------
{-
getFun :: (Polymonad f Identity f) => f (a -> b) -> (a -> f b)
getFun ff a = ff >>= (\f -> Identity (f a))

ap :: (Polymonad f Identity f, Polymonad f f f) => f (a -> b) -> f a -> f b
ap ff fa = fa >>= \a -> getFun ff a
-}
-- -----------------------------------------------------------------------------
-- Experiments
-- -----------------------------------------------------------------------------

{-
class 
  ( Unit m, Unit n, Unit p
  , Apply m n, Apply n p, Apply m p
  , Functor m, Functor n, Functor p
  ) => XPolymonad m n p where
-}
