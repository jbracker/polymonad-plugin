
-- General Polymomnads ---------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- -----------------------------------------------------------------------------

-- | Representation of polymonads in Haskell.
module Control.Polymonad
  ( Polymonad(..)
    -- Reexporting this is convenient for users, because they don't
    -- have to remember to import Data.Functor.Identity separatly anymore.
  , Identity( Identity, runIdentity )
  , fail
  , return
  ) where

import Prelude
  ( String
  , (.), ($)
  , error
  )
import qualified Prelude as P

import Data.Functor.Identity ( Identity( Identity, runIdentity ) )

-- | Synonym for error.
fail :: String -> m a
fail = error

-- -----------------------------------------------------------------------------
-- Polymonad Type Class
-- -----------------------------------------------------------------------------

-- | The polymonad type class. Instances implement a single bind-operation of
--   a polymonad. In most cases, this means several instances are required
--   to form a proper polymonad. Like a standard monad, polymonads also
--   require laws to hold. Please ensure that your instances obey the Polymonad
--   laws. The definition below gives the polymonad laws in detail.
--
--   <<docs/definition-polymonad.png>>
--
class Polymonad m n p where
  (>>=) :: m a -> (a -> n b) -> p b
  (>>) :: m a -> n b -> p b
  ma >> mb = ma >>= \_ -> mb

-- -----------------------------------------------------------------------------
-- Identity Instance
-- -----------------------------------------------------------------------------

-- | The identity polymonad.
{- We can just use the monad based derived forms instead of this.
instance Polymonad Identity Identity Identity where
  (Identity a) >>= f = f a
-}
-- -----------------------------------------------------------------------------
-- Monad Instances
-- -----------------------------------------------------------------------------

-- | Functor bind instance.
instance P.Monad f => Polymonad f Identity f where
  m >>= f = m P.>>= (P.return . runIdentity . f)

-- | Apply bind instance.
instance P.Monad f => Polymonad Identity f f where
  (Identity a) >>= f = f a

-- | Monadic bind instance.
instance P.Monad m => Polymonad m m m where
  m >>= f = m P.>>= f

-- | Return bind instance.
instance P.Monad m => Polymonad Identity Identity m where
  (Identity a) >>= f = P.return $ runIdentity $ f a

-- -----------------------------------------------------------------------------
-- Units / Returns
-- -----------------------------------------------------------------------------

-- | Polymonad return function as a handy wrapper for the return bind operation.
return :: (Polymonad Identity Identity m) => a -> m a
return x = Identity x >>= Identity

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
-- Applicative
-- -----------------------------------------------------------------------------
{-
getFun :: (Polymonad f Identity f) => f (a -> b) -> (a -> f b)
getFun ff a = ff >>= (\f -> Identity (f a))

ap :: (Polymonad f Identity f, Polymonad f f f) => f (a -> b) -> f a -> f b
ap ff fa = fa >>= \a -> getFun ff a
-}
