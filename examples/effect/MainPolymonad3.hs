
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE UndecidableInstances #-}

-- Ignore our orphan instance in this file.
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Use the polymonad plugin.
{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

import Control.Polymonad.Prelude

import qualified Control.Effect as E
import Control.Effect ( Effect, Plus, Unit )
import Control.Effect.CounterNat

instance (Effect m, h ~ Plus m f g, E.Inv m f g) => Polymonad (m (f :: [*])) (m (g :: [*])) (m (h :: [*])) where
  (>>=) = (E.>>=)

instance (Effect m) => Polymonad Identity (m (g :: [*])) (m (g :: [*])) where
  a >>= f = f (runIdentity a)

instance ( Effect m, E.Inv m f (Unit m), f ~ Plus m f (Unit m))
        => Polymonad (m (f :: [*])) Identity (m (f :: [*])) where
  ma >>= f = ma E.>>= (E.return . runIdentity . f)

instance (Effect m, h ~ Unit m) => Polymonad Identity Identity (m (h :: [*])) where
  a >>= f = (E.return . runIdentity . f . runIdentity) a

main :: IO ()
main = do
  print $ forget (test 1 2 3 4)

specialOp :: Int -> Int -> Counter 1 Int
specialOp n m = tick (n + m)

test :: Int -> Int -> Int -> Int -> Counter 3 Int
test a b c d = do
  ab <- specialOp a b
  abc <- specialOp ab c
  specialOp abc d
