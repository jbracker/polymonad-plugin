
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
{-# OPTIONS_GHC -fplugin MinimalPlugin #-}

import Prelude 
  ( String, IO, Int, Bool(..)
  , Show
  , print, fromInteger, error
  , (++), ($), (.), (<) )
import qualified Prelude as P

import Data.Functor.Identity ( Identity( Identity, runIdentity ) )

import qualified Control.Effect as E
import Control.Effect ( Effect, Plus, Unit )
import Control.Effect.Reader

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f

-- | Synonym for error.
fail :: String -> m a
fail = error

class Polymonad m n p where
  (>>=) :: m a -> (a -> n b) -> p b
  (>>) :: m a -> n b -> p b
  ma >> mb = ma >>= \_ -> mb
  
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

return :: (Polymonad Identity Identity m) => a -> m a
return x = Identity x >>= Identity

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
main = print $ runReader (flatFilter tree) (Ext (vThres :-> 3) Empty)

vThres :: Var "thres"
vThres = Var

data Tree = Leaf Int
          | Branch Tree Tree
          deriving Show

tree :: Tree
tree = Branch (Branch (Leaf 1) (Leaf 4)) (Leaf 5)

flatFilter :: Tree -> Reader '["thres" :-> Int] [Int]
{- flatFilter ( Leaf i ) = do
  thres <- ask vThres
  return (if i < thres then [] else [i]) -}
flatFilter ( Branch l r ) = do
  ls <- flatFilter l
  rs <- flatFilter r
  return (ls ++ rs)
