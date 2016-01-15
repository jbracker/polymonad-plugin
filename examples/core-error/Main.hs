
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

instance (Effect m, h ~ Plus m f g, E.Inv m f g) => Polymonad (m (f :: [*])) (m (g :: [*])) (m (h :: [*])) where
  (>>=) = (E.>>=)

instance ( Effect m, E.Inv m f (Unit m), f ~ Plus m f (Unit m))
        => Polymonad (m (f :: [*])) Identity (m (f :: [*])) where
  ma >>= f = ma E.>>= (E.return . runIdentity . f)

return :: (Polymonad Identity Identity m) => a -> m a
return x = Identity x >>= Identity

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

{-

For GHC 7.10.2:

'flatFilter' produces the following ambiguous wanted constraints:

  > Polymonad (Reader '["thres" :-> Int]) n (Reader '["thres" :-> Int]) (CNonCanonical)
  > Polymonad (Reader '["thres" :-> Int]) m n (CNonCanonical)
  > Polymonad Identity Identity m

To solve these the plugin does the following:

1. It produces two type equality constraints:
    > n ~ Identity (CNonCanonical)
    > m ~ Reader '["thres" :-> Int] (CNonCanonical)
2. As a result of these equality constraints the GHC constraint solver creates 
  the following wanted constraint:
    > Polymonad (Reader '["thres" :-> Int]) Identity (Reader '["thres" :-> Int]) (CNonCanonical)
  GHCs constraint solver can not pick an instance because several instances overlap:
    > P.Monad f => Polymonad f Identity f
    > ( Effect m, E.Inv m f (Unit m), f ~ Plus m f (Unit m)) => Polymonad (m (f :: [*])) Identity (m (f :: [*]))
  By trying to produce evidence for either of these instances the plugin determines 
  that only the second instance is actually applicable and therefore selects it and produces 
  evidence.

With this the constraints are solved and the type checking/constraint solving stage
is done. During core linting we get the following error:
> *** Core Lint errors : in result of Simplifier ***
> <no location info>: Warning:
>     [RHS of ds_a66V :: (Set '["thres" :-> Int], Set (Unit Reader))]
>     Bad getNth:
>       Nth:0
>         (Nth:2
>            (Sub (Sym (TFCo:R:Inv[]Readerfg[0] <'["thres" :-> Int]>_N <'[]>_N))
>             ; (Inv
>                  <Reader>_N <'["thres" :-> Int]>_N (Sym TFCo:R:Unit[]Reader[0]))_R
>             ; Sub
>                 (TFCo:R:Inv[]Readerfg[0] <'["thres" :-> Int]>_N <Unit Reader>_N)))
>       Split '["thres" :-> Int] '[] (Union '["thres" :-> Int] '[])
>       Split
>         '["thres" :-> Int]
>         (Unit Reader)
>         (Union '["thres" :-> Int] (Unit Reader))
As can be seen in the plugin [Check for 'Nth' constructor] the evidence produced by the plugin does
not contain the 'Nth' constructor for coercions/evidence anywhere. Thus, the 
produced evidence seems to trigger GHC to produce these 'bad' coercions/evidence 
somewhere.

-}