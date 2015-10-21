
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
--{-# LANGUAGE ConstraintKinds #-}

module Main ( main ) where

import Prelude
import qualified Prelude as P
import Control.Effect
import qualified Control.Effect as E
import Control.Effect.State
  ( State
  , Var(..), Eff(..)
  , (:->)(..), (:!)(..)
  , get, put )

ifThenElse True  t e = t
ifThenElse False t e = e

main :: IO ()
main = do
  return ()
  where --(>>=) = (P.>>=)
        return = P.return

data Tree = Leaf Int
          | Branch Tree Tree

leavesV  = Var :: (Var "leaves")
sumV     = Var :: (Var "sum")
flattenV = Var :: (Var "flatten")

update :: Var n -> (a -> a) -> State '[n :-> a :! 'RW] ()
update v f = do
  x <- get v
  _ <- return 2
  --let fx = f x
  put v (f x) --fx
  -- get v >>= \x -> return (f x) >>= \fx -> put v fx

  -- return fx
  where (>>=) = (E.>>=)
        --(>>) = (E.>>)
        return = E.return
        fail = E.fail

process :: Tree
        -> State '[ "flatten" :-> Bool :! 'R
                  , "leaves"  :-> Int  :! 'RW
                  , "sum"     :-> Int  :! 'RW
                  ] (Either Tree [Int])
process (Leaf i) = {-do
  update leavesV (+ 1)
  update sumV (+ i)
  flatten <- get flattenV
  if flatten
    then return $ Right [i]
    else return $ Left $ Leaf i-}
  update leavesV (+ 1)
  >>
  update sumV (+ i)
  >>
  get flattenV
  >>= \flatten ->
  if flatten
    then return $ Right [i]
    else return $ Left $ Leaf i
  where (>>=) = (E.>>=)
        (>>) = (E.>>)
        return = E.return
        fail = E.fail

{-
process (Branch tl tr) = do
  eitherL <- process tl
  eitherR <- process tr
  case (eitherL, eitherR) of
    (Left  l, Left  r) -> return $ Left  $ Branch l r
    (Right l, Right r) -> return $ Right $ l ++ r
  where (>>=) = (E.>>=)
        --(>>) = (E.>>)
        return = E.return
        fail = E.fail
-}
