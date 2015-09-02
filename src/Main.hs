
-- General Polymonads ----------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- SessionT --------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
-- Not Important
{-# LANGUAGE KindSignatures #-}


-- Plugin ----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

-- -----------------------------------------------------------------------------
module Main where

import qualified Prelude as P

import Control.Polymonad.Prelude
import Control.Polymonad.Hoare


--f :: (Num a) => a -> a
--f x = x + 1

eq :: (Ord a) => a -> a -> Bool
eq x y = x == y

main :: IO ()
main = P.return () {- do
  -- _ <- return $ f (3 :: Int)
  return $ eq True False -- putStrLn "A Test"
  return ()
  where ((>>=), return) = ((P.>>=) :: IO a -> (a -> IO b) -> IO b, P.return)
  -}

-- -----------------------------------------------------------------------------
-- IST-Polymonad
-- -----------------------------------------------------------------------------
{-
data IST p l a = IST a

instance Polymonad (IST p1 l1) (IST p2 l2) (IST p3 l3) where
  (IST a) >>= f = let IST b = f a in IST b
-}
-- -----------------------------------------------------------------------------
-- Session-Polymonad
-- -----------------------------------------------------------------------------

data SessionM (p :: SessionT) (q :: SessionT) a = SessionM a

data SessionT where
  Send :: a -> SessionT -> SessionT
  Recv :: a -> SessionT -> SessionT
  End  :: SessionT

send :: a -> SessionM (Send a q) q ()
send _ = SessionM ()

recv :: SessionM (Recv a q) q a
recv = SessionM undefined

instance HoareMonad SessionM where
  hoareBind (SessionM a) f = let SessionM b = f a in SessionM b
  hoareRet a = SessionM a

{-
instance Polymonad IO IO IO where
  (>>=) = (P.>>=)

instance Polymonad IO Identity IO where
  ma >>= f = ma P.>>= \a -> let Identity b = f a in P.return b

--instance Polymonad Identity Identity IO where
--  (Identity a) >>= f = let Identity b = f a in P.return b

instance Polymonad Identity IO IO where
  (Identity a) >>= f = f a
-}


{- TODO: Temporary while writing library -}
idOp :: a -> Identity ()
idOp _ = return ()

testId :: P.Maybe ()
testId = do
  idOp True -- :: Identity ()
  _ <- return 'a'-- :: Identity P.Char
  return () -- :: Identity ()


test1 :: P.Maybe [Int]
test1 = do
  i <- P.Just 300
  j <- P.Just $ do
    k <- [1,2,3]
    l <- [4,5,6]
    return $ k * l
  return $ j P.++ [400,500,i]

test2 :: (Polymonad m n p, Polymonad n Identity n) => (a -> b -> Int -> c) -> m a -> n b -> p [(c, Int)]
test2 f ma nb = do
  a <- ma
  b <- nb
  return $ do
    i <- [1..3]
    return (f a b i, i)
