
-- General Polymomnads ---------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RebindableSyntax #-}

-- SessionT --------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
-- Not Important
{-# LANGUAGE KindSignatures #-}


-- Plugin ----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

-- -----------------------------------------------------------------------------
module Main where

import Prelude 
  ( Num(..)
  , IO, Int, Bool(..)
  , ($), (.)
  , putStrLn
  , undefined )
import qualified Prelude as P

import Control.Polymonad

--f :: (Num a) => a -> a
--f x = x + 1

eq :: (P.Ord a) => a -> a -> Bool
eq x y = x P.== y

main :: IO ()
main = do
  -- _ <- return $ f (3 :: Int)
  return $ eq True False -- putStrLn "A Test"
  return ()
  where ((>>=), return) = ((P.>>=) :: IO a -> (a -> IO b) -> IO b, P.return)

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
{-
data SessionM (p :: SessionT) (q :: SessionT) a = SessionM a

data SessionT where
  Send :: a -> SessionT -> SessionT
  Recv :: a -> SessionT -> SessionT
  End  :: SessionT

send :: a -> SessionM (Send a q) q ()
send _ = SessionM ()

recv :: SessionM (Recv a q) q a
recv = SessionM undefined
-}
{-
instance Functor (SessionM p q) where
  fmap f (SessionM a) = SessionM (f a)

instance Unit (SessionM p p) where
  return = SessionM

instance Apply (SessionM p q) (SessionM p q) where
  app a f = f a
-}

instance Polymonad IO IO IO where
  (>>=) = (P.>>=)

instance Polymonad IO Identity IO where
  ma >>= f = ma P.>>= \a -> let Identity b = f a in P.return b

--instance Polymonad Identity Identity IO where
--  (Identity a) >>= f = let Identity b = f a in P.return b

instance Polymonad Identity IO IO where
  (Identity a) >>= f = f a


{-
instance Polymonad (SessionM p q) (SessionM q r) (SessionM p r) where
  (SessionM a) >>= f = let SessionM b = f a in SessionM b

instance Polymonad (SessionM p q) Identity (SessionM p q) where
  (SessionM a) >>= f = let Identity b = f a in SessionM b

--instance Polymonad Identity Identity (SessionM p p) where
--  (Identity a) >>= f = let Identity b = f a in SessionM b

instance Polymonad Identity (SessionM p q) (SessionM p q) where
  (Identity a) >>= f = let SessionM b = f a in SessionM b
-}
{-
testSession1 :: SessionM (Send Bool (Recv () End)) End ()
testSession1 = do
  send True -- :: SessionM (Send Bool (Recv () End)) (Recv () End) ()
  () <- recv -- :: SessionM (Recv () End) End ()
  return () -- :: SessionM End End ()
-}

{-
testSession2 :: SessionM (Send Bool (Recv () End)) End ()
testSession2 =
  (send True :: SessionM (Send Bool (Recv () End)) (Recv () End) ()) >>= \_ ->
  (recv :: SessionM (Recv () End) End ()) >>= \_ ->
  (return () :: SessionM End End ())
-} 


idOp :: a -> Identity ()
idOp _ = return ()

testId :: Identity ()
testId = do
  idOp True -- :: Identity ()
  _ <- return 'a'-- :: Identity P.Char
  return () -- :: Identity ()

{-
test :: Identity Bool
test = do
  x <- return True
  return x
-}























