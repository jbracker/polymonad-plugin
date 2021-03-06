
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RebindableSyntax #-}

-- Ignore our orphan instance in this file.
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Use the polymonad plugin.
{-# OPTIONS_GHC -fplugin Control.Polymonad.Plugin #-}

-- Remove this so compilation creates a proper executable.
--module MainPolymonad ( main ) where

import Control.Polymonad.Prelude
import Control.Polymonad.Hoare ( HoareMonad(..) )


import Control.Monad.Indexed
  ( IxPointed(..), (>>>=) )

import Control.Concurrent
  ( forkIO )

import Control.Concurrent.SimpleSession.Implicit
  ( Session, Cap
  , io, send, recv, close, sel1, sel2, zero, offer, enter
  , newRendezvous, accept, request )
import Control.Concurrent.SimpleSession.SessionTypes
  ( Var, Eps
  , (:&:), (:+:), (:!:), (:?:)
  , Z )

instance HoareMonad Session where
  hoareRet = ireturn
  hoareBind = (>>>=)

type Ping = Eps :+: (String :!: String :?: Var Z)
type Pong = Eps :&: (String :?: String :!: Var Z)

main :: IO ()
main = do
  rv <- newRendezvous
  _ <- forkIO $ accept rv
              $ enter >> ping 3
  request rv $ enter >> pong

ping :: Int -> Session (Cap (Ping, ()) Ping) () ()
ping 0 = do
    sel1; close
ping n = do
    sel2; send "Ping"
    rsp <- recv
    io $ putStrLn rsp
    zero; ping (n - 1)

pong :: Session (Cap (Pong, ()) Pong) () ()
pong = offer close $ do
    rsp <- recv
    io $ putStrLn rsp
    send "Pong"
    zero; pong

