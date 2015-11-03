 
module Plugin ( plugin ) where

import Plugins ( Plugin( tcPlugin ), defaultPlugin )

import Outputable
  ( Outputable( ppr )
  , showSDocUnsafe )
import TcPluginM
  ( TcPluginM
  , tcPluginIO )
import TcRnTypes
  ( TcPlugin(..) 
  , TcPluginResult(..)
  , ctLocSpan, ctLoc )

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \_clOpts -> Just testPlugin }

testPlugin :: TcPlugin
testPlugin = TcPlugin
  { tcPluginInit  = return ()
  , tcPluginSolve = \() given derived wanted -> do
      printStr "CALL PLUGIN"
      printObj $ zip given (fmap ctPosition given)
      printObj $ zip derived (fmap ctPosition derived)
      printObj $ zip wanted (fmap ctPosition wanted)
      return (TcPluginOk [] [])
  , tcPluginStop  = return
  }

printObj :: Outputable o => o -> TcPluginM ()
printObj = printStr . showSDocUnsafe . ppr

printStr :: String -> TcPluginM ()
printStr = tcPluginIO . putStrLn

ctPosition = ctLocSpan . ctLoc