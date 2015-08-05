
-- | Log message formatting and debuging functions.
module Control.Polymonad.Plugin.Log
  ( pprToStr, missingCaseError
  , pmErrMsg, pmDebugMsg, pmObjMsg
  -- * Debug Functions
  , printTrace, printObjTrace
  ) where

import Debug.Trace ( trace )

import Outputable
  ( Outputable( ppr )
  , showSDocUnsafe )

-- | Convert some generic outputable to a string (Unsafe).
pprToStr :: Outputable o => o -> String
pprToStr = showSDocUnsafe . ppr

-- | @prefixMsg prefix msg@ prefixes a message with the given string.
prefixMsg :: String -> String -> String
prefixMsg prefix = unlines . fmap (prefix ++) . lines

-- | Message prefix of the polymonad plugin.
pluginMsgPrefix :: String
pluginMsgPrefix = "[PM]"

-- | Prefix a message with the error prefix.
pmErrMsg :: String -> String
pmErrMsg = prefixMsg $ pluginMsgPrefix ++ " ERROR: "

-- | Prefix a message with the standard debug prefix.
pmDebugMsg :: String -> String
pmDebugMsg = prefixMsg $ pluginMsgPrefix ++ " "

-- | Prefix a message with the debug prefix and a note that this is a
--   printed object.
pmObjMsg :: String -> String
pmObjMsg = prefixMsg $ pluginMsgPrefix ++ "> "

-- | Used to emit an error with a message describing the missing case.
--   The string is the function that misses the case and the 'Outputable'
--   is the object being matched.
missingCaseError :: (Outputable o) => String -> Maybe o -> a
missingCaseError funName (Just val) = error $ "Missing case in '" ++ funName ++ "' for " ++ pprToStr val
missingCaseError funName Nothing    = error $ "Missing case in '" ++ funName ++ "'"

-- -----------------------------------------------------------------------------
-- Debug Functions
-- -----------------------------------------------------------------------------

-- | Print the result of calling 'show' on the given object.
printTrace :: (Show a) => a -> a
printTrace x = trace (show x) x

-- | Print the result of the 'Outputable' instance of the given object.
printObjTrace :: (Outputable o) => o -> o
printObjTrace o = trace (pprToStr o) o
