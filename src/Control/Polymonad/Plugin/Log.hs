
-- | Log message formatting and debuging functions.
module Control.Polymonad.Plugin.Log
  ( pprToStr, missingCaseError
  , pmErrMsg, pmDebugMsg, pmObjMsg
  , formatGroupSrcSpans
  , formatConstraint, formatSpan
  -- * Debug Functions
  , printTrace, printObjTrace, trace
  ) where

import Data.List ( groupBy, intercalate )

import Debug.Trace ( trace )

import SrcLoc
  ( SrcSpan(..)
  , srcSpanFileName_maybe
  , srcSpanStartLine, srcSpanEndLine
  , srcSpanStartCol, srcSpanEndCol )
import Outputable
  ( Outputable( ppr )
  , showSDocUnsafe )
import FastString ( unpackFS )
import TcRnTypes
  ( Ct(..), CtFlavour(..)--, CtLoc(..)
  , ctFlavour, ctPred )

import Control.Polymonad.Plugin.Utils ( removeDup )
import Control.Polymonad.Plugin.Constraint ( constraintSourceLocation )

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
-- Formatting
-- -----------------------------------------------------------------------------

-- | Format a list of source spans by grouping spans in the same file together.
formatGroupSrcSpans :: [SrcSpan] -> String
formatGroupSrcSpans spans = unwords $ fmap formatSpanGroup groupedSpans
  where
    formatSpanGroup :: [SrcSpan] -> String
    formatSpanGroup [] = ""
    formatSpanGroup ss@(s:_) =
      case srcSpanFileName_maybe s of
        Nothing -> intercalate ", " $ fmap formatSpan ss
        Just file -> unpackFS file ++ ": " ++ intercalate ", " (fmap formatSpan ss) ++ ";"

    groupedSpans = groupBy eqFileName $ removeDup spans
    eqFileName s1 s2 = srcSpanFileName_maybe s1 == srcSpanFileName_maybe s2

formatSpan :: SrcSpan -> String
formatSpan (UnhelpfulSpan str) = unpackFS str
formatSpan (RealSrcSpan s) =
  show (srcSpanStartLine s) ++ ":" ++
  show (srcSpanStartCol s) ++ "-" ++
  (if srcSpanStartLine s /= srcSpanEndLine s then show (srcSpanEndLine s) ++ ":" else "") ++
  show (srcSpanEndCol s)

formatConstraint :: Ct -> String
formatConstraint ct
  =  "["  ++ formatCtFlavour ct
  ++ "] " ++ formatCtType ct
  ++ " (" ++ formatSpan (constraintSourceLocation ct)
  ++ ", " ++ formatCtDataCon ct
  ++ ")"
  where
    formatCtDataCon :: Ct -> String
    formatCtDataCon c = case c of
      CDictCan      {} -> "CDictCan"
      CIrredEvCan   {} -> "CIrredEvCan"
      CTyEqCan      {} -> "CTyEqCan"
      CFunEqCan     {} -> "CFunEqCan"
      CNonCanonical {} -> "CNonCanonical"
      CHoleCan      {} -> "CHoleCan"
    formatCtFlavour :: Ct -> String
    formatCtFlavour c = case ctFlavour c of
      Given   -> "G"
      Wanted  -> "W"
      Derived -> "D"
    formatCtType :: Ct -> String
    formatCtType c = pprToStr $ ctPred c

-- -----------------------------------------------------------------------------
-- Debug Functions
-- -----------------------------------------------------------------------------

-- | Print the result of calling 'show' on the given object.
printTrace :: (Show a) => a -> a
printTrace x = trace (show x) x

-- | Print the result of the 'Outputable' instance of the given object.
printObjTrace :: (Outputable o) => o -> o
printObjTrace o = trace (pprToStr o) o
