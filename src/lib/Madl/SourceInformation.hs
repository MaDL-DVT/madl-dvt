{-|
Module      : Madl.SourceInformation
Description : Source information data structure for madl networks.
Copyright   : (c) Tessa Belder 2016

Provides a data type source information of madl networks.
-}
module Madl.SourceInformation(
    -- * Data Types
    SourceInformation(..), WithSourceInfo(..),
    -- * Construction
    emptySourceInfo,
    -- * Query
    getSourceInfo, setSourceInfo, addSourceInfo, removeSourceInfo,
    showSourcePos
    ) where

import Data.List

import Text.Parsec.Pos

import Utils.Text

-- | Source information consists of
--   1. The name of the source file
--   2. The line number of the source position
--   3. The column number of the source position
--   3. The source text
data SourceInformation = SrcInfo {
    srcFileName :: Text,
    srcFileLine :: Int,
    srcFileColumn :: Int,
    sourceText :: Text
    }
instance Show SourceInformation where
    show (SrcInfo f l c t) = intercalate ":" [utxt f, show l, show c, " " ++utxt t]

-- | Add source information to an object. @WSI v source location@ is an object @v@ parsed from @source@ obtained from @location@.
data WithSourceInfo a = WSI a String SourcePos deriving (Show)
-- | WithSourceInfo is an instance of @Functor@ such that a function is applied to the object containing source info.
instance Functor WithSourceInfo where
  fmap f (WSI v s loc) = WSI (f v) s loc

-- | Remove source information from an object.
removeSourceInfo :: WithSourceInfo a -> a
removeSourceInfo (WSI object _ _) = object

-- | Transfer source information from one object to another object
setSourceInfo :: a -> WithSourceInfo b -> WithSourceInfo a
setSourceInfo object (WSI _ s loc) = WSI object s loc

-- | Get the source information from an object
getSourceInfo :: WithSourceInfo a -> SourceInformation
getSourceInfo (WSI _ srctext srcpos) = SrcInfo {
    srcFileName = txt $ sourceName srcpos,
    srcFileLine = sourceLine srcpos,
    srcFileColumn = sourceColumn srcpos,
    sourceText = txt srctext
    }

-- | empty source information to use as a dummy --todo(tssb) remove
emptySourceInfo :: SourceInformation
emptySourceInfo = SrcInfo (txt "") 1 1 (txt "")

-- | Add source information to an object
addSourceInfo :: a -> SourceInformation -> WithSourceInfo a
addSourceInfo object (SrcInfo fname fline fcolumn srctxt) = WSI object (utxt srctxt) srcpos where
    srcpos = newPos (utxt fname) fline fcolumn

-- | Show a source position in haskell style
showSourcePos :: SourcePos -> String
showSourcePos srcpos = intercalate ":" [sourceName srcpos, show $ sourceLine srcpos, show $ sourceColumn srcpos, ""]