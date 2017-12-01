{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Utils.Text
Description : Utilities for working with the @Text@ type
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for working with the @Text@ type.
-}
module Utils.Text (
    txt, utxt,
    (+++), (.>),
    showT, readT, concatMapT,
    Text
) where

import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import Data.Text (Text)

-- Error function
fileName :: Text
fileName = "Utils.Text"

fatal :: (Text, Int) -> Int -> Text -> a
fatal src i s = error ("Fatal "++show i++" in " ++utxt fileName ++", arising from " ++show src ++":\n  "++utxt s)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal
-- End of error function

-- | Show an object as Text
showT :: (Show a) => a -> Text
showT = T.pack . show

-- | Read a Text
readT :: (Read a) => (Text, Int) -> Text -> a
readT src t = case listToMaybe $ reads $ T.unpack t of
    Nothing -> fatal src 29 "Read: no parse"
    Just (x, _) -> x

-- | Append Text using infix
(+++) :: Text -> Text -> Text
(+++) = T.append

-- | Shortcut to create Text
txt :: String -> Text
txt = T.pack

-- | Shortcut to unpack Text
utxt :: Text -> String
utxt = T.unpack

-- | Prefix text with underscore in between
(.>) :: Text -> Text -> Text
(.>) prefix t = prefix +++ T.cons '_' t

-- | Map a function to a list of object to obtain a list of @Text@s, and concatenate the result.
concatMapT :: (a -> Text) -> [a] -> Text
concatMapT f = T.concat . map f