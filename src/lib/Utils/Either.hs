{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Utils.Either
Description : Utilities for the @Either@ type
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions to work with the type @Either@.
-}
module Utils.Either (
    module Data.Either,
    module Data.Either.Unwrap,
    either2, mapBoth2
) where

import Data.Either
import Data.Either.Unwrap hiding (isLeft, isRight)

import Utils.Text

-- Error function
fileName :: Text
fileName = "Utils.Either"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++ utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | Apply either to 2 arguments.
either2 :: (a -> a' -> c) -> (b -> b' -> c) -> Either a b -> Either a' b' -> c
either2 f _g (Left x) (Left y) = f x y
either2 _f g (Right x) (Right y) = g x y
either2 _ _ _ _ = fatal 32 "Eithers do not match"

-- | Apply mapBoth to 2 arguments.
mapBoth2 :: (a -> a' -> c) -> (b -> b' -> d) -> Either a b -> Either a' b' -> Either c d
mapBoth2 f _g (Left x) (Left y) = Left $ f x y
mapBoth2 _f g (Right x) (Right y) = Right $ g x y
mapBoth2 _ _ _ _ = fatal 38 "Eithers do not match"
