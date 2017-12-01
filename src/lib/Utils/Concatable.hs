{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, FlexibleInstances #-}

{-|
Module      : Utils.Concatable
Description : Utilities for instances of both @Monoid@ and @IsString@
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions to transform instance of both @Monoid@ and @IsString@. It also contains the typeclass 'WithApplicative',
which is an instance of @Monoid@ and @IsString@ such that appending something to an empty instance always yields an empty instance.
-}
module Utils.Concatable (
    IsString, Monoid, (<>),
    WithApplicative(..), show,
    unwords, unlines, intercalate
    ) where

import Prelude (($), (.))
import Control.Applicative
import Control.Monad
import qualified Text.Show as S
import Data.List (intersperse)
import Data.Monoid
import Data.String (IsString, fromString)

-- | @show@ function to any type in the typeclass 'IsString'
show :: (S.Show a, IsString b) => a -> b
show = fromString . S.show

-- | @unwords@ function for Monoids
unwords :: (IsString a, Monoid a) => [a] -> a
unwords = intercalate " "

-- | @unlines@ function for monoids
unlines :: (IsString a, Monoid a) => [a] -> a
unlines = intercalate "\n"

-- | @intercalate@ function for monoids
intercalate :: Monoid a => a -> [a] -> a
intercalate x xs = mconcat $ intersperse x xs

-- | Takes a type @f@, and applies it to another type @a@. If @f@ is an instance of the typeclass @Applicative@,
-- and @a@ is a @Monoid@, then @WithApplicative f a@ is a @Monoid@ such that appending something to an empty instance always yields an empty instance.
newtype WithApplicative f a = WA {runWA :: f a} deriving S.Show

instance Functor f => Functor (WithApplicative f) where
    fmap f = WA . fmap f . runWA
instance Applicative f => Applicative (WithApplicative f) where
    pure = WA . pure
    (<*>) (WA f) = WA . (f <*>) . runWA
instance Monad f => Monad (WithApplicative f) where
    (>>=) (WA a) g = WA $ a >>= (runWA . g)
instance (Applicative f, Monoid a) => Monoid (WithApplicative f a) where
    mempty = pure mempty
    mappend a b = mappend <$> a <*> b

instance (Applicative f, IsString a) => IsString (WithApplicative f a) where
    fromString = pure . fromString
