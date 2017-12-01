{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings #-}

{-|
Module      : Utils.Map
Description : Utilities for searching in maps.
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for searching in different types of maps, and providing a usefull error message if the item searched for was not present.
-}
module Utils.Map (
    IsMap(..), lookupM, lookupM',
    lookupMnoShow,
    Map, IntMap, Set, Seq
    ) where

import Data.Hashable
import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM
import Data.IntMap (IntMap)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)

import Utils.Text

-- Error function
fileName :: Text
fileName = "Utils.Map"

fatal :: (Text, Int) -> Int -> Text -> a
fatal src i s = error ("Fatal "++show i++" in " ++utxt fileName ++", arising from " ++show src ++":\n  "++utxt s)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal
-- End of error function

-- | Class to group multiple types of maps
class IsMap m k v where
    lookup' :: k -> m -> Maybe v

instance (Hashable k, Ord k) => IsMap (Hash.Map k v) k v where
    lookup' = Hash.lookup
instance IsMap (IntMap v) Int v where
    lookup' = IM.lookup
instance Ord k => IsMap (Map k v) k v where
    lookup' = Map.lookup
instance IsMap (Seq v) Int v where
    lookup' i sequ
        | i < 0 || i > Seq.length sequ = Nothing
        | otherwise = Just $ Seq.index sequ i
instance IsMap (Set v) Int v where
    lookup' i set
        | i < 0 || i >= Set.size set = Nothing
        | otherwise = Just $ Set.elemAt i set
instance IsMap [v] Int v where
    lookup' i list
        | i < 0 || i >= length list = Nothing
        | otherwise = Just $ (list !! i)

-- | Function for (fromMaybe . lookup), and print a nice error message if the lookup fails. Replacement of Map.lookup with 'guaranteed' Just.
lookupM :: (IsMap m k v, Show k, Show m) => (Text, Int) -> k -> m -> v
lookupM src key mapp = fromMaybe (fatal src 32 $ "Not a valid key: " +++ showT key +++ " in " +++ showT mapp) $ lookup' key mapp

-- | Same as lookupM, but doesn't print the entire map in the error message. Doesn't have the (Show m) constraint.
lookupMnoShow :: (IsMap m k v, Show k) => (Text, Int) -> k -> m -> v
lookupMnoShow src key mapp = fromMaybe (fatal src 36 $ "Not a valid key: " +++ showT key +++ " in map.") $ lookup' key mapp

-- | Function for a (fromMaybe . lookup) with flipped arguments, and print a nice error message if the lookup fails. Replacement of Map.!
lookupM' :: (IsMap m k v, Show k, Show m) => (Text, Int) -> m -> k -> v
lookupM' src = flip (lookupM src)
