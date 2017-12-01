{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      : Madl.Base.Identifiers
Description : Identifier types for components and channels in a Madl network.
Copyright   : (c) Sanne Wouda 2015

This module defines the types 'ComponentID' and 'ChannelID'.
ComponentIDs are used to identify 'Components' of a 'MadlNetwork'.
ChannelIDs are used to identify 'Channels' of a 'MadlNetwork'.
-}
module Madl.Base.Identifiers (ComponentID(..), ChannelID(..)) where

import Data.Hashable

-- | Component identifier.
newtype ComponentID = ComponentIDImpl { runComponentID :: Int } deriving (Eq, Ord, Hashable)
-- | Channel identifier.
newtype ChannelID = ChannelIDImpl { runChannelID :: Int } deriving (Eq, Ord, Hashable)

instance Show ComponentID where
    show c = "CID" ++ show (runComponentID c)

instance Show ChannelID where
    show x = "XID" ++ show (runChannelID x)
