{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Madl2Verilog.Channel
Description : Conversion of madl channels to verilog.
Copyright   : (c) Tessa Belder 2015-2016

Contains functions to transform madl channels to verilog code.
-}
module Madl2Verilog.Channel (
    ChannelInfo,
    deriveChannelInfo,
    declareChannelFromInfo
) where

import qualified Data.HashMap as Hash
import qualified Data.Text as T

import Utils.Map
import Utils.Text

import Madl.MsgTypes
import Madl.Network

import Madl2Verilog.VerilogGen

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Channel"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

----------------
-- Data Types --
----------------

-- | All channel information necessary to generate verilog
data ChannelInfo = ChannelInfo {
    chanIdentifier :: [Text],
    chanDataSize :: Int
} deriving (Show)

-----------------------------------------------
-- Functions to derive necessary information --
-----------------------------------------------

-- | Derive all channel information necessary to generate verilog
deriveChannelInfo :: IMadlNetwork n => [Text] -> Hash.Map [Text] ColorSet -> TMadlNetwork n -> [ChannelInfo]
deriveChannelInfo prefix channelTypeMap network = [getInfo c | (n,c) <- getChannelsWithID network, internalNode n] where
    getInfo :: Channel -> ChannelInfo
    getInfo chan = ChannelInfo {
        chanIdentifier = chanIdentifier',
        chanDataSize = chanDataSize'
    } where
        chanIdentifier' = getNameList chan
        chanDataSize'= encodingSize $ lookupM (src 70) key channelTypeMap
        key = prefix ++ chanIdentifier'

    internalNode n = getMInitiator network n /= Nothing && getMTarget network n /= Nothing

-----------------------------------
-- Functions to generate Verilog --
-----------------------------------

-- | Declare channel
declareChannelFromInfo :: Bool -> ChannelInfo -> VerilogCode
declareChannelFromInfo useInterface chan = declareMadlChannel useInterface (chanDataSize chan) (T.intercalate "_" $ chanIdentifier chan)