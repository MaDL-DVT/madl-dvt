{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-}

{-|
Module      : Madl.ToAut
Description : Transforms a madl network to aldebaran format.
Copyright   : (c) Tessa Belder 2015-

Transforms a madl network to aldebaran format.
-}
module Madl.ToAut (
    madl2aut,
    aut2file
) where

import qualified Data.Map as M

import Utils.Map
import Utils.Text

import Madl.Network

-- Error function
fileName :: Text
fileName = "Madl.ToAut"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++ utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | Transforms a madl network to aldebaran format
madl2aut :: forall a b c. (Show b, Show c, HasName b c) => c -> Network a b -> [String]
madl2aut _proxy madl = [aut_header] ++ aut_edges
    where
        aut_header =
            "des (0,"
            ++ show nr_of_transitions ++ ","
            ++ show nr_of_states ++ ")"

        nr_of_transitions = length channels
        nr_of_states = length componentIds

        aut_edges = map autEdge channels

        autEdge :: (ChannelID, (ComponentID, b, ComponentID)) -> String
        autEdge (node, (ini, chan, trgt)) =
            "(" ++ show ((lookupM (src 28) ini componentNrMap)::Int) ++ ","
             ++ label ++ ","
             ++ show ((lookupM (src 30) trgt componentNrMap)::Int) ++ ")"
            where
                label = show node ++ ":" ++ show chanName
                chanName::c = getName chan

        componentIds = getComponentIDs madl
        channels = map (\i -> (i, getChannelContext madl i)) $ getChannelIDs madl
        componentNrMap :: Map ComponentID Int
        componentNrMap = M.fromList $ zip componentIds [(0::Int)..]

-- | Prints a list of strings to a file
aut2file :: [String] -> String -> IO()
aut2file aut file = do
    writeFile file $ unlines aut