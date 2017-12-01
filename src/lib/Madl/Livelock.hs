{-# LANGUAGE OverloadedStrings #-}
module Madl.Livelock (
    findPossibleLivelocks
) where

import Control.Monad
import Utils.Text

import Madl.MsgTypes
import Madl.Network

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in ring detection:\n  "++ utxt s)

-- Find first possible livelock or Nothing if livelock-free
findPossibleLivelocks :: XColoredNetwork c -> Maybe [(ChannelID, ColorSet)]
findPossibleLivelocks net = msum $ map startSearch sources where
    sources = map (sourceOutChannel net) (getAllSourceIDs net)
    startSearch s = searchLivelock net [] (getColorSet net s) s

-- Algorithm 2 from thesis, DFS color propagation from sources
-- If lasso is found, possible livelock was found.
-- Either returns first livelock found or Nothing
searchLivelock :: XColoredNetwork c -> [(ChannelID, ColorSet)] -> ColorSet -> ChannelID -> Maybe [(ChannelID, ColorSet)]
searchLivelock net seen color inChannel = if emptyColorSet color then Nothing 
    else case alreadySeen of
        Just a -> Just a
        Nothing -> case targetComp of
            -- If a sink is reached we successfully ended the flow.
            Sink _ -> Nothing
            DeadSink _ -> Nothing

            -- Propagate search over elements
            ControlJoin _ -> if inChannel == head inChannels
                then searchLivelock net newSeen color outChan
                else Nothing
            Cut _ -> searchLivelock net newSeen color outChan
            Fork _ -> msum $ map (searchLivelock net newSeen color) outChannels
            Function _ typeFunction _ -> searchLivelock net newSeen (transformColor typeFunction) outChan
            GuardQueue _ _ -> searchLivelock net newSeen color outChan
            LoadBalancer _ -> msum $ map (searchLivelock net newSeen color) outChannels
            Merge _ -> searchLivelock net newSeen color outChan
            Queue _ _ -> searchLivelock net newSeen color outChan
            Switch _ _ -> msum $ map (\c -> searchLivelock net newSeen (typeIntersection color (chanColors c)) c) outChannels
            Vars _ -> searchLivelock net newSeen color outChan

            -- Not supported (for now)
            FControlJoin _ _ -> Nothing
            Match _ _ -> Nothing
            MultiMatch _ _ -> Nothing
            Automaton _ _ _ _ _-> Nothing
            Joitch _ _ -> Nothing

            -- We propagate with the data flow starting from sources, we should not somehow reach sources again.
            Source _ _ -> fatal 26 "Livelock detection should not reach sources."
            PatientSource _ _ -> fatal 27 "Livelock detection should not reach sources."

        where
            (target, _) = getTargetWithPort net inChannel
            targetComp = getComponent net target
            outChan = head outChannels
            outChannels = getOutChannels net target
            inChannels = getInChannels net target
            chanColors = getColorSet net

            -- There exists an entry in the seen list that has the same channel and has at least one intersecting color
            alreadySeen = findOverlap seen inChannel color
            newSeen = (inChannel, color):seen
            transformColor :: MFunctionDisj -> ColorSet
            transformColor f = case resultingType (makeArguments [color]) (XAppliedTo f [XVar 0]) of
                Right err -> fatal 67 (showT err)
                Left (newColor) -> newColor

sourceOutChannel :: XColoredNetwork c -> ComponentID -> ChannelID
sourceOutChannel net sourceID = out where
    [out] = getOutChannels net sourceID

-- Check if (channel, color) is in seen list
findOverlap :: [(ChannelID, ColorSet)] -> ChannelID -> ColorSet -> Maybe [(ChannelID, ColorSet)]
findOverlap seen channel color = helper [] seen where
    doOverlap c c' = not $ emptyColorSet $ typeIntersection c c'
    helper checked list = case list of
        [] -> Nothing
        (chan, cCol):xs -> if (channel == chan) && (doOverlap color cCol)
            then Just $ (chan, cCol):(checked++[(channel, color)])
            else helper ((chan, cCol):checked) xs
