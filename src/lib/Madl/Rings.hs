{-# LANGUAGE OverloadedStrings #-}
--{-# OPTIONS_GHC -Wwarn #-}
module Madl.Rings (Ring(..), findRings, combineRings, showRing, getRingInvariants) where

import qualified Data.Map as Map
import Data.List

import Utils.Text
import Utils.Map

import Madl.Network
import Madl.MsgTypes
import Madl.Invariants

data Ring = Ring{
    ringChannels :: [ChannelID],
    ringIns :: [ChannelID],
    ringOuts :: [ChannelID],
    ringColor :: ColorSet
}

-- Error function
fileName :: Text
fileName = "Rings"

src :: Int -> (Text, Int)
src i = (fileName, i)

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in ring detection:\n  "++ utxt s)

findRings :: XColoredNetwork c -> [Ring]
findRings net = nub $ concat $ map (findRingsStart net) entryPoints
    where
        entryPoints = getEntryPoints net

findRingsStart :: XColoredNetwork c -> ComponentID -> [Ring]
findRingsStart net cID = concat $ map (\c -> concat $ map (\cs -> findRingsRecurse net c cs (cID, cs) [] [] []) (splitColors $ getColorSet net c)) outChans
    where 
        outChans = getOutChannels net cID
        splitColors cs = map toColorSet (getColors cs)

-- DFS color propagation, algorithm 1 in thesis.
findRingsRecurse :: XColoredNetwork c -> ChannelID -> ColorSet -> (ComponentID, ColorSet) -> [ChannelID] -> [ChannelID] -> [ChannelID] -> [Ring]
findRingsRecurse net inChan color start@(startC, startCol) ring ins outs = if (emptyColorSet color) || elem inChan ring then [] else
    if target == startC && subTypeOf color startCol then
        [Ring (reverse $ inChan:ring) (filterByColor (ins ++ inChannels')) (filterByColor outs) color]
    else
        case targetComp of
            Queue _ _ -> findRingsRecurse net outChan color start newRing ins outs
            Function _ typeFunction _ -> findRingsRecurse net outChan (transformColor typeFunction) start newRing ins outs
            Merge _ -> findRingsRecurse net outChan color start newRing (ins ++ inChannels') outs
            Switch _ _ -> concat $ map (\c -> findRingsRecurse net c (typeIntersection color (chanColors c)) start newRing ins outs) outChannels
            ControlJoin _ -> if inChan == head inChannels 
                then findRingsRecurse net outChan color start newRing ins outs 
                else []
            LoadBalancer _ -> concat $ map (\c -> findRingsRecurse net c color start newRing ins (outs ++ outChannels' c)) outChannels
            Fork _ -> concat $ map (\c -> findRingsRecurse net c color start newRing ins outs) outChannels
            GuardQueue _ _ -> findRingsRecurse net outChan color start newRing (ins ++ inChannels') outs
            Vars _ -> findRingsRecurse net outChan color start newRing ins outs -- Just propagate everything
            Cut _ -> findRingsRecurse net outChan color start newRing ins outs -- Just propagate everything
            Sink _ -> [] -- No rings from sinks so return empty set
            DeadSink _ -> [] -- No rings from sinks so return empty set

            -- Unsupported - stop ring detection here
            FControlJoin _ _ -> []
            Match _ _ -> []
            MultiMatch _ _ -> []
            Automaton _ _ _ _ _-> []
            Joitch _ _ -> []

            -- Errors
            Source _ _ -> fatal 34 "Ring detection should not reach sources"
            PatientSource _ _ -> fatal 60 "Ring detection should not reach sources"
    where
        target = getTarget net inChan
        targetComp = getComponent net target
        outChan = head outChannels
        outChannels = getOutChannels net target
        outChannels' o = filter (\c -> c /= o) outChannels
        inChannels = getInChannels net target
        inChannels' = filter (\c -> c /= inChan) inChannels
        newRing = inChan:ring
        chanColors c = getColorSet net c
        filterByColor cs = filter (\c -> not $ emptyColorSet $ typeIntersection color (chanColors c)) cs

        transformColor :: MFunctionDisj -> ColorSet
        transformColor f = case resultingType (makeArguments [color]) (XAppliedTo f [XVar 0]) of
            Right err -> fatal 67 (showT err)
            Left (newColor) -> newColor

-- Find all entry points in a list of components
getEntryPoints :: XColoredNetwork c -> [ComponentID]
getEntryPoints net = filter (isEntryPoint net) components
    where
        components = getComponentIDs net

-- Is component a valid entry point into a ring?
isEntryPoint :: XColoredNetwork c -> ComponentID -> Bool
isEntryPoint net c = case comp of
    Merge{} -> True
    GuardQueue{} -> True
    _ -> False
    where 
        comp = getComponent net c

-- Ring to string
showRing :: Show c => XColoredNetwork c -> Ring -> String
showRing net ring = "Ring - Color: " ++ (show $ ringColor ring) ++ "; Queues: " ++ (show $ map componentName queues) ++ "; In: " ++ (show inNames) ++ "; Out: " ++ (show outNames)
    where
        inNames = map (\(channel, _) -> channelName channel) ins'
        outNames = map (\(channel, _) -> channelName channel) outs'
        ins' = map (getChannel net) (ringIns ring)
        outs' = map (getChannel net) (ringOuts ring)
        queues = filter isRingQueue (map (getComponent net . getTarget net) (ringChannels ring))

setEqual :: Eq a => [a] -> [a] -> Bool
setEqual x y = null (x\\y) && null (y\\x)

instance Eq Ring where
    ring1 == ring2 = (setEqual (ringChannels ring1) (ringChannels ring2)) &&
        (setEqual (ringChannels ring1) (ringChannels ring2)) &&
        (setEqual (ringChannels ring1) (ringChannels ring2)) && 
        ((ringColor ring1) == (ringColor ring2))

-- Combine all rings with the same queue set
-- Rings are added to a map wich maps (queues, ring)
-- If a ring is found that already has an entry, the map is updated with the union of the old and new ring
-- Otherwise the ring is simply added to the map
combineRings :: XColoredNetwork c -> [Ring] -> [Ring]
combineRings net rings = Map.elems ringMap where
        ringMap = foldl addToMap Map.empty $ map (\r -> (queues r, r)) rings -- Add all (queues, ring) pairs to map
        queues r = filter (isRingQueue . (getComponent net) . (getTarget net)) (ringChannels r)

addToMap :: Map [ChannelID] Ring -> ([ChannelID], Ring) -> Map [ChannelID] Ring
addToMap currentMap (queues, ring) = case Map.lookup queues currentMap of
    Nothing -> Map.insert queues ring currentMap
    Just ring' -> Map.insert queues (ringUnion ring ring') currentMap

-- Create union of two rings
ringUnion :: Ring -> Ring -> Ring
ringUnion ring1 ring2 = Ring unionComponents unionIns unionOuts unionColors
    where
        unionComponents = union (ringChannels ring1) (ringChannels ring2)
        unionIns = union (ringIns ring1) (ringIns ring2)
        unionOuts = union (ringOuts ring1) (ringOuts ring2)
        unionColors = typeUnion (ringColor ring1) (ringColor ring2)

-- Get invariants for all rings
getRingInvariants :: XColoredNetwork c -> [Ring] -> [Invariant Int]
getRingInvariants net rings = concat $ map (createInvariants net) validRings where
    -- Filter out non-useful rings
    validRings = filter (subTypeProperty net) rings

-- Check if the type of all queues/GuardQueues is a subtype of the ring type
subTypeProperty :: XColoredNetwork c -> Ring -> Bool
subTypeProperty net ring = all colorSubset queues where
    colorSubset queue = subTypeOf (queueType queue) (ringColor ring)
    queues = filter (isRingQueue . getComponent net) ringComponents
    queueType queue = head $ outputTypes net queue
    ringComponents = map (getTarget net) (ringChannels ring)

isRingQueue :: XComponent c -> Bool
isRingQueue comp = case comp of
    Queue{} -> True
    GuardQueue{} -> True
    _ -> False

-- Create invariants for a ring
createInvariants :: XColoredNetwork c -> Ring -> [Invariant Int]
createInvariants net ring = [inv1] where
    inv1 = entryInvariant net ring

-- Create entry invariant: 
-- sum of contents of all queues in ring <= sum of capacities of all queues - min(entry limit)
-- Note: LeqInvariant! sum(queues) - limit <= 0
entryInvariant :: XColoredNetwork c -> Ring -> Invariant Int
entryInvariant net ring = LeqInvariant queueMap Map.empty (-1 * limit) where
    map1 :: Map.Map (Maybe Color) Int
    map1 = Map.fromList $ [(Nothing, 1)]

    queueMap = Map.fromList $ map (\q -> (getTarget net q, map1)) queues
    queues = filter (isRingQueue . getComponent net . getTarget net) (ringChannels ring)

    -- Max number of packets in the ring occ(R) <= cap(R) - min l(i) for i \in ringIns
    limit = totalCapacity - (minimum entryLimits)
    -- Calculate cap(R)
    totalCapacity = sum $ map (getCapacity net) queues
    -- Find all entry limits
    entryLimits = map (getEntryLimit net) (ringIns ring)

-- Get capacity of component
getCapacity :: XColoredNetwork c -> ChannelID -> Int
getCapacity net channelID = case comp of
    Queue _ cap -> cap
    GuardQueue _ cap -> if channelID == bufferChannel then cap else 0 -- Only count if the channel is the buffer channel
    _ -> fatal 158 "getCapacity should only be called on Queues or GuardQueues"
    where
        comp = getComponent net target
        target = getTarget net channelID
        bufferChannel = inChannel 0
        inChannel :: Int -> ChannelID
        inChannel = lookupM' (src 183) (getInChannels net target)

-- Get the number with which an entry point shrinks the total number of packets in the ring
-- l(x) = cap(gq) if x is i_g of GuardQueue gq, 0 otherwise
getEntryLimit :: XColoredNetwork c -> ChannelID -> Int
getEntryLimit net channelID = case comp of
        Merge _ -> 0
        GuardQueue _ size -> if channelID == guardChannel then size else 0 -- Only limit if entry channel is guard channel of GuardQueue
        _ -> fatal 175 "getEntryLimit should only be called on Queues or GuardQueues"
    where
        target = getTarget net channelID
        comp = getComponent net target
        guardChannel = inChannel 1
        inChannel :: Int -> ChannelID
        inChannel = lookupM' (src 196) (getInChannels net target)
