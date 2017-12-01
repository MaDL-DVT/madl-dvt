{-# LANGUAGE ScopedTypeVariables, OverloadedStrings, CPP #-}

{-|
Module      : Madl.Islands
Description : Extract transfer islands from a madl network.
Copyright   : (c) 2015 - 2017 Eindhoven University of Technology
Authors     : Sanne Wouda 2015-2016, Tessa Belder 2015-2016, Julien Schmaltz 2017

Provides a data type for transfer islands. Provides a function to extract these islands from a madl network.
-}
module Madl.Islands (
    Island(..), IslandSet, 
    transferIslands, condition, dataPropagation, islandHasChannel,
    islToChanIDs, islSetToList, getIns, getIslIns, getOuts, getIslOuts
#ifdef TESTING
    -- * Tests
    , Madl.Islands.unitTests
#endif
    ) where

import qualified Data.IntMap as IM
import qualified Data.Map    as M

import Data.Foldable (foldl')
import Data.List (intersect, elemIndex)
import Data.Maybe (mapMaybe,maybeToList,catMaybes,isNothing,fromMaybe)


import Utils.Map
import Utils.Text

import Madl.Network
import Madl.MsgTypes

#ifdef TESTING
import Test.HUnit
import Madl.Base.Identifiers
#endif

-- import Debug.Trace


-- Error function
fileName :: Text
fileName = "Madl.Islands"

fatal :: Int -> String -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++ s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | An island with channels of type @a@ and transitions of automata
data Island a = Island
    { islandChannels :: Map ChannelID a,
      islandTransitions :: Map ComponentID (AutomatonTransition, Int)
    } deriving (Eq, Show)
-- | A set of islands with channels of type @a@
type IslandSet a = IntMap (Island a)

newKey :: IslandSet a -> Int
newKey is = if IM.null is then 0 else 1 + fst (IM.findMax is)

filterWithChannel :: ChannelID -> IslandSet a -> IslandSet a
filterWithChannel c = IM.filter (islandHasChannel c)

islandHasChannel :: forall a. ChannelID -> Island a -> Bool
islandHasChannel c = M.member c . islandChannels

islSetToList :: (IslandSet a) -> [Island a]
islSetToList i = map (\(_,t) -> t) $ IM.toList i

islToChanIDs :: (Island a) -> [ChannelID]
islToChanIDs (Island isl _) = map (\(x,_) -> x) (M.toList isl)


-- | Get initiator components of an island.
getIns :: (Island a) -> ColoredNetwork -> [ComponentID]
getIns (Island c _) net = let chans = (map (\(t,_) -> t) (M.toList c))
                              inits = (map (\t -> getInitiator net t) chans)
                          in filter (\t -> case (intersect (getInChannels net t) chans) of [] -> True; _ -> False ) inits

getIslIns :: (Island a) -> ColoredNetwork -> [ChannelID]
getIslIns isl net = concat (map (\t -> getOutChannels net t) $ getIns isl net)

-- | Get target components of an island
getOuts :: (Island a) -> ColoredNetwork -> [ComponentID]
getOuts (Island c _) net = let chans = (map (\(t,_) -> t) (M.toList c))
                               outs = (map (\t -> getTarget net t) chans)
                           in filter (\t -> case (intersect (getOutChannels net t) chans) of [] -> True; _ -> False) outs

getIslOuts :: (Island a) -> ColoredNetwork -> [ChannelID]
getIslOuts isl net = concat (map (\t -> getInChannels net t) $ getOuts isl net)


type LNode a b = (a,b)

-- | Extract the set of transfer islands from a madl network.
transferIslands :: forall b. Show b => Network Component b -> IslandSet b
transferIslands g = {-# SCC "BuildTransferIslands" #-} foldl' (flip f) s $ transferOrder g where
    f :: ComponentID -> IslandSet b -> IslandSet b
    f n is =
        -- if checkIslands g is' then
            is'
        -- else fatal 78 (show l)
            where
        is' = updateIslands n l (getInChannels g n) (outChannels n) is
        l = getComponent g n
    s = IM.empty
    outChannels :: ComponentID -> [LNode ChannelID b]
    outChannels n = map labelChannel (getOutChannels g n)
    labelChannel :: ChannelID -> LNode ChannelID b
    labelChannel node = (node, getChannel g node)

_checkIslands :: forall a t b . (Show t, Show a) => Network (XComponent t) b -> IslandSet a -> Bool
_checkIslands net isles = IM.null $ IM.filter illegal isles where
    illegal :: Island a -> Bool
    illegal (isle@Island{islandChannels=xs}) = res where
        res = any (invalidChannel isle . fst) $ M.toList xs
    invalidChannel :: Island a -> ChannelID -> Bool
    invalidChannel (Island{islandTransitions=ts}) xID = let cID = getInitiator net xID in case getComponent net cID of
        Automaton{} -> isNothing ph where
            _idx :: Int
            (AutomatonT{phi=ph}, _idx) = lookupM (src 92) cID ts
        _ -> False

type Transition a = ([ChannelID], Maybe (ComponentID, (AutomatonTransition, Int)), [(ChannelID, a)])

maybeAddTrans :: Maybe (ComponentID, (AutomatonTransition, Int)) -> Island a -> Island a
maybeAddTrans (Just p) = addTrans p
maybeAddTrans Nothing = id

updateIslands' :: forall a. Show a => [Transition a] -> IslandSet a -> IslandSet a
-- ts transition list
-- isles: current island set
-- return updated island set
updateIslands' ts isles = if valid isles then foldr f non_con ts else fatal 113 ("inputs without islands: " ++ show all_is) where
    -- initial island set is non-con (non relevant islands)
    -- 
    f :: Transition a -> IslandSet a -> IslandSet a
    f (is, trans, os) isles' = IM.union new isles' where
        -- con = connected islands (from split on list) one island per input channel (see 120)
        -- combine first
        -- extend adds output channels to all islands and possibly transitions
        new = (extend . combine) con
        extend = IM.map (addChannels os . maybeAddTrans trans)
        combine = foldr (cartProd isles') identity
        identity = IM.singleton (newKey isles') $ Island M.empty M.empty
        (con,_) = splitOnList is isles
    all_is = concat [is | (is, _, _) <- ts]
    -- list of all inputs from the transitions
    non_con = IM.filter (\Island{islandChannels=xs} -> all (\c -> M.notMember c xs) all_is) isles
    -- from isles, select irrelevant islands for the set of transitions
    valid = all (not . IM.null) . fst . splitOnList all_is
    -- valid check that islands have at least one channel 

updateIslands :: forall a .Show a => ComponentID -> Component -> [ChannelID] -> [(ChannelID, a)] -> IslandSet a -> IslandSet a
updateIslands _ Sink{} [i] [] isles =
    updateIslands' [([i], Nothing, [])] isles
updateIslands _ DeadSink{} [_] [] isles = isles
updateIslands _ Source{} [] [o] islands =
    updateIslands' [([], Nothing, [o])] islands
updateIslands _ PatientSource{} [] [o] islands =
    updateIslands' [([], Nothing, [o])] islands
updateIslands _ Queue{} _ [o] islands =
    updateIslands' [([], Nothing, [o])] islands
updateIslands _ Vars{} [i] [o] islands =
    updateIslands' [([i], Nothing, [o])] islands
updateIslands _ Cut{} [i] [o] islands =
    updateIslands' [([i], Nothing, [o])] islands
updateIslands _ Function{} [i] [o] islands =
    updateIslands' [([i], Nothing, [o])] islands
updateIslands _ Fork{} [i] os islands =
    updateIslands' [([i], Nothing, os)] islands
updateIslands _ ControlJoin{} is [o] islands =
    updateIslands' [(is, Nothing, [o])] islands
updateIslands _ FControlJoin{} is [o] islands =
    updateIslands' [(is, Nothing, [o])] islands
updateIslands _ Switch{} [i] os islands = updateIslands' ts islands where
    ts = map (\o -> ([i], Nothing, [o])) os
updateIslands _ Merge{} is [o] islands = updateIslands' ts islands where
    ts = map (\i -> ([i], Nothing, [o])) is
updateIslands _ (Match{}) (m:i:[]) (t:f:[]) isles = updateIslands' ts isles where
    ts = [([i,m], Nothing, [t]), ([i], Nothing, [f])]
updateIslands _ MultiMatch{} is os isles = updateIslands' ts isles where
    ts = [([m,d], Nothing, [o]) | (m, o) <- zip ms os, d <- ds]
    (ms, ds) = splitAt (length os) is
updateIslands _ LoadBalancer{} [i] os isles = updateIslands' ts isles where
    ts = map (\o -> ([i], Nothing, [o])) os
updateIslands _ Joitch{} (in1:in2:[]) os isles = updateIslands' ts isles where
    ts = map (\(o1,o2) -> ([in1,in2], Nothing, [o1,o2])) $ pairs os
    pairs [] = []
    pairs [_] = fatal 104 "Illegal network"
    pairs (c1:c2:cs) = (c1, c2) : pairs cs
updateIslands cID Automaton{transitions=ts} is os isles = updateIslands' groups isles where
    groups :: [Transition a]
    groups = map at2t (zip ts [0..])
    at2t :: (AutomatonTransition, Int) -> Transition a
    at2t (t@AutomatonT{inPort=i,outPort=maybeO}, idx) =
        (map (findX 162 is) [i], Just (cID, (t, idx)), map (findX 163 os) (maybeToList maybeO))
    findX :: Show b => Int -> [b] -> Int -> b
    findX i ps = flip (lookupM (src i)) ps
updateIslands _ GuardQueue{} [_, ig] [o] islands = updateIslands' [([], Nothing, [o]),([ig], Nothing, [o])] islands

updateIslands _ c@Match{} _ _ _ = fatal 95 ("invalid network; component: " ++ show c)
updateIslands _ c@Sink{} _ _ _ = fatal 60 ("invalid network; component: " ++ show c)
updateIslands _ c@DeadSink{} _ _ _ = fatal 62 ("invalid network; component: " ++ show c)
updateIslands _ c@Source{} _ _ _ = fatal 64 ("invalid network; component: " ++ show c)
updateIslands _ c@PatientSource{} _ _ _ = fatal 66 ("invalid network; component: " ++ show c)
updateIslands _ c@Queue{} _ _ _ = fatal 68 ("invalid network; component: " ++ show c)
updateIslands _ c@Vars{} _ _ _ = fatal 114 ("invalid network; component: " ++ show c)
updateIslands _ c@Cut{} _ _ _ = fatal 114 ("invalid network; component: " ++ show c)
updateIslands _ c@Function{} _ _ _ = fatal 70 ("invalid network; component: " ++ show c)
updateIslands _ c@Fork{} _ _ _ = fatal 72 ("invalid network; component: " ++ show c)
updateIslands _ c@ControlJoin{} _ _ _ = fatal 80 ("invalid network; component: " ++ show c)
updateIslands _ c@FControlJoin{} _ _ _ = fatal 109 ("invalid network; component: " ++ show c)
updateIslands _ c@Switch{} _ _ _ = fatal 86 ("invalid network; component: " ++ show c)
updateIslands _ c@Merge{} _ _ _ = fatal 92 ("invalid network; component: " ++ show c)
updateIslands _ c@LoadBalancer{} _ _ _ = fatal 102 ("invalid network; component: " ++ show c)
updateIslands _ c@Joitch{} _ _ _ = fatal 120 ("invalid network; component: " ++ show c)
updateIslands _ c@GuardQueue{} _ _ _ = fatal 194 ("invalid network; component: " ++ show c)

cartProd :: IslandSet a -> IslandSet a -> IslandSet a -> IslandSet a
-- islands: ilsands until now
-- compute product between as and bs
cartProd islands as bs =
    IM.fromList (zip [newKey islands..] $ catMaybes
        [ if M.null (M.intersection ts ts') 
            -- ts and ts' are automaton transitions
            -- check intersection between (process) transitions part of the two islands            
            -- if intersection is empty, return Just and compute union (merge islands)
            -- if intersection not empty, return Nothing and islands not mergeable.
            -- note that intersection is computed using process ID only. 
            -- ts and ts' are maps where the key is the component ID
            -- this will not work if processes can write (or read) to more than one channel
            -- on a transition. 
            then Just $ Island (M.union xs xs') (M.union ts ts') 
            else Nothing |
            (_, Island xs ts)   <- IM.toList as,
            (_, Island xs' ts') <- IM.toList bs
        ])

splitOnList :: forall a . Show a => [ChannelID] -> IslandSet a -> ([IslandSet a], IslandSet a)
splitOnList cs is = (islandsByInput, otherIslands) where
    -- cs = list of channel ID's (should be an xs)
    -- is = island set
    -- compute islands relevant to the channels. (example: input channels of a join)
    islandsByInput :: [IslandSet a]
    islandsByInput = map (flip filterWithChannel is) cs 
    -- for each channel is cs, returns the set of islands with this channel. 
    -- otherIslands is the complement, islands without the channel. 
    otherIslands = IM.difference is (foldr IM.union IM.empty islandsByInput)

addChannels :: [(ChannelID, a)] -> Island a -> Island a
addChannels cs island = foldr addChannel island cs

addChannel :: (ChannelID, a) -> Island a -> Island a
addChannel (xID, x) isle@Island{islandChannels=xs} =
    isle{islandChannels = M.insert xID x xs}

addTrans :: (ComponentID, (AutomatonTransition, Int)) -> Island a -> Island a
addTrans (cID, trans) isle@Island{islandTransitions=ts} =
    isle{islandTransitions = M.insertWith (fatal 219 "transition exists") cID trans ts}

-- | Produces an 'MFunctionDisj' which evaluates to the data type of the channel identified by the given channelID.
dataPropagation :: (Show b, Show d) => Network (XComponent c) b -> Island d -> ChannelID -> MFunctionDisj
-- TODO(snnw): check that x is in island with islandId
dataPropagation net island x =
    -- if M.member x (islandChannels island) then
        dataPropagation' c
        -- else fatal 211 ("illegal call to dataPropagation " ++ show x ++ " " ++ show island)
        where
    cID = getInitiator net x
    c = getComponent net cID
    forward = dataPropagation net island
    is = getInChannels net cID
    os = getOutChannels net cID
    [i] = is
    dataPropagation' :: XComponent c -> MFunctionDisj
    dataPropagation' Source{} = XInput cID
    dataPropagation' PatientSource{} = XInput cID
    dataPropagation' Sink{} = fatal 90 "a sink cannot be an initiator"
    dataPropagation' DeadSink{} = fatal 117 "a sink cannot be an initiator"
    dataPropagation' Queue{} = XInput cID
    dataPropagation' Vars{} = forward i
    dataPropagation' Cut{} = forward i
    dataPropagation' Switch{} = forward i
    dataPropagation' Fork{} = forward i
    dataPropagation' Merge{} = forward enabledInput where
        channelsInIsland = M.keys (islandChannels island)
        enabledInput = case intersect channelsInIsland is of
            [input] -> input
            _ -> fatal 145 "Illegal island"
    dataPropagation' ControlJoin{} = forward (head is)
    dataPropagation' (FControlJoin _ f) = XIfThenElseD (XAppliedToB f input) input1 input2 where
        input@(input1:input2:[]) = map forward is
    dataPropagation' (Function _ f _) = f `XAppliedTo` input where
        input = map forward is
    dataPropagation' Match{} = forward (lookupM (src 164) (1::Int) is)
    dataPropagation' MultiMatch{} = forward enabledDataInput where
        channelsInIsland = M.keys (islandChannels island)
        dataInputs = drop (getNrOutputs net cID) is
        enabledDataInput = case intersect channelsInIsland dataInputs of
            [input] -> input
            _ -> fatal 157 "Illegal island"
    dataPropagation' LoadBalancer{} = forward i
    dataPropagation' Joitch{} = forward enabledInput where
        [evenIn, oddIn] = getInChannels net cID
        (evenOuts, oddOuts) = splitOuts os
        enabledInput = if x `elem` evenOuts then evenIn else
            if x `elem` oddOuts then oddIn else fatal 178 "Illegal island"
        splitOuts [] = ([], [])
        splitOuts [_] = fatal 176 "Illegal network"
        splitOuts (c1:c2:cs) = (c1:cs', c2:cs'') where
            (cs', cs'') = splitOuts cs
    dataPropagation' Automaton{} =
        (fromMaybe (fatal 254 "missing expected output function") (phi trans))
        `XAppliedTo` inputs where
        inputs = map forward is
        trans :: AutomatonTransition
        _idx :: Int
        (trans, _idx) = lookupM (src 255) cID (islandTransitions island)
    dataPropagation' GuardQueue{} = case intersect channelsInIsland is of
        [input] -> forward input
        [] -> XInput cID
        _ -> fatal 300 $ "Illegal island"
        where
            channelsInIsland = M.keys (islandChannels island)
     
-- | Produces a list of boolean conditions which must evaluate to True in order for a transtion to take place on the given island.
condition :: (Show b, Show d) => Network (XComponent c) b -> Island d -> [MFunctionBool]
condition net island = mapMaybe getCondition (getComponentsWithID net) where
    getCondition :: (ComponentID, XComponent c) -> Maybe MFunctionBool
    getCondition (node, Switch _ preds) = if length xs == 0 then Nothing
        else Just $ p `XAppliedToB` [dataPropagation net island x] where
            outputs = zip (getOutChannels net node) preds
            xs = filter ((`elem` channelsInIsland) . fst) outputs
            channelsInIsland = M.keys (islandChannels island)
            [(x, p)] = xs
    getCondition (node, Match _ f) = case (islandHasChannel mIn island, islandHasChannel dIn island) of
        (False, False) -> Nothing
        (True, True) -> Just match
        (False, True) -> Just $ XUnOpBool Not match
        (True, False) -> fatal 174 "Illegal island"
        where
            match = f `XAppliedToB` [dataPropagation net island dIn, dataPropagation net island mIn]
            (mIn:dIn:[]) = getInChannels net node
    getCondition (node, MultiMatch _ f) = case (filter (flip islandHasChannel island) mIns, filter (flip islandHasChannel island) dIns) of
        ([], []) -> Nothing
        ([mIn], [dIn]) -> Just $ f `XAppliedToB` [dataPropagation net island dIn, dataPropagation net island mIn]
        p -> fatal 182 ("Illegal island " ++ show p)
        where
            (mIns, dIns) = splitAt (getNrOutputs net node) $ getInChannels net node
    getCondition (node, Joitch _ preds) = case map (flip elemIndex outs) $ filter (flip islandHasChannel island) outs of
        [] -> Nothing
        [Just x, Just y] -> if abs (x - y) /= 1 then fatal 212 "Illegal island"
                else Just $ (lookupM (src 209) (x `div` 2) preds) `XAppliedToB` [dataPropagation net island evenIn, dataPropagation net island oddIn]
        _ -> fatal 210 "Illegal island"
        where
            [evenIn, oddIn] = getInChannels net node
            outs = getOutChannels net node
    getCondition (node, Automaton{}) = case M.lookup node (islandTransitions island) of
        Nothing -> Nothing
        Just (AutomatonT{epsilon=eps}, _) -> Just $ eps `XAppliedToB` map (dataPropagation net island) ins where
            ins = getInChannels net node
    getCondition (_, _) = Nothing

----------------
-- Unit Tests --
----------------

#ifdef TESTING

-- | List of tests to execute
unitTests :: [Test]
unitTests = [testSourceIsland, testSourceIsland2] where

    testSourceIsland = TestLabel "Source Island" $ TestCase $ (do c1; c2)  where
        isles :: IslandSet String
        isles = updateIslands' [([], Nothing, [(ChannelIDImpl 0,"a")])] IM.empty
        c1 = assertEqual "num island" 1 (IM.size isles)
        c2 = assertEqual "num channels in island" 1 (M.size xs) where
            [(_, Island xs _)] = IM.toList isles

    testSourceIsland2 = TestLabel "Source with existing island" $ TestCase $ (do c1; c2) where
        isles, isles' :: IslandSet String
        isles = updateIslands' [([], Nothing, [(ChannelIDImpl 0,"a")])] IM.empty
        isles' = updateIslands' [([], Nothing, [(ChannelIDImpl 1,"b")])] isles
        c1 = assertEqual "num islands" 1 (IM.size isles)
        c2 = assertEqual "num islands" 2 (IM.size isles')

#endif