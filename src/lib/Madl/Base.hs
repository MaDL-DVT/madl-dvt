{-# LANGUAGE  OverloadedStrings, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, CPP #-}

{-|
Module      : Madl.Base
Description : Basic datastructure on which madl networks are constructed.
Copyright   : (c) Sanne Wouda 2015

This module provides a basic data structure for madl networks.
-}
module Madl.Base(
    -- * Network class
    INetwork,
    -- * Data Types
    Network(..), MacroNetwork,
    ChannelID, ComponentID,
    ComponentContext, ChannelContext, DisconnectedChannelContext,
    CGraph,
    -- * Constructors
    mkNetwork, mkMacroNetwork, componentGraph,
    -- * Queries
    component, channel,
    components, channels,
    componentContext, channelContext, disconnectedChannelContext,
    inn, innContext,
    out, outContext,
    target, mTarget,
    initiator, mInitiator,
    -- * Fold
    foldrOnComponents,
    -- * Map
    mapOnChannels, mapOnComponents, mapOnComponentsWithID,
    mapOnComponentsAndChannels, mapOnComponentsContext,
    mapOnChannelsWithID,
    mapWithContextOnComponents,
    -- * Operations
    adjustChannel,
    replaceComponentWithNetwork
    , isConsistent
#ifdef TESTING
    -- * Tests
    , Madl.Base.unitTests
#endif
) where

#ifdef TESTING
import Test.HUnit
import Data.Maybe (fromJust)
#endif

-- import Debug.Trace

import qualified Data.Graph.Inductive.Graph as FGL
import Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.IntMap as IM
import Data.List (intersect)

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.Base.Identifiers

-- Error function
fileName :: Text
fileName = "Madl.Base"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | The context of a component consists of a list of incoming channels, the component itself, and a list of outgoing channels
type ComponentContext a = ([ChannelID], a, [ChannelID])
-- | The context of a channel consists of an initiator component, the channel itself, and a target component
type ChannelContext b = (ComponentID, b, ComponentID)
-- | A disconnected channel context is not required to have initiator and target components.
type DisconnectedChannelContext b = (Maybe ComponentID, b, Maybe ComponentID)

-- | Network data type, with components of type @a@ and channels of type @b@.
data Network a b = NetworkImpl {
    componentMap :: IntMap (ComponentContext a), -- ^ The components of the network
    channelMap :: IntMap (ChannelContext b) -- ^ The channels of the network
} deriving (Show, Eq)

instance Foldable (Network a) where
    foldr f s g' = IM.foldr (f . snd3) s (channelMap g')

-- | Fold over the components of a network
foldrOnComponents :: (a -> b' -> b') -> b' -> Network a b -> b'
foldrOnComponents f s g' = IM.foldr (f. snd3) s (componentMap g')

-- | A macro network is a 'Network' with 'DisconnectedChannelContext's
data MacroNetwork a b = MacroNetworkImpl {
    mComponentMap :: IntMap (ComponentContext a), -- ^ The components of the macro network
    mChannelMap :: IntMap (DisconnectedChannelContext b) -- ^ The channels of the macro network
} deriving (Show,Eq)

-- TODO(snnw) build an instance Eq that ignores specific ChannelIDs and ComponentIDs
--
-- That is, if there exists a mapping between the respective sets of IDs,
-- such that mapped Channels/Components are equivalent, then the networks are equivalent.

-- | Class to group types 'Network' and 'MacroNetwork' together.
class INetwork n a b where
    iComponentMap :: n a b -> IntMap (ComponentContext a) -- ^ The components of the inetwork
    iChannelMap :: n a b -> IntMap (DisconnectedChannelContext b) -- ^ The channels of the inetwork
    iMkNetwork :: IntMap (ComponentContext a) -> IntMap (DisconnectedChannelContext b) -> n a b -- ^ Creates an inetwork from components and channels

instance INetwork Network a b where
    iComponentMap = componentMap
    iChannelMap = disconnectedXmap . channelMap
    iMkNetwork cMap xMap = NetworkImpl cMap (connectedXmap xMap)

instance INetwork MacroNetwork a b where
    iComponentMap = mComponentMap
    iChannelMap = mChannelMap
    iMkNetwork = MacroNetworkImpl

-- | Get the channel context identified by the given channelID
channelContext :: Network a b -> ChannelID -> ChannelContext b
channelContext net (ChannelIDImpl x) = lookupMnoShow (src 22) x (channelMap net)

-- | Get the disconnected channel context identified by the given channelID
disconnectedChannelContext :: INetwork n a b => n a b -> ChannelID -> DisconnectedChannelContext b
disconnectedChannelContext net (ChannelIDImpl x) = lookupMnoShow (src 51) x (iChannelMap net)

-- | Get the component context identified by the given componentID
componentContext :: INetwork n a b => n a b -> ComponentID -> ComponentContext a
componentContext net (ComponentIDImpl c) = lookupMnoShow (src 26) c (iComponentMap net)

-- | Get the component identified by the given componentID
component :: INetwork n a b => n a b -> ComponentID -> a
component net = snd3 . (componentContext net)

-- | Get all components from a network
components :: INetwork n a b => n a b -> [ComponentID]
components net = map ComponentIDImpl $ IM.keys (iComponentMap net)

-- | Get the channel identified by the given channelID
channel :: INetwork n a b => n a b -> ChannelID -> b
channel net = snd3 . (disconnectedChannelContext net)

-- | Get all channels from a network
channels :: INetwork n a b => n a b -> [ChannelID]
channels net = map ChannelIDImpl $ IM.keys (iChannelMap net)

-- | Get the list channelIDs identifying the incoming channels of the component identified by the given componentID
inn :: INetwork n a b => n a b -> ComponentID -> [ChannelID]
inn net = fst3 . (componentContext net)

-- | Get the list channelIDs identifying the outgoing channels of the component identified by the given componentID
out :: INetwork n a b => n a b -> ComponentID -> [ChannelID]
out net = thrd3 . (componentContext net)

-- | Get the list of channel contexts of the incoming channels of the component identified by the given componentID
innContext :: (Show b) => Network a b -> ComponentID -> [ChannelContext b]
innContext net = (map (channelContext net)) . (inn net)

-- | Get the list of channel contexts of the outgoing channels of the component identified by the given componentID
outContext :: (Show b) => Network a b -> ComponentID -> [ChannelContext b]
outContext net = (map (channelContext net)) . (inn net)

-- | Get the componentID identifying the target of the channel identified by the given channelID
target :: Network a b -> ChannelID -> ComponentID
target net = thrd3 . (channelContext net)

-- | If it exists, get the componentID identifying the target of the channel identified by the given channelID
mTarget :: INetwork n a b => n a b -> ChannelID -> Maybe ComponentID
mTarget net = thrd3 . (disconnectedChannelContext net)

-- | Get the componentID identifying the initiator of the channel identified by the given channelID
initiator :: Network a b -> ChannelID -> ComponentID
initiator net = fst3 . (channelContext net)

-- | If it exists, get the componentID identifying the initiator of the channel identified by the given channelID
mInitiator :: INetwork n a b => n a b -> ChannelID -> Maybe ComponentID
mInitiator net = fst3 . (disconnectedChannelContext net)

-- | Update the channel identified by the given channelID according to the given function
adjustChannel :: Network a b -> (b -> b) -> ChannelID -> Network a b
adjustChannel (NetworkImpl cMap xMap) f (ChannelIDImpl x) =
    NetworkImpl cMap (IM.adjust f' x xMap) where
        f' (i, x', t) = (i, f x', t)

-- | Component graph. A graph where the nodes are components, and edges are unlabeled.
type CGraph a = Gr a ()

-- | Extract the component graph from a network.
componentGraph :: forall a b . Network a b -> CGraph a
componentGraph g = s where
    f (ComponentIDImpl i, _, ComponentIDImpl t) = (i, t, ())
    s = FGL.mkGraph (IM.toList $ fmap snd3 (componentMap g)) (IM.elems $ fmap f (channelMap g))

type InterfacePort = (ChannelID, ChannelID)

-- TOOD(snnw) to improve interface: n a b -> MacroNetwork a b -> [InterfacePort] -> [InterfacePort] -> (n a b, [InterfacePort])  ???
-- | Replace a single component of a network by a macro network.
replaceComponentWithNetwork :: forall n a b . (INetwork n a b,Show b) => n a b -> ComponentID -> MacroNetwork a b -> [ChannelID] -> [ChannelID] -> (n a b, [(ChannelID, ChannelID)])
#ifdef TESTING
replaceComponentWithNetwork net _ _ _ _ | not (isConsistent net) = fatal 176 "containing network is not consistent"
replaceComponentWithNetwork _ _ sub _ _ | not (isConsistent sub) = fatal 177 "macro network is not consistent"
#endif
replaceComponentWithNetwork _ _ _ ins outs | not $ null (intersect ins outs) = fatal 183 "inputs and outputs must be distinct"
        -- TODO(snnw): we could allow this, but we need an identity function primitve here.
        -- Or use mapOnComponentsContext to perform a filter
replaceComponentWithNetwork net macro sub ins outs | otherwise = (net', ifx) where
    ifx = zip (ins ++ outs) (map ChannelIDImpl ifxOld)
    net' = iMkNetwork cMap' (assignXPorts cMap' xMap')

    -- all channels, without context
    xMap' :: IntMap b
    xMap' = IM.union (stripPorts xMap) (macroInternalXMap (iChannelMap sub))

    -- all components, with remapped context
    cMap' :: IntMap (ComponentContext a)
    cMap' = IM.delete (runComponentID macro) $
                IM.union (remapTop $ iComponentMap net)
                         (remapMacro $ renumberComponents $ iComponentMap sub)

    -- channels from macro, renumbered, excluding interface channels
    macroInternalXMap :: IntMap (DisconnectedChannelContext b) -> IntMap b
    macroInternalXMap = IM.fromList . map (mapFst renumberChannel) . IM.assocs . stripPorts

    -- remaps ports of components from top
    remapTop :: IntMap (ComponentContext a) -> IntMap (ComponentContext a)
    remapTop = id

    -- remaps ports of components from macro
    remapMacro :: IntMap (ComponentContext a) -> IntMap (ComponentContext a)
    remapMacro = mapOnPorts remapMacroChannelID

    mapOnPorts :: (ChannelID -> ChannelID) -> IntMap (ComponentContext a) -> IntMap (ComponentContext a)
    mapOnPorts f = IM.map f' where
        f' (is, c, os) = (map f is, c, map f os)

    -- renumber components of the macro
    renumberComponents :: IntMap (ComponentContext a) -> IntMap (ComponentContext a)
    renumberComponents m = IM.fromList $ map (mapFst renumberComponent) (IM.assocs m) where
        renumberComponent :: Int -> Int
        renumberComponent = (+) firstFreeCID

    remapMacroChannelID :: ChannelID -> ChannelID
    remapMacroChannelID x = case interfaceChannel x of
        Just x' -> x'
        Nothing -> ChannelIDImpl (runChannelID x + firstFreeXID)

    renumberChannel :: Int -> Int
    renumberChannel = runChannelID . remapMacroChannelID . ChannelIDImpl

    interfaceChannel :: ChannelID -> Maybe ChannelID
    interfaceChannel = (flip IM.lookup) macroInterfaceChannels . runChannelID where
        -- maps a macro channel to the corresponding outside channel
        macroInterfaceChannels :: IntMap ChannelID
        macroInterfaceChannels =
            IM.fromList $ map (mapFst runChannelID) ((map swap inInterface) ++ outInterface)

    inInterface :: [InterfacePort]
    inInterface = zip (inn net macro) ins

    outInterface :: [InterfacePort]
    outInterface = zip outs (out net macro)

    cMap = iComponentMap net
    xMap = iChannelMap net

    ifxOld = map runChannelID (inn net macro ++ out net macro)


    firstFreeCID = 1 + fst (IM.findMax cMap)
    firstFreeXID = 1 + fst (IM.findMax xMap)

stripPorts :: (Functor f) => f (t, b, t1) -> f b
stripPorts = fmap snd3

-- | Map a function over all components in the network.
mapOnComponents :: (INetwork n a b, INetwork n a' b) => (a -> a') -> n a b -> n a' b
mapOnComponents f net = iMkNetwork (IM.map f' (iComponentMap net)) (iChannelMap net) where
    f' (is, c, os) = (is, f c, os)

-- | Map a function over all components in the network.
mapOnComponentsWithID :: (ComponentID -> a -> a') -> Network a b -> Network a' b
mapOnComponentsWithID f net = NetworkImpl (IM.mapWithKey f' (componentMap net)) (channelMap net) where
    f' n (is, c, os) = (is, f (ComponentIDImpl n) c, os)

-- | Map a function over all channels in the network.
mapOnChannelsWithID :: (ChannelID -> b -> b') -> Network a b -> Network a b'
mapOnChannelsWithID f net = NetworkImpl (componentMap net) (IM.mapWithKey f' (channelMap net)) where
    f' n (i, x, o) = (i, f (ChannelIDImpl n) x, o)

-- | Map a function over all channels in the network.
mapOnChannels :: (INetwork n a b, INetwork n a b') => (b -> b') -> n a b -> n a b'
mapOnChannels f net = iMkNetwork (iComponentMap net) (IM.map f' (iChannelMap net)) where
    f' (i, x, t) = (i, f x, t)

-- | Map functions over all components and channels in the network.
mapOnComponentsAndChannels :: (INetwork n a b, INetwork n a' b') => (a -> a') -> (b -> b') -> n a b -> n a' b'
mapOnComponentsAndChannels f g net = iMkNetwork (IM.map (h f) (iComponentMap net)) (IM.map (h g) (iChannelMap net)) where
    h f' (a, b, c) = (a, f' b, c)

-- | Map a function over all components in the network.
mapWithContextOnComponents :: (INetwork n a b, INetwork n a' b) => (ComponentContext a -> a') -> n a b -> n a' b
mapWithContextOnComponents f net = iMkNetwork (IM.map f' (iComponentMap net)) (iChannelMap net) where
    f' context@(is, _, ts) = (is, f context, ts)

type ChannelMap = IntMap ChannelID

-- | Map a function over all component contexts in the network.
mapOnComponentsContext :: forall a a' b . Show b => (ComponentContext a -> Either (ComponentContext a') ChannelID) -> Network a b -> Network a' b
mapOnComponentsContext f net = NetworkImpl cMap' (IM.map fst xMap) where
    cMap' = IM.map renamePorts cMap

    renamePorts :: forall x .ComponentContext x -> ComponentContext x
    renamePorts (is, c, os) = (map rename is, c, map rename os)
    rename = (flip (lookupM (src 278)) xRenameMap) . runChannelID
    cMap = IM.mapMaybe f' (componentMap net)
    f' c = case f c of
        Left (is, a, os) -> Just (is, a, os)
        Right _ -> Nothing
    xRenameMap = IM.unions $ IM.elems $ IM.map snd xMap
    xMap = IM.mapMaybeWithKey adjustChannelContext (channelMap net)

    -- adjusts channel contexts and builds a channel rename map for the component contexts
    adjustChannelContext :: Int -> ChannelContext b -> Maybe (ChannelContext b, ChannelMap)
    adjustChannelContext idx (i, x, t) =
        let i' = runComponentID i
            (t', xRename) = newTarget idx t
            createNewContext _ = ((i, x, t'), xRename)
        in fmap createNewContext (IM.lookup i' cMap)
            -- checks if the channel's initiator exists in the new cMap
            -- if it does not, then this channel is removed

    -- find the new target of channel xId from original target t
    -- produces a map from old xId to all new channels
    newTarget :: Int -> ComponentID -> (ComponentID, ChannelMap)
    newTarget newX' t =
        let t' = runComponentID t
            oldX' = followComponentToChannel t
            (c, xMap') = newTarget newX' (target net oldX')
        in case IM.lookup t' cMap of
            Just _ -> (t, IM.singleton newX' (ChannelIDImpl newX'))
            Nothing -> (c, IM.union xMap' (IM.singleton (runChannelID oldX') (ChannelIDImpl newX')))
    followComponentToChannel :: ComponentID -> ChannelID
    followComponentToChannel c = case (f . (componentContext net)) c of
        Left _ -> fatal 311 "trying to skip a component that was not removed"
        Right xId -> xId

-- | Create a macro network from a list of components contexts and a list of channels
mkMacroNetwork :: [([Int], a, [Int])] -> [b] -> MacroNetwork a b
mkMacroNetwork cs xs
    | checkNetworkInputs cs xs = net
    | otherwise = fatal 256 "channel pointers out of range" where
        net = MacroNetworkImpl cMap (assignXPorts cMap xMap)
        cMap = IM.fromList (zip [0..] (map setChannelIDs cs))
        xMap = IM.fromList (zip [0..] xs)

-- | Check if a list of component contexts is consistent with regard to a list of channels
checkNetworkInputs :: [([Int], a, [Int])] -> [b] -> Bool
checkNetworkInputs cs xs = and $ concatMap checkComponent cs where
    checkComponent (is, _, ts) = map inRange (is ++ ts)
    inRange i = 0 <= i && i < n
    n = length xs

-- | Create a network from a list of component contexts and a list of channels
mkNetwork :: (Show b) => [([Int], a, [Int])] -> [b] -> Network a b
mkNetwork cs xs 
    | checkNetworkInputs cs xs = net
    | otherwise = fatal 276 "channel pointers out of range" where
        net = NetworkImpl cMap (connectedXmap (assignXPorts cMap xMap))
        cMap = IM.fromList (zip [0..] (map setChannelIDs cs))
        xMap = IM.fromList (zip [0..] xs)

setChannelIDs :: ([Int], t, [Int]) -> ([ChannelID], t, [ChannelID])
setChannelIDs (is, c, ts) = (map ChannelIDImpl is, c, map ChannelIDImpl ts)

-- | Transform a map of disconnected channel contexts to a map of connected channel contexts
connectedXmap :: IntMap (DisconnectedChannelContext b) -> IntMap (ChannelContext b)
connectedXmap = IM.mapWithKey connectContext where
    connectContext _ (Just i, x, Just t) = (i, x, t)
    connectContext k (i, _, t) = fatal 322 ("channel context is not fully connected: "
        +++ showT k +++ " with initiator " +++ showT i +++ ", and target " +++ showT t)

-- | Transform a map of connected channel contexts to a map of disconnected channel contexts
disconnectedXmap :: IntMap (ChannelContext b) -> IntMap (DisconnectedChannelContext b)
disconnectedXmap = IM.map (\(i, x, t) -> (Just i, x, Just t))

-- | Transform a map of channels to a map of disconnected channel contexts, according to a list of component contexts
assignXPorts :: forall a b. IntMap (ComponentContext a) -> IntMap b -> IntMap (DisconnectedChannelContext b)
assignXPorts cMap = IM.mapWithKey doChannel where
    doChannel :: Int -> b -> DisconnectedChannelContext b
    doChannel i x = (ini, x, trgt) where
        (ini, trgt) = lookupM (src 279) i ports
    ports = portXMap cMap

-- | A map of disconnected channel contexts without the channel objects themself
type PortXMap = IntMap (Maybe ComponentID, Maybe ComponentID)

-- | Extract a 'PortXMap' from a map of component contexts.
portXMap :: IntMap (ComponentContext a) -> PortXMap
portXMap cMap = IM.foldlWithKey doComponent IM.empty cMap where
    doComponent :: PortXMap -> Int -> ComponentContext a -> PortXMap
    doComponent m c (mIs, _, mTs) = m' where
        cID = ComponentIDImpl c
        m' = foldr setTarget (foldr setInit m mTs) mIs

        setTarget (ChannelIDImpl t) pm =
            IM.insertWith (\_ (i, _) -> (i, Just cID)) t (Nothing, Just cID) pm
        setInit (ChannelIDImpl i) pm =
            IM.insertWith (\_ (_, t) -> (Just cID, t)) i (Just cID, Nothing) pm


-- TODO(snnw) use lookupMnoShow to get rid of Show b
-- | Check if the channelmap and componentmap of a network are consistent with each other.
isConsistent :: forall a b n . (Show b, INetwork n a b) => n a b -> Bool
isConsistent net = and (IM.elems $ IM.mapWithKey matches cMap) where
    cMap = iComponentMap net
    xMap = iChannelMap net
    matches :: Int -> ComponentContext a -> Bool
    matches cId (is, _, os) = all (matchesTarget cId) is && all (matchesInitiator cId) os
    matchesTarget :: Int -> ChannelID -> Bool
    matchesTarget cId i =
        let context :: DisconnectedChannelContext b
            context = lookupM (src 373) (runChannelID i) xMap
        in thrd3 context == Just (ComponentIDImpl cId)
    matchesInitiator :: Int -> ChannelID -> Bool
    matchesInitiator cId o =
        let context :: DisconnectedChannelContext b
            context = lookupM (src 374) (runChannelID o) xMap
        in fst3 context == Just (ComponentIDImpl cId)

#ifdef TESTING
-- | A list of unit tests, mainly to test the 'replaceComponentWithNetwork' function.
unitTests :: [Test]
unitTests = [testUnfold, testTwoComponentsMacro
            , testUnfoldPortOrder, testUnfoldPortOrderB
            , testExternalComponents
            , testMapOnComponentContexts
            ] where
    testUnfold = TestLabel "unfold simple macro" $ TestCase $ assertEqual "unfold failed" expected unfolded where
        macro = MacroNetworkImpl (IM.singleton 0 ([ChannelIDImpl 0],0,[ChannelIDImpl 1])) (IM.fromList [(0, (Nothing, 0, Just (ComponentIDImpl 0))), (1, (Just (ComponentIDImpl 0), 1, Nothing))])
        top = MacroNetworkImpl (IM.singleton 2 ([ChannelIDImpl 2],2,[ChannelIDImpl 3])) (IM.fromList [(2, (Nothing, 2, Just (ComponentIDImpl 2))), (3, (Just (ComponentIDImpl 2), 3, Nothing))])
        unfolded :: MacroNetwork Int Int
        (unfolded,_) = replaceComponentWithNetwork top (ComponentIDImpl 2) macro [ChannelIDImpl 0] [ChannelIDImpl 1]
        expected :: MacroNetwork Int Int
        expected = MacroNetworkImpl
            (IM.singleton 3 ([ChannelIDImpl 2],0,[ChannelIDImpl 3]))
            (IM.fromList [(2, (Nothing, 2, Just (ComponentIDImpl 3))), (3, (Just (ComponentIDImpl 3), 3, Nothing))])

    testTwoComponentsMacro = TestLabel "unfold less simple macro" $ TestCase $ assertEqual "unfold failed" expected unfolded where
        macro = MacroNetworkImpl
            (IM.fromList [(0, ([ChannelIDImpl 0],0,[ChannelIDImpl 1])), (1, ([ChannelIDImpl 1],1,[ChannelIDImpl 2]))])
            (IM.fromList [(0, (Nothing, 0, Just (ComponentIDImpl 0))), (1, (Just (ComponentIDImpl 0), 1, Just (ComponentIDImpl 1))), (2, (Just (ComponentIDImpl 1), 2, Nothing))])
        top = MacroNetworkImpl (IM.singleton 2 ([ChannelIDImpl 2],2,[ChannelIDImpl 3])) (IM.fromList [(2, (Nothing, 2, Just (ComponentIDImpl 2))), (3, (Just (ComponentIDImpl 2), 3, Nothing))])
        unfolded :: MacroNetwork Int Int
        (unfolded,_) = replaceComponentWithNetwork top (ComponentIDImpl 2) macro [ChannelIDImpl 0] [ChannelIDImpl 2]
        expected :: MacroNetwork Int Int
        expected = MacroNetworkImpl
            (IM.fromList [(3, ([ChannelIDImpl 2],0,[ChannelIDImpl 5])), (4, ([ChannelIDImpl 5],1,[ChannelIDImpl 3]))])
            (IM.fromList [(2, (Nothing, 2, Just (ComponentIDImpl 3))), (5, (Just (ComponentIDImpl 3), 1, Just (ComponentIDImpl 4))), (3, (Just (ComponentIDImpl 4), 3, Nothing))])

    testUnfoldPortOrder = TestLabel "id port order" $ TestCase (unfoldPortOrderTest id)

    testUnfoldPortOrderB = TestLabel "reverse port order" $ TestCase (unfoldPortOrderTest reverse)

    unfoldPortOrderTest order = assertEqual "port order not preserved" (order [1,2]) xs where
        macro :: MacroNetwork String Int
        macro = mkMacroNetwork [([0], "fork", order [1,2])] [0,1,2]
        top :: MacroNetwork String Int
        top = mkMacroNetwork [([0], "macro", [1, 2])] [0,1,2]
        unfolded :: MacroNetwork String Int
        (unfolded,_) = replaceComponentWithNetwork top (ComponentIDImpl 0) macro [ChannelIDImpl 0] [ChannelIDImpl 1, ChannelIDImpl 2]
        xs :: [Int]
        xs = map (channel unfolded) (out unfolded c)
        c :: ComponentID
        [c] = components unfolded

    testExternalComponents = TestLabel "external components" $ TestCase (do c1; c2) where
        macro :: MacroNetwork String Int
        macro = mkMacroNetwork [([0], "1", [1])] [0,1]
        top :: MacroNetwork String Int
        top = mkMacroNetwork [([0],"q0",[1]), ([1],"macro",[2]), ([2],"q1",[3])] [0,1,2,3]
        (unfolded,_) = replaceComponentWithNetwork top (ComponentIDImpl 1) macro [ChannelIDImpl 0] [ChannelIDImpl 1]
        c1 = assertEqual "target of q0 does not match" "1" $
            ((component unfolded) . fromJust . (mTarget unfolded) . head . (out unfolded) . ComponentIDImpl) 0
        c2 = assertEqual "initiator of q1 does not match" "1" $
            ((component unfolded) . fromJust . (mInitiator unfolded) . head . (inn unfolded) . ComponentIDImpl) 2

    testMapOnComponentContexts = TestLabel "map on component contexts" $ TestCase (do c1; c2; c3)
     where
        net :: Network Int Int
        net = mkNetwork [([], 0, [0]), ([0], 10, [1]), ([1], 11, [2]), ([2], 1, [])] [0,1,2]
        f (is, c, os) | c < 10    = Left (is, c, os)
                      | otherwise = Right (head os)
        fnet = mapOnComponentsContext f net
        c1 = assertEqual "num components" 2 (length $ components fnet)
        c2 = assertEqual "num channels" 1 (length $ channels fnet)
        c3 = assertBool "is consistent" (isConsistent fnet)
#endif
