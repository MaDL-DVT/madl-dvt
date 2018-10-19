{-# LANGUAGE  MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, OverloadedStrings, FlexibleContexts, CPP #-}
{-# OPTIONS_GHC -Wall #-}

{-|
Module      : Madl.Network
Description : Data structure for madl networks.
Copyright   : (c) Eindhoven University of Technology
Authors: Sanne Wouda 2015-2016, Tessa Belder 2015-2016, Julien Schmaltz 2015-2017

This module the data structure for madl networks. Furthermore it contains 
queries for these networks, and network transformation functions.
-}
module Madl.Network (
    -- * Type classes
    INetwork, IMadlNetwork,
    Flattened(..),
    MayBeQueue(..), HasName(..),
    -- * Data Types
    Specification(..), SpecificationSource(..),
    ChannelID, ComponentID,
    -- ** Networks
    Network, MadlNetwork, XMadlNetwork, TMadlNetwork,
    FlattenedNetwork, FlatFlattenedNetwork,
    XFlattenedNetwork,
    ColoredNetwork, FlatColoredNetwork, XColoredNetwork,
    MadlMacroNetwork, FlattenedMacroNetwork,
    -- ** Network components
    Component, FlatComponent, XComponent(..),
    AutomatonTransition(..),
    Channel, XChannel(..),
    Macro, FlatMacro, XMacro(..),
    MacroInstance, FlatMacroInstance, XMacroInstance(..),
    ComponentOrMacro, FlatComponentOrMacro, XComponentOrMacro(..),
    -- * Construction
    emptySpecificationSource,
    Madl.Network.mkNetwork, Madl.Network.mkMacroNetwork,
    mkMacro,
    -- * Query
    largestConnectedComponent, transferOrder, networkTypes,
    networkStructFields, validMaDLNetwork, getStructFields,
    -- ** Component Queries
    getComponentIDs, getComponents, getComponentsWithID,
    getComponent, getComponentContext,
    findComponentID, findComponent, findComponentWithID,
    getNameText, getNameList,
    getInChannels, getOutChannels, getAllChannels,
    getNrInputs, getNrOutputs,
    inputTypes, outputTypes,
    getAllQueues, getAllSwitches,getAllSources,getAllSinks,getAllMerges,
    getAllQueuesWithID,getAllSwitchesWithID,getAllSourcesWithID,getAllSourceIDs,
    getAllMergesWithID,getAllSinksWithID,getAllFJoinsWithID,getAllProcessesWithID,
    getAutomatonStateMap,getAllProcesses,getAutomatonStateMapWithProcessName,
    getAllFunctionsWithID,prettyPrintStateMap,
    -- ** Channel Queries
    getChannelIDs, getChannels, getChannelsWithID,
    getChannel, getChannelContext,
    findChannelID, findChannel,findChannelWithID,
    getInitiator, getTarget, getColorSet,
    getInitiatorWithPort, getTargetWithPort,
    getMInitiator, getMTarget,
    -- ** Macro Queries
    getMacros, getMacro, splitInterface,
    getMacroInstances, getInstanceChannels,
    -- * Fold
    foldrOnComponents,
    -- * Map
    mapOnChannels, mapOnComponents, mapOnComponentsWithID,
    mapOnComponentsAndChannels, mapOnComponentsContext,
    mapOnChannelsWithID,
    mapWithContextOnComponents,
    -- * Network transformations
    channelTypes, removeColors,
    unfoldMacros, unfoldMacrosWithNameMap,
    cast',
    pruneNetwork
#ifdef TESTING
    -- * Tests
    , Madl.Network.unitTests
#endif
) where

-- import Debug.Trace

import qualified Data.Graph.Inductive.Graph as FGL
import Data.Graph.Inductive.Query.BCC (bcc)
import Data.Graph.Inductive.Query.DFS (topsort')
import Data.Hashable (Hashable)
import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Traversable()
import qualified Data.Map as Data.Map


import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.Base
import Madl.MsgTypes
import Madl.SourceInformation

#ifdef TESTING
import Test.HUnit
import Examples.TypesAndFunctions
#endif

-- Error function
fileName :: Text
fileName = "Madl.Network"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++ utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-------------------------
-- Transfer Order
-------------------------

-- | Get the transfer order for a network
transferOrder :: forall a b . MayBeQueue a => Network a b -> [ComponentID]
transferOrder = (map fst) . topsort' . removeQueueInputPorts . componentGraph . numberComponents where
    numberComponents = mapOnComponentsWithID (\i x -> (i, x))

-- | Remove the incoming channels from queues
removeQueueInputPorts :: forall a b . MayBeQueue a => CGraph (b, a) -> CGraph (b, a)
removeQueueInputPorts g = FGL.gfiltermap (Just . removeQueueInputPort) g where
    removeQueueInputPort :: FGL.Context (b,a) () -> FGL.Context (b,a) ()
    removeQueueInputPort context@(_, cId, c, os) = if isQueue (snd c) then ([], cId, c, os) else removeQueueInitiator context
    removeQueueInitiator :: FGL.Context (b,a) () -> FGL.Context (b,a) ()
    removeQueueInitiator (is, cId, c, os) = (is, cId, c, filter notToQueue os)
    notToQueue :: ((), FGL.Node) -> Bool
    notToQueue = (not . isQueue . snd. fromMaybe (fatal 134 "missing node label") . FGL.lab g . snd)


-- TODO(snnw) Reduce an automaton to the combinational part

-- doContext :: MayBeQueue a => FGL.Context (b,a) c -> CGraph (b,a) -> CGraph (b,a)
-- doContext ctx g = foldr doTransition g $ getTransitions (snd $ FGL.lab' ctx)

-- doTransition :: AutomatonTransition -> CGraph (b,a) -> CGraph (b,a)
-- doTransition (AutomatonT _ _ event transform) g = undefined

-- | Get the size of the largest connected component in a network
largestConnectedComponent :: MayBeQueue a => Network a b -> Int
largestConnectedComponent = maximum . (map length) . (map FGL.nodes) . bcc . removeQueueInputPorts . componentGraph . numberComponents where
    numberComponents = mapOnComponentsWithID (\i x -> (i, x))

-------------------------------------
-- MaDLNetwork data types
-------------------------------------

-- | A madl network is a network with 'ComponentOrMacro' as component type, 
--  and 'Channel' as channel type.
--  The "Text" argument to XMadlNetwork is later a parameter.
type MadlNetwork = XMadlNetwork Text
-- | A madl macro network is a macro network with 'ComponentOrMacro' as 
--  component type, and 'Channel' as channel type
type MadlMacroNetwork = XMadlMacroNetwork Text
-- | A madl network where the names of components and channels are of an arbitrary type
type XMadlNetwork c = Network (XComponentOrMacro (XChannel c) c) (XChannel c)
-- | A madl macro network where the names of components and channels are of an arbitrary type
type XMadlMacroNetwork c = MacroNetwork (XComponentOrMacro (XChannel c) c) (XChannel c)

-- | A flattened network is a network with 'Component' as component type, and 'Channel' as channel type
type FlattenedNetwork = XFlattenedNetwork Text
-- | A flattened macro network is a macro network with 'Component' as component type, and 'Channel' as channel type
type FlattenedMacroNetwork = XFlattenedMacroNetwork Text
-- | A flattened network where the names of components and channels have type @[Text]@
type FlatFlattenedNetwork = XFlattenedNetwork [Text]
-- | A flattened network where the names of components and channels are of an arbitrary type
type XFlattenedNetwork c = Network (XComponent c) (XChannel c)
-- | A flattened macro network where the names of components and channels are of an arbitrary type
type XFlattenedMacroNetwork c = MacroNetwork (XComponent c) (XChannel c)


-- | A process state consists of a name of this state, and a list of argument instantiations
type PState = (Text, [Color])
-- | Maps process state to identifier number
type PStateNrMap = Map PState Int


-- | Class for grouping the MadlNetwork and MadlMacroNetwork.
class INetwork n (ComponentOrMacro Channel) Channel => IMadlNetwork n
instance IMadlNetwork Network
instance IMadlNetwork MacroNetwork
-- | The type TMadlNetwork is the type of instances of the 'INetwork' class
type TMadlNetwork n = n (ComponentOrMacro Channel) Channel

-- | Either a 'Component' or a 'MacroInstance'
type ComponentOrMacro b = XComponentOrMacro b Text
-- | A 'Component' or 'MacroInstance' with a name of type @[Text]@
type FlatComponentOrMacro b = XComponentOrMacro b [Text]
-- | A 'Component' or 'MacroInstance' with a name of an arbitrary type
data XComponentOrMacro b c = C {runC :: XComponent c} | M {runM :: XMacroInstance b c} deriving (Show,Eq)

-- | A component (primitive) of a madl network
type Component = XComponent Text
-- | A 'Component' with a name of type @[Text]@
type FlatComponent = XComponent [Text]
-- | A 'Component' with a name of an arbitrary type
data XComponent c =
    -- | Produces packets. Parameter 'messages' determines the color of these packets.
    --   Blocking of a source is considered a deadlock.
    Source {
        componentName :: c,
        messages :: ColorSet
    }
    -- | Produces packets. Parameter 'messages' contains the color of these packets.
    --   Blocking of this type of source is not considered a deadlock.
    | PatientSource {
        componentName :: c,
        messages :: ColorSet
    }
    -- | Consumes packets. Is always ready to consume a packet (a live sink).
    | Sink {
        componentName :: c
    }
    -- | Consumes packets. Is never ready to consume a packet.
    | DeadSink {
        componentName :: c
    }
    -- | Transforms packets. Parameter 'function' contains the function to transform with.
    | Function {
        componentName :: c,
        function :: MFunctionDisj,
        returnType :: ColorSet
    }
    -- | Stores packets. Parameter 'capacity' determines how many packets can be stored. Has FIFO behavior.
    | Queue {
        componentName :: c,
        capacity :: Int
    }
    -- | Routes packets. Parameter 'switching' determines how packets are routed.
    --   Each incoming packet must match to exactly one of the switching types.
    --   The amount of switching types must be equal to the number of outgoing channels of the switch.
    | Switch {
        componentName :: c,
        switching :: [MFunctionBool]
    }
    -- | Arbitor. Transfers packets from multiple incoming channels to a single outgoing channel.
    --   Arbitration behavior is arbitrary.
    | Merge {
        componentName :: c
    }
    -- | Duplicates packets. Packet from a single incoming channel are tranfered to all outgoing channels.
    | Fork {
        componentName :: c
    }
    -- | Joins packets. The packets from its first incoming channel are transfered to its outgoing channel.
    --   Packets on other incoming channels are used for synchronization, then disappear.
    | ControlJoin {
        componentName :: c
    }
    -- | Joins packets. The function determines which packet is transfered to the outgoing channel.
    | FControlJoin {
        componentName :: c,
        matchFunction :: MFunctionBool
    }
    -- | Matches and routes packets. Parameter 'matchFunction' determines whether packets match or not.
    --   Has 2 inputs (m and d) and 2 outputs (t and f).
    --   If two incoming packets from d and m match, the packet from m is consumed and disappears,
    --     and the packet from d is transfered to t.
    --   If two incoming packets from d and m don't match, the packet from m is not consumed, i.e. it stays available for the next match.
    --     The packet from d is transfered to f.
    | Match {
        componentName :: c,
        matchFunction :: MFunctionBool
    }
    -- | Matches and routes packets. Parameter 'matchFunction' determines whether packets match or not.
    --   Has n + m inputs (m_1..m_n and d_1..d_m) and n outputs (o_1..o_n).
    --   Has an arbiter (sel) that takes value 'None' (undecided) or a pair (i, j), with (1 <= i <= n and 1 <= j <= m).
    --   The arbiter can only take value (i, j) if m_i and d_j are both irdy, and if the packets from m_i and d_j match.
    --   When the arbiter has selected (i, j), the packet from m_i is consumed and disappears, and the packet from d_j is transfered to o_i.
    | MultiMatch {
        componentName ::c,
        matchFunction :: MFunctionBool
    }
    -- | Routes incoming packets to one of its outputs, based on some arbitration policy.
    | LoadBalancer {
        componentName :: c
    }
    -- | Finite State Machine
    | Automaton {
        componentName :: c,
        nrOfInputs    :: Int, -- ^ number of incoming channels
        nrOfOutputs   :: Int, -- ^ number of outgoing channels
        nrOfStates    :: Int, -- ^ amount of states
        transitions   :: [AutomatonTransition], -- ^ list of transitions
        stateMap       :: PStateNrMap -- ^ map between state names and state ID's
    }
    -- | Switch for a pair of incoming packets. Parameter 'predicates' determines how the packets are routed.
    --   For each pair of incoming packets, exactly one of the predicates must evaluate to @True@.
    --   The amount of outgoing channels of the Joitch must be twice the amount of predicates.
    | Joitch {
        componentName :: c,
        predicates :: [MFunctionBool]
    }
    -- | Trivial component. Behavior is equal to a queue of size 0, and to the identity function. Used to break deadlock equations (fix for #98).
    | Vars {
        componentName :: c
    }
    -- | {Trivial like Vars, but breaks cycles.}
    | Cut{
        componentName :: c
    }
    -- | Merge with internal queue on first input, only allows input on second input if internal queue is empty.
    | GuardQueue {
        componentName :: c,
        capacity :: Int
    }
    deriving (Show,Eq)

-- | A transition of a finite state machine
data AutomatonTransition = AutomatonT {
    startState :: Int, -- ^ start-state
    endState :: Int, -- ^ end-state
    inPort :: Int, -- ^ input port
    epsilon :: MFunctionBool,
    eventFunction :: Int -> Color -> Bool, -- ^ port-sensitive event
    outPort :: Maybe Int,
    phi :: Maybe (MFunctionDisj),
    packetTransformationFunction :: Int -> Color -> Maybe (Int, Color) -- ^ port-sensitive packet transformation
} 

-- JS: noway to show for eventFunction nor packetTransformationFunction
instance Show AutomatonTransition where
    show (AutomatonT{startState=start,endState=end,inPort=ip,epsilon=eps,outPort=op,phi=ph}) = "(" ++ intercalate ", " [show start, show end, show ip, show eps, show op, show ph] ++ ")"
instance Eq AutomatonTransition where
    (==) _ _ = fatal 291 "Cannot determine equality between automaton transition"

-- | A macro instance component of a madl network
type MacroInstance b = XMacroInstance b Text
-- | A 'MacroInstance' with a name of type @[Text]@
type FlatMacroInstance b = XMacroInstance b [Text]
-- | A 'MacroInstance' with a name of an arbitrary type
data XMacroInstance b c =
    MacroInstance {
        instanceName :: c,
        instanceMacro :: XMacro b c
    } deriving (Show,Eq)

-- | A madl macro
type Macro b = XMacro b Text
-- | A 'Macro' where the names of components and channels have type @[Text]@
type FlatMacro b = XMacro b [Text]
-- | A 'Macro' where the names of components and channels are of an arbitrary type
data XMacro b c =
    Macro {
        macroInterface :: [ChannelID],
        macroName :: Text,
        macroNetwork :: MacroNetwork (XComponentOrMacro b c) b
    } deriving (Show,Eq)

-- | A channel of madl network
type Channel = XChannel Text
-- | A 'Channel' with a name of type @[Text]@
type FlatChannel = XChannel [Text]
-- | A 'Channel' with a name of an arbitrary type
data XChannel c = Channel {channelName :: c} deriving (Show,Eq)

-------------------------------------
-- MaDLNetwork constructors
-------------------------------------

-- | A specification consists of a list of components of type a with names of type c,
--   a list of channels of type b with names of type c, and a list of ports of type (c, c).
data Specification a b c = NSpec {
    specComponents :: [a],
    specChannels :: [b],
    specPorts :: [(c, c)]
    } deriving (Show)

-- | Make a network structure from a set of components, a set of channels,
--   and a set of ports represent by (componentName, channelName) and (channelName, componentName) pairs.
--   Ports are assigned based on order of input of the ports.
--   MacroInstance instanceChannels are assigned in sorted order of ports, ie. in sorted order of input of the ports.
mkNetwork :: forall a b c . (Show c, Ord c, Hashable c, HasName a c, HasName b c, Show b) => Specification a b c -> Network a b
mkNetwork spec@(NSpec cs xs _) = Madl.Base.mkNetwork cs' xs where
    cs' = map (\((is, os), c) -> (is, c, os)) (zip (IM.elems contextMap) cs)
    contextMap = makeComponentContexts spec

-- | Make a network structure from a set of components, a set of channels,
--   and a set of ports represent by (componentName, channelName) and (channelName, componentName) pairs.
--   Ports are assigned based on order of input of the ports.
--   MacroInstance instanceChannels are assigned in sorted order of ports, ie. in sorted order of input of the ports.
mkMacroNetwork :: forall a b c. (Show c, Ord c, Hashable c, HasName b c, HasName a c, Show b) => Specification a b c -> MacroNetwork a b
mkMacroNetwork spec@(NSpec cs xs _) = Madl.Base.mkMacroNetwork cs' xs where
    cs' = map (\((is, os), c) -> (is, c, os)) (zip (IM.elems contextMap) cs)
    contextMap = makeComponentContexts spec

-- Useful datatypes for network construction
type CMap c = Hash.Map c Int
type ContextMap = IntMap ([Int], [Int])

-- | Create componentContexts, i.e. assign ports.
makeComponentContexts :: (Show c, Hashable c, Ord c, HasName a c, HasName b c) => Specification a b c -> ContextMap
makeComponentContexts (NSpec cs xs ports) = foldr (getPort compMap chanMap) IM.empty ports where
    compMap = Hash.fromList $ zip (map getName cs) [0..]
    chanMap = Hash.fromList $ zip (map getName xs) [0..]

-- | Assign a single port
getPort :: (Hashable c, Ord c, Show c) => CMap c -> CMap c -> (c, c) -> ContextMap -> ContextMap
getPort compMap chanMap (i, t) ccs =
    case (Hash.lookup i compMap, Hash.lookup i chanMap, Hash.lookup t compMap, Hash.lookup t chanMap) of
        (Nothing, Nothing, _, _) -> fatal 132 $ "initiator does not exist: " +++ showT i +++ " in compmap: " +++ showT compMap +++ " and chanmap: " +++ showT chanMap
        (_, _, Nothing, Nothing) -> fatal 132 $ "target does not exist: " +++ showT t +++ " in compmap: " +++ showT compMap +++ " and chanmap: " +++ showT chanMap
        (Just _, Just _, _, _) -> fatal 134 $ "initiator cannot be both a component and a channel: " +++ showT i
        (_, _, Just _, Just _) -> fatal 135 $ "target cannot be both a component and a channel: " +++ showT t
        (Just _, Nothing, Just _, Nothing) -> fatal 136 $ "initiator and target cannot both be a component: " +++ showT i +++ " and " +++ showT t
        (Nothing, Just _, Nothing, Just _) -> fatal 137 $ "initiator and target cannot both be a channel: " +++ showT i +++ " and " +++ showT t
        (Just a, Nothing, Nothing, Just b) -> IM.insertWith addOutput a ([], [b]) ccs where
            addOutput _ (is, os) = (is, b:os)
        (Nothing, Just b, Just a, Nothing) ->  IM.insertWith addInput a ([b], []) ccs where
            addInput _ (is, os) = (b:is, os)

-- | Create a macro object from its parameters
mkMacro :: forall b c. (Eq c, Show c, HasName b c) => MacroNetwork (XComponentOrMacro b c) b -> Text -> [c] -> XMacro b c
mkMacro network name interface =
    Macro {
        macroInterface = map channelNr interface,
        macroNetwork = network,
        macroName = name
    } where
        channelNr :: c -> ChannelID
        channelNr chanName = fromMaybe err $ findChannelID network chanName where
            err = fatal 175 $ "Invalid channelName: " +++ showT chanName

--------------------------------------------------------------------------------
-- Source Context
--------------------------------------------------------------------------------

-- | a source context consists of
--   1. a map from componentnames to source information
--   2. a map from channelnames to source information
data SpecificationSource = SpecSrc {
    componentSource :: Hash.Map [Text] SourceInformation,
    channelSource   :: Hash.Map [Text] SourceInformation
    } deriving (Show)

-- | The empty source context
emptySpecificationSource :: SpecificationSource
emptySpecificationSource = SpecSrc {
    componentSource = Hash.empty,
    channelSource = Hash.empty
    }

-------------------------------------
-- Typed MaDLNetwork
-------------------------------------

-- TODO(snnw): add type information to queues as well
--
-- | A ColoredNetwork is a network with components and where each channel has 
--   been annotated with an overapproximation of the colors of the packets
--   that can be transfered through that channel.
type ColoredNetwork = XColoredNetwork Text
-- | A 'ColoredNetwork' where the names of components and channels have type @[Text]@
type FlatColoredNetwork = XColoredNetwork [Text]
-- | A 'ColoredNetwork' where the names of components and channels are of an arbitrary type
type XColoredNetwork c = Network (XComponent c) (WithColors (XChannel c))

-- | Function 'channelTypes' executes the color derivation, i.e., it annotates each channel with its colors.
-- For each source, the set of colors injected by that source is propagated forwards until a fixpoint is reached.
channelTypes :: forall c. Show c => XFlattenedNetwork c -> XColoredNetwork c
channelTypes net = foldr propFromSource start (map fst $ filter (isSource . snd) $ getComponentsWithID net) where
    start :: XColoredNetwork c
    start = mapOnChannels (addColors nul) net
    propFromSource :: ComponentID -> XColoredNetwork c -> XColoredNetwork c
    propFromSource cID net' = case prop net' (componentContext net' cID) of
        Just net'' -> fixpoint net'' (out net'' cID)
        Nothing -> net'
    fixpoint :: XColoredNetwork c -> [ChannelID] -> XColoredNetwork c
    fixpoint net' [] = net'
    fixpoint net' (c:cs) = let trgt = componentContext net' $ target net' c in
        case prop net' trgt of
            Nothing -> fixpoint net' cs
            Just net'' -> fixpoint net'' (nub $ thrd3 trgt ++ cs)

-- | Execute color propagation for a single component
prop :: forall c. Show c => XColoredNetwork c -> ComponentContext (XComponent c) -> Maybe (XColoredNetwork c)
prop net (_, Source _ t, [xOut]) = updateType net xOut t
prop net (_, PatientSource _ t, [xOut]) = updateType net xOut t
prop _ (_, Sink{}, _) = Nothing
prop _ (_, DeadSink{}, _) = Nothing
prop net ([xIn], Queue {}, [xOut]) = updateType net xOut (getColorSet net xIn)
prop net ([xIn], Vars {}, [xOut]) = updateType net xOut (getColorSet net xIn)
prop net ([xIn], Cut {}, [xOut]) = updateType net xOut (getColorSet net xIn)
prop net ([xIn], Function name typeFunction returntype, [xOut]) =
  case resultingType (makeArguments [getColorSet net xIn]) (XAppliedTo typeFunction [XVar 0]) of
    Right err -> fatal 360 $ (showT err) +++ "in function: " +++ showT name --Nothing -- TODO(tssb, snnw): Make difference between Nothing and Nothing explicit
    Left (propType::ColorSet) -> if propType `subTypeOf` returntype then updateType net xOut propType
        else fatal 362 $ "Error in type propagation of function component " +++showT name +++":\n  " +++ "Calculated type " +++ showT propType +++ " is not a subtype of the expected returntype " +++ showT returntype
prop net (xs, Merge{}, [xOut]) = updateType net xOut newType where
    newType = foldr (typeUnion . getColorSet net) nul xs
prop net ([xIn], Switch _ preds, xs) = foldlAllMaybe setSwitchType net (zip xs preds) where
    setSwitchType :: XColoredNetwork c -> (ChannelID, MFunctionBool) -> Maybe (XColoredNetwork c)
    setSwitchType net' (xOut, p) = updateType net' xOut $ filter (\c -> predIsTrue p [c]) inColors
    inColors = getColors $ getColorSet net xIn
prop net ([xIn], Fork{}, xs) = foldlAllMaybe forking net xs where
    forking :: XColoredNetwork c -> ChannelID -> Maybe (XColoredNetwork c)
    forking net' xOut = updateType net' xOut (getColorSet net' xIn)
prop net (dataIn:tokenIns, ControlJoin{}, [xOut]) = updateType net xOut inType where
    inType = if any (emptyColorSet . getColorSet net) tokenIns then nul else getColorSet net dataIn
prop net (xIn1:xIn2:[], FControlJoin _ f, [xOut]) = updateType net xOut (typeUnion inType1 inType2) where
    inType1 = filter (flip (mayMatch True f) $ getColorSet net xIn2) (getColors $ getColorSet net xIn1)
    inType2 = filter (mayMatch False f $ getColorSet net xIn1) (getColors $ getColorSet net xIn2)
prop net (matchIn:dataIn:[], (Match _ f), tOut:fOut:[]) = maybe (updateNoMatch net) applyNoMatch updateMatch where
    applyNoMatch n = maybe (Just n) Just (updateNoMatch n)
    updateMatch = updateType net tOut (matchingValues True)
    updateNoMatch net' = updateType net' fOut (matchingValues False)
    matchingValues val = filter (flip (mayMatch val f) $ getColorSet net matchIn) (getColors $ getColorSet net dataIn)
prop net (inputs, (MultiMatch _ f), outputs) = foldlAllMaybe updateOutput net $ zip matchIns outputs where
    (matchIns, dataIns) = splitAt (length outputs) inputs
    dColors = getColors . foldr typeUnion nul $ map (getColorSet net) dataIns
    updateOutput :: XColoredNetwork c -> (ChannelID, ChannelID) -> Maybe (XColoredNetwork c)
    updateOutput net' (mIn, xOut) = updateType net' xOut $ filter (flip (mayMatch True f) $ getColorSet net mIn) dColors
prop net ([xIn], LoadBalancer{}, xs) = foldlAllMaybe balancing net xs where
    balancing :: XColoredNetwork c -> ChannelID -> Maybe (XColoredNetwork c)
    balancing net' xOut = updateType net' xOut (getColorSet net' xIn)
prop net (xIns, (Automaton _ _ _ _ ts _), xOuts) = foldlAllMaybe transforming net (zip [0..] xOuts) where
    transforming :: XColoredNetwork c -> (Int, ChannelID) -> Maybe (XColoredNetwork c)
    transforming net' (port, xOut) = updateType net' xOut . map snd $ filter ((== port) . fst) resultingColors
    resultingColors :: [(Int, Color)]
    resultingColors = concatMap (\input -> concatMap (execTransition input) ts) (zip [0..] xIns)
    execTransition :: (Int, ChannelID) -> AutomatonTransition -> [(Int, Color)]
    execTransition (p, xIn) (AutomatonT{eventFunction=e,packetTransformationFunction=f}) = mapMaybe (\c -> if e p c then f p c else Nothing) (getColors $ getColorSet net xIn)
prop net ([xIn1, xIn2], Joitch _ preds, xs) = foldlAllMaybe joitching net (zip preds $ makePairs xs) where
    joitching :: XColoredNetwork c -> (MFunctionBool, (ChannelID, ChannelID)) -> Maybe (XColoredNetwork c)
    joitching net' (p, (xOut1, xOut2)) = case updateType net' xOut1 colors1 of
        Nothing -> updateType net' xOut2 colors2
        Just net'' -> Just . fromMaybe net'' $ updateType net'' xOut2 colors2
        where
            colors1 = filter (flip (mayMatch True p) $ getColorSet net xIn2) (getColors $ getColorSet net xIn1)
            colors2 = filter (mayMatch True p $ getColorSet net xIn1) (getColors $ getColorSet net xIn2)
    makePairs [] = []
    makePairs [_] = fatal 398 "invalid network"
    makePairs (xOut1:xOut2:xOuts) = (xOut1, xOut2) : makePairs xOuts
prop net (xs, GuardQueue{}, [xOut]) = updateType net xOut newType where
    newType = foldr (typeUnion . getColorSet net) nul xs
prop _ (_, Source{}, _) = fatal 283 "invalid network"
prop _ (_, PatientSource{}, _) = fatal 285 "invalid network"
prop _ (_, Queue{}, _) = fatal 287 "invalid network"
prop _ (_, Vars{}, _) = fatal 288 "invalid network"
prop _ (_, Cut{}, _) = fatal 289 "invalid network"
prop _ (_, Function{}, _) = fatal 292 "invalid network"
prop _ (_, Merge{}, _) = fatal 297 "invalid network"
prop _ (_, Switch{}, _) = fatal 300 "invalid network"
prop _ (_, Fork{}, _) = fatal 304 "invalid network"
prop _ (_, ControlJoin{}, _) = fatal 309 "invalid network"
prop _ (_, FControlJoin{}, _) = fatal 415 "invalid network"
prop _ (_, Match{}, _) = fatal 341 "invalid network"
prop _ (_, LoadBalancer{}, _) = fatal 361 "invalid network"
prop _ (_, Joitch{}, _) = fatal 413 "invalid network"
prop _ (_, GuardQueue{}, _) = fatal 547 "invalid network"

-- | Get the colorset of the channel identified by the given channelID
getColorSet :: INetwork n a (WithColors b) => n a (WithColors b) -> ChannelID -> ColorSet
getColorSet net node = snd (channel net node)

-- | Fold over a list of objects, and ignore objects that evaluate to a @Nothing@ value
foldlAllMaybe :: (a -> b -> Maybe a) -> a -> [b] -> Maybe a
foldlAllMaybe _ _ [] = Nothing
foldlAllMaybe f a (b:bs) = case f a b of
    Nothing -> foldlAllMaybe f a bs
    Just a' -> case foldlAllMaybe f a' bs of
                Nothing -> Just a'
                Just a''-> Just a''

-- | Update the colorset of the channel identified by the given channelID to the given colorset.
-- Returns @Nothing@ if the given colorset is equal to the old colorset of the channel.
updateType :: (IsColorSet c, Show b) => Network a (WithColors b) -> ChannelID -> c -> Maybe (Network a (WithColors b))
updateType net node newType =
    if getColorSet net node == (toColorSet newType) then Nothing else Just (adjustChannel net f node) where
        f (lab, _) = (lab, toColorSet newType)

-------------------------------------
-- MaDLNetwork type classes
-------------------------------------

-- | Class that allows to test whether components and/or macros are of a certain type
class MayBeQueue c where
    isAutomaton    :: c -> Bool
    isFunction     :: c -> Bool
    isQueue        :: c -> Bool
    isSink         :: c -> Bool
    isSource       :: c -> Bool
    isCJoin        :: c -> Bool
    isFJoin        :: c -> Bool
    isFork         :: c -> Bool    
    isSwitch       :: c -> Bool 
    isMerge        :: c -> Bool
    isLoadBalancer :: c -> Bool
    isGuardQueue   :: c -> Bool
    getTransitions :: c -> [AutomatonTransition]
instance MayBeQueue (XComponentOrMacro b c) where
    isAutomaton (C comp)    = isAutomaton comp
    isAutomaton (M _)       = False
    isFunction (C comp)     = isFunction comp
    isFunction (M _)        = False
    isQueue (C comp)        = isQueue comp
    isQueue (M _)           = False
    isSink (C comp)         = isSink comp
    isSink (M _)            = False
    isSource (C comp)       = isSource comp
    isSource (M _)          = False
    isCJoin (C comp)        = isCJoin comp
    isCJoin (M _)           = False
    isFJoin (C comp)        = isFJoin comp
    isFJoin (M _)           = False
    isFork (C comp)         = isFork comp
    isFork (M _)            = False
    isSwitch (C comp)       = isSwitch comp
    isSwitch (M _)          = False
    isMerge (C comp)        = isMerge comp
    isMerge (M _)           = False
    isLoadBalancer (C comp) = isLoadBalancer comp
    isLoadBalancer (M _)    = False
    isGuardQueue (C comp)   = isGuardQueue comp
    isGuardQueue (M _)      = False
    getTransitions (C comp) = getTransitions comp
    getTransitions (M _)    = []
instance MayBeQueue (XComponent c) where
    isAutomaton Automaton{}       = True
    isAutomaton _                 = False
    isFunction Function{}         = True
    isFunction _                  = False
    isQueue Queue{}               = True
    isQueue _                     = False
    isSink Sink{}                 = True
    isSink DeadSink{}             = True
    isSink _                      = False
    isSource Source{}             = True
    isSource PatientSource{}      = True
    isSource _                    = False
    isCJoin ControlJoin{}         = True
    isCJoin _                     = False
    isFJoin FControlJoin{}        = True
    isFJoin _                     = False
    isFork Fork{}                 = True
    isFork _                      = False
    isSwitch Switch{}             = True
    isSwitch _                    = False
    isMerge Merge{}               = True
    isMerge _                     = False
    isLoadBalancer LoadBalancer{} = True
    isLoadBalancer _              = False
    isGuardQueue GuardQueue{}     = True
    isGuardQueue _                = False
    getTransitions a@Automaton{}  = transitions a
    getTransitions _ = []

-- | Class to convenient get and set the names of components, channels, macroinstances and macros
class HasName a b where
    getName :: a -> b
    setName :: b -> a -> a
instance HasName (XComponentOrMacro b c) c where
    getName (C comp) = getName comp
    getName (M macr) = getName macr
    setName name (C comp) = C $ setName name comp
    setName name (M macr) = M $ setName name macr
instance HasName (XComponent c) c where
    getName = componentName
    setName name comp = comp {componentName = name}
instance HasName (XMacroInstance b c) c where
    getName = instanceName
    setName name macr = macr {instanceName = name}
instance HasName (XChannel c) c where
    getName = channelName
    setName name chan = chan {channelName = name}
instance HasName (XMacro b c) Text where
    getName = macroName
    setName name macr = macr {macroName = name}
instance HasName a b => HasName (WithColors a) b where
    getName (x, _) = getName x
    setName name (x, t) = (setName name x, t)



-- | Get the name of a component as a single string
getNameText :: HasName a [Text] => a -> Text
getNameText = (T.intercalate "__") . getName

-- | Wrap the name of a component in a singleton list
getNameList :: HasName a c => a -> [c]
getNameList = (:[]) . getName

-- | Class to convert the names of channels, components and entire networks between 'Text' and '[Text]'
class Flattened a b where
    unflatten :: a -> b
    flatten :: b -> a
instance Flattened b' b => Flattened (XComponentOrMacro b' [Text]) (XComponentOrMacro b Text) where
    unflatten (C comp) = C $ unflatten comp
    unflatten (M macr) = M $ unflatten macr
    flatten (C comp) = C $ flatten comp
    flatten (M macr) = M $ flatten macr
instance Flattened (XComponent [Text]) (XComponent Text) where
    unflatten c@(Source _ msg) = Source (getNameText c) msg
    unflatten c@(PatientSource _ msg) = PatientSource (getNameText c) msg
    unflatten c@Sink{} = Sink (getNameText c)
    unflatten c@DeadSink{} = DeadSink (getNameText c)
    unflatten c@(Function _ fun rt) = Function (getNameText c) fun rt
    unflatten c@(Queue _ cap) = Queue (getNameText c) cap
    unflatten c@Vars{} = Vars $ getNameText c
    unflatten c@Cut{} = Cut $ getNameText c
    unflatten c@(Switch _ swtch) = Switch (getNameText c) swtch
    unflatten c@Merge{} = Merge (getNameText c)
    unflatten c@Fork{} = Fork (getNameText c)
    unflatten c@ControlJoin{} = ControlJoin (getNameText c)
    unflatten c@(FControlJoin _ fun) = FControlJoin (getNameText c) fun
    unflatten c@(Match _ fun) = Match (getNameText c) fun
    unflatten c@(MultiMatch _ fun) = MultiMatch (getNameText c) fun
    unflatten c@LoadBalancer{} = LoadBalancer (getNameText c)
    unflatten c@(Automaton _ ins outs n ts stm) = Automaton (getNameText c) ins outs n ts stm
    unflatten c@(Joitch _ preds) = Joitch (getNameText c) preds
    unflatten c@(GuardQueue _ cap) = GuardQueue (getNameText c) cap
    flatten (Source name msg) = Source [name] msg
    flatten (PatientSource name msg) = PatientSource [name] msg
    flatten (Sink name) = Sink [name]
    flatten (DeadSink name) = DeadSink [name]
    flatten (Function name fun rt) = Function [name] fun rt
    flatten (Queue name cap) = Queue [name] cap
    flatten (Vars name) = Vars [name]
    flatten (Cut name) = Cut [name]
    flatten (Switch name swtch) = Switch [name] swtch
    flatten (Merge name) = Merge [name]
    flatten (Fork name) = Fork [name]
    flatten (ControlJoin name) = ControlJoin [name]
    flatten (FControlJoin name fun) = FControlJoin [name] fun
    flatten (Match name fun) = Match [name] fun
    flatten (MultiMatch name fun) = MultiMatch [name] fun
    flatten (LoadBalancer name) = LoadBalancer [name]
    flatten (Automaton name ins outs n ts stm) = Automaton [name] ins outs n ts stm
    flatten (Joitch name preds) = Joitch [name] preds
    flatten (GuardQueue name cap) = GuardQueue [name] cap
instance Flattened b' b => Flattened (XMacroInstance b' [Text]) (XMacroInstance b Text) where
    unflatten m@(MacroInstance _ macr) = MacroInstance (getNameText m) (unflatten macr)
    flatten (MacroInstance name macr) = MacroInstance [name] (flatten macr)
instance Flattened FlatChannel Channel where
    unflatten c = Channel (getNameText c)
    flatten c = Channel [getName c]
instance Flattened b' b => Flattened (WithColors b') (WithColors b) where
    unflatten = mapFst unflatten
    flatten = mapFst flatten
instance Flattened b' b => Flattened (XMacro b' [Text]) (XMacro b Text) where
    unflatten (Macro ifx name net) = Macro ifx name (unflatten net)
    flatten (Macro ifx name net) = Macro ifx name (flatten net)
instance (Show b', Show b, Flattened a' a, Flattened b' b) => Flattened (Network a' b') (Network a b) where
    unflatten = mapOnComponentsAndChannels unflatten unflatten
    flatten = mapOnComponentsAndChannels flatten flatten
instance (Flattened a' a, Flattened b' b) => Flattened (MacroNetwork a' b') (MacroNetwork a b) where
    unflatten = mapOnComponentsAndChannels unflatten unflatten
    flatten = mapOnComponentsAndChannels flatten flatten

-- | Remove the colors from a colored net
removeColors :: (INetwork n a (WithColors b), INetwork n a b) => n a (WithColors b) -> n a b
removeColors = mapOnChannels fst

-------------------------------------
-- MaDLNetwork queries
-------------------------------------

-- | Get all componentIDs of a network
getComponentIDs :: INetwork n a b => n a b -> [ComponentID]
getComponentIDs = components

-- | Get all components of a network
getComponents :: INetwork n a b => n a b -> [a]
getComponents net = map (component net) (components net)

-- | Get all components of a network, including their id-number
getComponentsWithID :: INetwork n a b => n a b -> [(ComponentID, a)]
getComponentsWithID net = map (\i -> (i, component net i)) (components net)

-- | Get all queues of a network
getAllQueues :: INetwork n (XComponent c) b => n (XComponent c) b -> [XComponent c] 
getAllQueues net = filter isQueue (getComponents net)

-- | Get all switches of a network
getAllSwitches :: INetwork n (XComponent c) b => n (XComponent c) b -> [XComponent c]
getAllSwitches net = filter isSwitch (getComponents net)

-- | Get all sources of a network
-- Note: PatientSources are included.
getAllSources :: INetwork n (XComponent c) b => n (XComponent c) b -> [XComponent c]
getAllSources net = filter isSource (getComponents net)

-- | Get all sinks of a network
getAllSinks :: INetwork n (XComponent c) b => n (XComponent c) b -> [XComponent c]
getAllSinks net = filter isSink (getComponents net)

-- | Get all merges of a network
getAllMerges :: INetwork n (XComponent c) b => n (XComponent c) b -> [XComponent c]
getAllMerges network = filter isMerge (getComponents network)

-- | Get all FControlJoins with ID of a network
getAllFJoinsWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllFJoinsWithID net = filter (isFJoin . snd) (getComponentsWithID net)

-- | Get all Functions with ID of a network
getAllFunctionsWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllFunctionsWithID net = filter (isFunction . snd) (getComponentsWithID net)

-- | Get all processes with ID of a network
getAllProcessesWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllProcessesWithID net = filter (isAutomaton . snd) (getComponentsWithID net)

-- | Get all processes without ID
getAllProcesses :: INetwork n (XComponent c) b => n (XComponent c) b -> [XComponent c]
getAllProcesses net = filter isAutomaton (getComponents net)

-- | Get the state map of an automaton
getAutomatonStateMap :: (XComponent c) -> PStateNrMap
getAutomatonStateMap comp = case comp of 
     Automaton{stateMap = x} -> x
     _ -> Data.Map.empty

-- | Get state map with process name
getAutomatonStateMapWithProcessName ::  XComponent c -> Maybe (c, PStateNrMap)
getAutomatonStateMapWithProcessName comp = case comp of 
   Automaton{componentName = name,stateMap = x} -> Just (name,x)
   _ -> Nothing

ppState :: PState -> String
ppState (txt, c) = (show txt)++","++(show c)

ppStateMap1 :: PStateNrMap -> String
ppStateMap1 pStateMap = 
   let f key x = "STATE "++(ppState key)++","++(show x)++";"
       mapped = Data.Map.mapWithKey f pStateMap
   in concat $ Data.Map.elems mapped

prettyPrintStateMap :: (Show c) => Maybe (c, PStateNrMap) -> String
prettyPrintStateMap stMapWithName = case stMapWithName of
    Just (name, stMap) -> "PROCESS "++(show name)++","++(ppStateMap1 stMap)
    Nothing -> ""

-- | Get all queues with ID of a network
getAllQueuesWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllQueuesWithID net = filter (isQueue . snd) (getComponentsWithID net)

-- | Get all switches with ID of a network
getAllSwitchesWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllSwitchesWithID net = filter (isSwitch . snd) (getComponentsWithID net)

-- | Get all sources with ID of a network.
-- Note: PatientSources are included. 
getAllSourcesWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllSourcesWithID net = filter (isSource . snd) (getComponentsWithID net)

-- | Get all merges with ID of a network
getAllMergesWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllMergesWithID net = filter (isMerge . snd) (getComponentsWithID net)

-- | Get ID's of all sources of a network
getAllSourceIDs :: INetwork n (XComponent c) b => n (XComponent c) b -> [ComponentID]
getAllSourceIDs net = map fst (getAllSourcesWithID net)

-- | Get all sinks with ID of a network
getAllSinksWithID :: INetwork n (XComponent c) b => n (XComponent c) b -> [(ComponentID, XComponent c)]
getAllSinksWithID net = filter (isSink . snd) (getComponentsWithID net)

-- | Find a specific component of a network, searching by id-number
getComponent :: INetwork n a b => n a b -> ComponentID -> a
getComponent = component

-- | Find a specific component of its network, including its incoming and outgoing channels, searching by id-number
getComponentContext :: Show b => Network a b -> ComponentID -> ComponentContext a
getComponentContext = componentContext

-- | Find all outgoing channels of a specific component of a network
getOutChannels :: INetwork n a b => n a b -> ComponentID -> [ChannelID]
getOutChannels = out

-- | Find all incoming channels of a specific component of a network
getInChannels :: INetwork n a b => n a b -> ComponentID -> [ChannelID]
getInChannels = inn

-- | Find the number of outgoing channels of a specific component of a network
getNrOutputs :: INetwork n a b => n a b -> ComponentID -> Int
getNrOutputs net = length . out net

-- | Find the number of incoming channels of a specific component of a network
getNrInputs :: INetwork n a b => n a b -> ComponentID -> Int
getNrInputs net = length . inn net

-- | Find all incoming and outgoing channels of a specific component of a network
getAllChannels :: INetwork n a b => n a b -> ComponentID -> [ChannelID]
getAllChannels network node = getInChannels network node ++ getOutChannels network node

-- | Find a specific componentID of a network, searching by name
findComponentID :: (Eq c, HasName a c, INetwork n a b) => n a b -> c -> Maybe ComponentID
findComponentID net = fmap fst . findComponentWithID net

-- | Find a specific component of a network, searching by name
findComponent :: (Eq c, HasName a c, INetwork n a b) => n a b -> c -> Maybe a
findComponent net = fmap snd . findComponentWithID net

-- | Find a specific component of a network, including its id-number, searching by name
findComponentWithID :: (Eq c, HasName a c, INetwork n a b) => n a b -> c -> Maybe (ComponentID, a)
findComponentWithID network = findComponent' componentOrMacros where
    componentOrMacros = getComponentsWithID network
    findComponent' [] _ = Nothing
    findComponent' ((node, comp):comps) name
        | getName comp == name  = Just (node, comp)
        | otherwise             = findComponent' comps name

-- | Get all channelsIDs of a network
getChannelIDs :: INetwork n a b => n a b -> [ChannelID]
getChannelIDs = channels

-- | Get all channels of a network
getChannels :: INetwork n a b => n a b -> [b]
getChannels net = map (channel net) (channels net)

-- | Get all channels of a network, including their id-number
getChannelsWithID :: INetwork n a b => n a b -> [(ChannelID, b)]
getChannelsWithID net = map (\i -> (i, channel net i)) (channels net)

-- | Find a specific channel of a network, searching by id-number
getChannel :: INetwork n a b => n a b -> ChannelID -> b
getChannel = channel

-- | Find a specific channel of its network, including its initiator and target, searching by id-number
getChannelContext :: Network a b -> ChannelID -> ChannelContext b
getChannelContext = channelContext

-- | Find the initiator component of a specific channel of a network
getInitiator :: Network a b -> ChannelID -> ComponentID
getInitiator = initiator

-- | Find the target component of a specific channel of a network
getTarget :: Network a b -> ChannelID -> ComponentID
getTarget = target

-- | Find the initiator component of a specific channel of network,
--    including the portnumber this channel is connected to.
getInitiatorWithPort :: Network a b -> ChannelID -> (ComponentID, Int)
getInitiatorWithPort net x = (c, fromMaybe (fatal 144 "network is invalid") $ elemIndex x is) where
    c = getInitiator net x
    is = getOutChannels net c

-- | Find the target component of a specific channel of network,
--    including the portnumber this channel is connected to.
getTargetWithPort :: Network a b -> ChannelID -> (ComponentID, Int)
getTargetWithPort net x = (c, fromMaybe (fatal 144 "network is invalid") $ elemIndex x is) where
    c = getTarget net x
    is = getInChannels net c

-- | Try to find the initiator component of a specific channel of a network
getMInitiator :: INetwork n a b => n a b -> ChannelID -> Maybe ComponentID
getMInitiator = mInitiator

-- | Try to find the target component of a specific channel of a network
getMTarget :: INetwork n a b => n a b -> ChannelID -> Maybe ComponentID
getMTarget = mTarget

-- | Find a specific channelID of a network, searching by name
findChannelID :: (Eq c, HasName b c, INetwork n a b) => n a b -> c -> Maybe ChannelID
findChannelID net = (fmap fst) . (findChannelWithID net)

-- | Find a specific channel of a network, searching by name
findChannel :: (Eq c, HasName b c, INetwork n a b) => n a b -> c -> Maybe b
findChannel net = (fmap snd) . (findChannelWithID net)

-- | Find a specific channel of a network, including its id-number, searching by name
findChannelWithID :: (Eq c, HasName b c, INetwork n a b) => n a b -> c -> Maybe (ChannelID, b)
findChannelWithID network = findChannel' xs where
    xs = getChannelsWithID network
    findChannel' [] _ = Nothing
    findChannel' ((node, chan):chans) name
        | getName chan == name  = Just (node, chan)
        | otherwise             = findChannel' chans name

-- | Get all macros of a network
getMacros :: forall n b c. (Ord c, INetwork n (XComponentOrMacro b c) b) =>
    n (XComponentOrMacro b c) b -> [XMacro b c]
getMacros network = sortMacros $ getMacros' (macrosTop network) Hash.empty where
    macrosTop network' = Hash.elems $ Hash.fromList [(getName macro :: Text, macro) | M macroInst <- getComponents network', let macro = instanceMacro macroInst]

    getMacros' :: [XMacro b c] -> Hash.Map Text (XMacro b c, [Text]) -> Hash.Map Text (XMacro b c, [Text])
    getMacros' macros m = foldr getMacro' m macros where
        getMacro' macro macroMap = if Hash.member name macroMap
            then macroMap
            else getMacros' macroMacros (Hash.insert name (macro, map getName macroMacros) macroMap) where
                name = getName macro
                macroMacros = macrosTop $ macroNetwork macro

    sortMacros :: Hash.Map Text (XMacro b c, [Text]) -> [XMacro b c]
    sortMacros macromap = if Hash.null macromap then []
        else map fst (Hash.elems topMacros) ++ sortMacros (Hash.map removeTopNames remainingMacros) where
            removeTopNames :: (XMacro b c, [Text]) -> (XMacro b c, [Text])
            removeTopNames (macro, names) = (macro, names \\ Hash.keys topMacros)
            topMacros, remainingMacros :: Hash.Map Text (XMacro b c, [Text])
            (topMacros, remainingMacros) = Hash.partition (null . snd) macromap

-- | Get the macro of the given name (if it exists)
getMacro :: (Ord c, INetwork n (XComponentOrMacro b c) b) => n (XComponentOrMacro b c) b -> Text -> Maybe (XMacro b c)
getMacro network name = case filter ((== name) . getName) (getMacros network) of
    [] -> Nothing
    macro:_ -> Just macro

-- | Returns true if the given macro name is the name of the given macro,
--   or if the one of the components inside the given macro is a macroInstance
--   of the given macro name
containsMacro :: forall b c. Ord c => Text -> XMacro b c -> Bool
containsMacro = containsMacro' [] where
    containsMacro' :: [Text] -> Text -> XMacro b c -> Bool
    containsMacro' seen name macro = mName == name ||
        ( not (mName `elem` seen) && any (containsMacro' (mName:seen) name) macroMacros) where
        mName = getName macro
        macroMacros = getMacros $ macroNetwork macro

-- | Returns the names of all macroInstances of the given macro name
getMacroInstances :: INetwork n (ComponentOrMacro b) b => n (ComponentOrMacro b) b -> Text -> [[Text]]
getMacroInstances network macro = concatMap (getMacroInstances' []) (instances network) where
    getMacroInstances' :: [Text] -> MacroInstance b -> [[Text]]
    getMacroInstances' prefix macroInstance =
           (if instanceType == macro then [prefix'] else [])
        ++ concatMap (getMacroInstances' prefix') (instances mNetwork) where
            instanceType = getName $ instanceMacro macroInstance
            prefix' :: [Text]
            prefix' = prefix ++ getNameList macroInstance
            mNetwork = macroNetwork $ instanceMacro macroInstance

    instances :: INetwork n (ComponentOrMacro b) b => n (ComponentOrMacro b) b -> [MacroInstance b]
    instances network' = [macroInst | M macroInst <- getComponents network', containsMacro macro (instanceMacro macroInst)]

-- | Get the input- and output-channels of a component. Useful for getting the instanceChannels of a macroInstance.
getInstanceChannels :: INetwork n a b => n a b -> ComponentID -> [ChannelID]
getInstanceChannels n c = is++ts where
    (is, _, ts) = componentContext n c

-- | Get the types of the input channels of a specific component
inputTypes :: INetwork n a (WithColors b) => n a (WithColors b) -> ComponentID -> [ColorSet]
inputTypes network node = map (getColorSet network) (inn network node)

-- | Get the types of the output channels of a specific component
outputTypes :: INetwork n a (WithColors b) => n a (WithColors b) -> ComponentID -> [ColorSet]
outputTypes network node = map (getColorSet network) (out network node)

-- | Get all type names used in the network (in sources, predicates and functions)
networkTypes :: INetwork n (XComponent c) b => n (XComponent c) b -> [Text]
networkTypes = Set.toList . foldr (addTypes) Set.empty . getComponents where
    addTypes :: XComponent c -> Set Text -> Set Text
    addTypes comp names = Set.union names $ case comp of
        Automaton{} -> Set.empty  -- TODO(snnw)  might be required
        ControlJoin{} -> Set.empty
        DeadSink{} -> Set.empty
        FControlJoin _ p -> mfboolTypes p
        Fork{} -> Set.empty
        Function _ f _ -> mfdisjTypes f
        Joitch _ ps -> Set.unions $ map mfboolTypes ps
        LoadBalancer{} -> Set.empty
        Match _ p -> mfboolTypes p
        Merge{} -> Set.empty
        MultiMatch _ p -> mfboolTypes p
        PatientSource _ msg -> Set.fromList $ colorTypes msg
        Queue{} -> Set.empty
        Sink{} -> Set.empty
        Source _ msg -> Set.fromList $ colorTypes msg
        Switch _ sws -> Set.unions $ map mfboolTypes sws
        Vars{} -> Set.empty
        Cut{} -> Set.empty
        GuardQueue{} -> Set.empty

    colorTypes :: ColorSet -> [Text]
    colorTypes cs = colorSetKeys cs ++ concat (map (either structTypes (const [])) $ colorSetElems cs)
    structTypes :: Struct -> [Text]
    structTypes = concat . map (either colorTypes $ const []) . structElems

    mfboolTypes :: MFunctionBool -> Set Text
    mfboolTypes mfbool = case mfbool of
        XCompare _ val1 val2 -> Set.union (mfvalTypes val1) (mfvalTypes val2)
        XMatch disj1 disj2 -> Set.union (mfdisjTypes disj1) (mfdisjTypes disj2)
        XTrue -> Set.empty
        XFalse -> Set.empty
        XUnOpBool _ bool -> mfboolTypes bool
        XBinOpBool _ bool1 bool2 -> Set.union (mfboolTypes bool1) (mfboolTypes bool2)
        XAppliedToB bool disjs -> Set.union (Set.unions $ map mfdisjTypes disjs) (mfboolTypes bool)
        XSelectB disj sels -> Set.unions [Set.unions . map mfboolTypes $ Hash.elems sels, mfdisjTypes disj, Set.fromList $ Hash.keys sels]
        XIfThenElseB bool1 bool2 bool3 -> Set.unions [mfboolTypes bool1, mfboolTypes bool2, mfboolTypes bool3]
    mfdisjTypes :: MFunctionDisj -> Set Text
    mfdisjTypes mfdisj = case mfdisj of
        XChoice val structOrVal -> Set.insert val $ either mfstructTypes mfvalTypes structOrVal
        XSelect disj sels -> Set.unions [Set.unions . map mfdisjTypes $ Hash.elems sels, mfdisjTypes disj, Set.fromList $ Hash.keys sels]
        XIfThenElseD bool disj1 disj2 -> Set.unions [mfboolTypes bool, mfdisjTypes disj1, mfdisjTypes disj2]
        XInput{} -> Set.empty
        XAppliedTo disj disjs -> Set.union (Set.unions $ map mfdisjTypes disjs) (mfdisjTypes disj)
        XVar{} -> Set.empty
        XGetFieldDisj _ struct -> mfstructTypes struct
    mfstructTypes :: MFunctionStruct -> Set Text
    mfstructTypes mfstruct = case mfstruct of
        XConcat flds -> Set.unions . map (either mfdisjTypes mfvalTypes) $ Hash.elems flds
        XChooseStruct val disj -> Set.insert val $ mfdisjTypes disj
        XIfThenElseC bool struct1 struct2 -> Set.unions [mfboolTypes bool, mfstructTypes struct1, mfstructTypes struct2]
    mfvalTypes :: MFunctionVal -> Set Text
    mfvalTypes mfval = case mfval of
        XConst{} -> Set.empty
        XUnOp _ val -> mfvalTypes val
        XBinOp _ val1 val2 -> Set.union (mfvalTypes val1) (mfvalTypes val2)
        XChooseVal val disj -> Set.insert val $ mfdisjTypes disj
        XGetFieldVal _ struct -> mfstructTypes struct
        XIfThenElseV bool val1 val2 -> Set.unions [mfboolTypes bool, mfvalTypes val1, mfvalTypes val2]

getStructFields :: ColorSet -> [Text]
getStructFields (ColorSet cs) = let cs' = Set.toList cs
                                in Set.toList $ Set.unions $ map (\x -> getStructFields' x) cs' 
  where getStructFields' :: Color -> Set Text
        getStructFields' (Color _ (Left (VStruct h))) = let ks = Set.fromList $ Hash.keys h
                                                            vs = map (\x -> let Left c = x in c)
                                                                 $ filter (\x -> case x of Left _ -> True; _ -> False)
                                                                 $ map (\(_,x) -> x) (Hash.toList h)
                                                            ns = map (\x -> getStructFields' x) vs
                                                        in Set.unions (ns ++ [ks])
        getStructFields' (Color _ _) = Set.empty

-- | Get all field names used in a network's structs
networkStructFields :: INetwork n (XComponent c) b => n (XComponent c) b -> [Text]
networkStructFields = Set.toList . foldr (addStructFields) Set.empty . getComponents where
    addStructFields :: XComponent c -> Set Text -> Set Text
    addStructFields comp names = Set.union names $ case comp of
        Automaton{} -> Set.empty  
        ControlJoin{} -> Set.empty
        DeadSink{} -> Set.empty
        FControlJoin _ p -> mfboolFields p
        Fork{} -> Set.empty
        Function _ f _ -> mfdisjFields f
        Joitch _ ps -> Set.unions $ map mfboolFields ps
        LoadBalancer{} -> Set.empty
        Match _ p -> mfboolFields p
        Merge{} -> Set.empty
        MultiMatch _ p -> mfboolFields p
        PatientSource _ msg -> Set.fromList $ getStructFields msg
        Queue{} -> Set.empty
        Sink{} -> Set.empty
        Source _ msg -> Set.fromList $ getStructFields msg
        Switch _ sws -> Set.unions $ map mfboolFields sws
        Vars{} -> Set.empty
        Cut{} -> Set.empty
        GuardQueue{} -> Set.empty

    mfboolFields :: MFunctionBool -> Set Text
    mfboolFields mfbool = case mfbool of
        XCompare _ val1 val2 -> Set.union (mfvalFields val1) (mfvalFields val2)
        XMatch disj1 disj2 -> Set.union (mfdisjFields disj1) (mfdisjFields disj2)
        XTrue -> Set.empty
        XFalse -> Set.empty
        XUnOpBool _ bool -> mfboolFields bool
        XBinOpBool _ bool1 bool2 -> Set.union (mfboolFields bool1) (mfboolFields bool2)
        XAppliedToB bool disjs -> Set.union (Set.unions $ map mfdisjFields disjs) (mfboolFields bool)
        XSelectB disj sels -> Set.unions [Set.unions . map mfboolFields $ Hash.elems sels, mfdisjFields disj, Set.fromList $ Hash.keys sels]
        XIfThenElseB bool1 bool2 bool3 -> Set.unions [mfboolFields bool1, mfboolFields bool2, mfboolFields bool3]
    mfdisjFields :: MFunctionDisj -> Set Text
    mfdisjFields mfdisj = case mfdisj of
        XChoice _ structOrVal -> either mfstructFields mfvalFields structOrVal
        XSelect disj sels -> Set.unions [Set.unions . map mfdisjFields $ Hash.elems sels, mfdisjFields disj, Set.fromList $ Hash.keys sels]
        XIfThenElseD bool disj1 disj2 -> Set.unions [mfboolFields bool, mfdisjFields disj1, mfdisjFields disj2]
        XInput{} -> Set.empty
        XAppliedTo disj disjs -> Set.union (Set.unions $ map mfdisjFields disjs) (mfdisjFields disj)
        XVar{} -> Set.empty
        XGetFieldDisj _ struct -> mfstructFields struct
    mfstructFields :: MFunctionStruct -> Set Text
    mfstructFields mfstruct = case mfstruct of
        XConcat flds -> Set.unions . map (either mfdisjFields mfvalFields) $ Hash.elems flds
        XChooseStruct x disj -> Set.insert x $ mfdisjFields disj
        XIfThenElseC bool struct1 struct2 -> Set.unions [mfboolFields bool, mfstructFields struct1, mfstructFields struct2]
    mfvalFields :: MFunctionVal -> Set Text
    mfvalFields mfval = case mfval of
        XConst{} -> Set.empty
        XUnOp _ _ -> Set.empty
        XBinOp _ val1 val2 -> Set.union (mfvalFields val1) (mfvalFields val2)
        XChooseVal _ disj -> mfdisjFields disj
        XGetFieldVal _ struct -> mfstructFields struct
        XIfThenElseV bool val1 val2 -> Set.unions [mfboolFields bool, mfvalFields val1, mfvalFields val2]

----------------------------
-- Network Operations
----------------------------

-- | Pairs an object with a name map
type WithNameMap a = (a, Hash.Map [Text] [Text])

-- | Transform a network to a flattened network with a namemap that maps the names of channels
--   in the unflattened network to the names of their corresponding channels in the flattened network.
unfoldMacrosWithNameMap :: forall n b b'. (Show b, Show b', HasName b Text, HasName b' [Text], Flattened b' b) =>
    (INetwork n (XComponentOrMacro b Text) b, INetwork n (XComponentOrMacro b' [Text]) b', INetwork n (XComponent [Text]) b') =>
        n (XComponentOrMacro b Text) b -> WithNameMap (n (XComponent [Text]) b')
unfoldMacrosWithNameMap network = (cast flattenedNetwork, nameMap)
    where
    flattenedNetwork :: n (XComponentOrMacro b' [Text]) b'
    (flattenedNetwork, nameMap) = foldr unfoldMacroWithNameMap (flatnet, Hash.empty) macroInstances

    flatnet :: n (XComponentOrMacro b' [Text]) b'
    flatnet = mapOnComponentsAndChannels flatten flatten network

    macroInstances :: [(ComponentID, XMacroInstance b Text)]
    macroInstances = [(node, macroInst) | (node, M macroInst) <- getComponentsWithID network ]

    unfoldMacroWithNameMap :: (ComponentID, XMacroInstance b Text) -> WithNameMap (n (XComponentOrMacro b' [Text]) b')
                                                                    -> WithNameMap (n (XComponentOrMacro b' [Text]) b')
    unfoldMacroWithNameMap (node, macroInst) (network', namemap) =
        expandMacroWithNameMap node macroInst (network', namemap)

-- | Unfold a specific macro in a network, with a namemap
expandMacroWithNameMap :: forall n b b'. (Show b, Show b', HasName b Text, HasName b' [Text], Flattened b' b) =>
    (INetwork n (XComponentOrMacro b Text) b, INetwork n (XComponentOrMacro b' [Text]) b') =>
        ComponentID -> XMacroInstance b Text -> WithNameMap (n (XComponentOrMacro b' [Text]) b') -> WithNameMap (n (XComponentOrMacro b' [Text]) b')
expandMacroWithNameMap node macroInstance (network, nameMap) = (net, hmap'') where
    (flatMacro, deepMap) = mapFst rename (unfoldMacrosWithNameMap mNet)
    rename :: MacroNetwork (XComponent [Text]) b' -> MacroNetwork (XComponent [Text]) b'
    rename = mapOnComponents (prefixName mInstName) . mapOnChannels (prefixName mInstName)
    macroDef = instanceMacro macroInstance
    mNet :: MacroNetwork (XComponentOrMacro b Text) b
    mNet = macroNetwork macroDef
    mNet_flat :: MacroNetwork (XComponentOrMacro b' [Text]) b'
    mNet_flat = flatten mNet
    (is, ts) = splitInterface macroDef
    net :: n (XComponentOrMacro b' [Text]) b'
    (net, ifx) = replaceComponentWithNetwork network node (cast' flatMacro) is ts
    hmap = Hash.fromList $ map (\(internalOld,new) -> (channelInMacroName internalOld, xName net new)) ifx
    hmap' = Hash.union nameMap hmap
    hmap'' :: Hash.Map [Text] [Text]
    hmap'' =  Hash.foldWithKey transferName hmap' deepMap
    mInstName :: Text
    mInstName = getName macroInstance

    transferName :: [Text] -> [Text] -> Hash.Map [Text] [Text] -> Hash.Map [Text] [Text]
    transferName key value namemap' = case Hash.lookup (mInstName : value) namemap' of
        Nothing -> Hash.insert (mInstName : key) (mInstName : value) namemap'
        Just value' -> Hash.insert (mInstName : key) value' namemap'

    prefixName :: HasName a' [c'] => c' -> a' -> a'
    prefixName prefix x = setName (prefix : getName x) x
    channelInMacroName :: ChannelID -> [Text]
    channelInMacroName x =  mInstName : xName mNet_flat x
    xName :: (INetwork n' a' d, HasName d c') => n' a' d -> (ChannelID -> c')
    xName net' = getName . (channel net')

-- TODO(tssb) make a unit test to check correctness of the name map

-- | Transform a network to a flattened network
unfoldMacros :: (Show b, Show b', HasName b Text, HasName b' [Text], Flattened b' b) =>
    (INetwork n (XComponentOrMacro b Text) b, INetwork n (XComponentOrMacro b' [Text]) b', INetwork n (XComponent [Text]) b') =>
        n (XComponentOrMacro b Text) b -> n (XComponent [Text]) b'
unfoldMacros = fst . unfoldMacrosWithNameMap

-- | Cast a network where the components are of type 'ComponentOrMacro', but does not containing any macro-instances,
-- to a network where the components are of type 'Component'
cast :: (INetwork n (XComponentOrMacro b' c) b', INetwork n (XComponent c) b') => n (XComponentOrMacro b' c) b' -> n (XComponent c) b'
cast network = mapOnComponents f network where
    f (C c) = c
    f (M _) = fatal 451 "Cast on network containing macros"

-- | Cast a network where the components are of type 'Component', to a network where the components are of type 'ComponentOrMacro'
cast' :: (INetwork n (XComponentOrMacro b' c) b', INetwork n (XComponent c) b') => n (XComponent c) b' -> n (XComponentOrMacro b' c) b'
cast' flatNetwork = mapOnComponents C flatNetwork

-- | Remove all dead parts from a typed network
pruneNetwork :: forall c. Show c => XColoredNetwork c -> XColoredNetwork c
pruneNetwork network = mapOnComponentsContext pruneComponent network where
    pruneComponent :: ComponentContext (XComponent c) -> Either (ComponentContext (XComponent c)) ChannelID
    pruneComponent context@(is, c, os) =
        if keepComponent context then
            Left (is, c, os)
        else case c of
            ControlJoin name -> if any isAlive is then Left (is, DeadSink name, os)
                                else Right (head $ filter isAlive os)
            _ -> Right (head $ filter isAlive os)

    keepComponent (is, _, os) = all isAlive (is ++ os)

    isAlive :: ChannelID -> Bool
    isAlive = not . emptyColorSet . snd . getChannel network

-- | Divide the interface of a macro into incoming- and outgoing interface channels
splitInterface :: XMacro b c -> ([ChannelID], [ChannelID])
splitInterface macro = partition (isJust . mTarget network) (macroInterface macro) where
    network = macroNetwork macro

---------------------------------------------------
-- Valid MaDL network and MaDL macro definitions --
---------------------------------------------------

-- | Error type resulting from function 'validMaDLNetwork'
type Error = String

{- |
    The 'validMaDLNetwork' functions checks if a network is valid as a MaDL Network.
   1. Channels must be connected to two components
   2. Components must be connected to the correct number of input and output channels
   3. Component-, MacroInstance-, and Channel-names must be unique
   4. All macros must be valid
   5. Arguments of all components must be valid: -> Check this condition last! Typepropagation is needed to check this condition,
                                                                                 which may fail if some of the other conditions are not met.
      - Queue: its capacity must be at least 1
      - Function: the function applied to its inputtype must yield a valid resulting type.
      - Switch: its switchfunction must be valid, meaning each incoming packet of the switch is routed to exactly one direction.
      - Match: the matchfunctions applied to their inputtypes must result in bittype (boolean) packets.
-}
validMaDLNetwork :: MadlNetwork -> Maybe Error
validMaDLNetwork network
    | not $ null condition1 = Just $ "Not a valid MaDL Network: Some channels are not connected to the right number of components:\n " ++ show condition1
    | not $ null condition2 = Just $ "Not a valid MaDL Network: Some components/macros are not connected to the right number of channels:\n " ++ show condition2
    | not $ null condition3 = Just $ "Not a valid MaDL Network: Some names are not uniquely used:\n " ++ show condition3
    | not $ null condition4 = Just $ show condition4
    | not $ null condition5 = Just $ "Not a valid MaDL Network: Some components have invalid arguments:\n" ++ show condition5
    | otherwise = Nothing where
        condition1::[Text] = [] -- Trivially true by data structure
        condition2 = getWronglyConnectedComponents network
        condition3::[Text] = getDoubleNames network
        condition4 = mapMaybe validMaDLMacro (getMacros network)
        condition5 = getUnvalidArgumentComponents network

{- |
    The 'validMaDLMacro' functions checks if a network is valid as a MaDL Macro Network.
   1. Channels must be connected to one or two components : 1 input and/or 1 output component
   2. Components must be connected to the correct number of input and output channels
   3. Component-, MacroInstance-, and Channel-names must be unique
-}
validMaDLMacro :: forall b c.(HasName b c, Show b, Show c, Ord c) => XMacro b c -> Maybe Error
validMaDLMacro macro
   | not $ null condition1 = Just $ name ++ " is not a valid MaDL Macro: Some channels are not connected to the right number of components:\n " ++ show condition1
   | not $ null condition2 = Just $ name ++ " is not a valid MaDL Macro: Some components/macros are not connected to the right number of channels:\n " ++ show condition2
   | not $ null condition3 = Just $ name ++ " is not a valid MaDL Macro: Some names are not uniquely used:\n " ++ show condition3
   | otherwise = Nothing where
        condition1 = getUnconnectedChannels network
        condition2 = getWronglyConnectedComponents network
        condition3::[c] = getDoubleNames network

        network = macroNetwork macro
        name = T.unpack $ getName macro

-- | Find names of channels not connected to at least one component
getUnconnectedChannels :: (INetwork n a b) => n a b -> [DisconnectedChannelContext b]
getUnconnectedChannels network = map (disconnectedChannelContext network) $ filter (not . atLeastOnePort network) (getChannelIDs network)

-- | Channels must be connected to one or two ports : 1 input and/or 1 output port
atLeastOnePort :: INetwork n a b => n a b -> ChannelID -> Bool
atLeastOnePort network chan = case disconnectedChannelContext network chan of
    (Nothing, _, Nothing) -> False
    _ -> True

-- | Find components and macroinstances that are not connected to the correct amount of ports
getWronglyConnectedComponents :: forall n b c. INetwork n (XComponentOrMacro b c) b =>
    n (XComponentOrMacro b c) b -> [ComponentContext (XComponentOrMacro b c)]
getWronglyConnectedComponents network = mapMaybe f (getComponentsWithID network) where
    f :: (ComponentID, XComponentOrMacro b c) -> Maybe (ComponentContext (XComponentOrMacro b c))
    f (node, compOrMacro)
        | correctNrPorts network (node, compOrMacro) = Nothing
        | otherwise                  = Just (componentContext network node)

-- | Components must be connected to the correct number of input and output ports
correctNrPorts :: INetwork n (XComponentOrMacro b c) b =>
    n (XComponentOrMacro b c) b -> (ComponentID, XComponentOrMacro b c) -> Bool
correctNrPorts network (node, compOrMacro) = requiredInEdges inEdges && requiredOutEdges outEdges && otherRequirements where
    inEdges = getNrInputs network node
    outEdges = getNrOutputs network node
    (requiredInEdges, requiredOutEdges) = case compOrMacro of
        M macro -> getRequiredPortsM (instanceMacro macro)
        C comp -> getRequiredPorts comp
    otherRequirements = case compOrMacro of
        M _ -> True
        C MultiMatch{} -> inEdges > outEdges
        C Joitch{} -> outEdges `mod` 2 == 0
        C _ -> True

-- The correct number of input and output ports for each component
getRequiredPorts :: XComponent c -> (Int -> Bool, Int -> Bool)
getRequiredPorts Source{} = ((== 0), (== 1))
getRequiredPorts PatientSource{} = ((== 0), (== 1))
getRequiredPorts Sink{} = ((== 1), (== 0))
getRequiredPorts DeadSink{} = ((== 1), (== 0))
getRequiredPorts Function{} = ((== 1), (== 1))
getRequiredPorts Queue{} = ((== 1), (== 1))
getRequiredPorts Vars{} = ((== 1), (== 1))
getRequiredPorts Cut{} = ((== 1), (== 1))
getRequiredPorts Switch{} = ((== 1), (>= 2))
getRequiredPorts Merge{} = ((>= 2), (== 1))
getRequiredPorts Fork{} = ((== 1), (>= 2))
getRequiredPorts ControlJoin{} = ((== 2), (== 1))
getRequiredPorts FControlJoin{} = ((== 2), (== 1))
getRequiredPorts Match{} = ((== 2), (== 2))
getRequiredPorts MultiMatch{} = ((>= 2), (>= 1))
getRequiredPorts LoadBalancer{} = ((== 1), (>= 2))
getRequiredPorts (Automaton _ ins outs _ _ _) = ((== ins), (== outs))
getRequiredPorts Joitch{} = ((== 2), (>= 2))
getRequiredPorts GuardQueue{} = ((== 2), (== 1))

-- | The correct number of input and output ports for a macro
getRequiredPortsM :: XMacro b c -> (Int -> Bool, Int -> Bool)
getRequiredPortsM m = ((== length inports), (== length outports)) where
    (inports, outports) = splitInterface m

-- | Find names assigned to multiple components/macroinstances/channels
getDoubleNames :: (Ord c, INetwork n a b, HasName a c, HasName b c) => n a b -> [c]
getDoubleNames network = [ head gr | gr <- group $ sort $ getAllNames network, length gr > 1]

-- | Get a list of all names of components and channels in a network
getAllNames :: (INetwork n a b, HasName a c, HasName b c) => n a b -> [c]
getAllNames network = componentAndMacroNames ++ channelNames where
    componentAndMacroNames = map getName (getComponents network)
    channelNames = map getName $ getChannels network

-- | Get a list of all components with invalid argument(s)
getUnvalidArgumentComponents :: MadlNetwork -> [Error]
getUnvalidArgumentComponents network = mapMaybe (validArguments typednet) $ getComponentsWithID typednet where
    typednet = channelTypes $ unfoldMacros network

-- | Check whether the given component has a valid switchfunction
validArguments :: FlatColoredNetwork -> (ComponentID, FlatComponent) -> Maybe Error
validArguments network (node, comp) = case comp of
    Source{} -> Nothing
    PatientSource{} ->  Nothing
    Sink{} -> Nothing
    DeadSink{} -> Nothing
    Function _ func _ -> if emptyColorSet intype then Nothing else
        case resultingType args (XAppliedTo func [XVar 0]) of
            Left (_::ColorSet) -> Nothing
            Right _ -> Just $ err ["Not a valid function:",  "  " ++ show func, "applied to input type:", "  " ++ show intype]
        where
            args = IM.singleton 0 intype
            [intype] = inputTypes network node
    Queue _ cap -> if cap > 0 then Nothing
        else Just $ err ["Not a valid capacity: " ++ show cap]
    Vars{} -> Nothing
    Cut{} -> Nothing
    Switch _ preds ->
        if not completeSwitchFunction then Just (err ["Switch function is not complete"]) -- :",  "  " ++ show totalSwitchType, "for input type:", "  " ++ show intype])
        else if not nonOverlappingSwitchFunction then Just (err ["Switch function overlaps"])
        else if not correctLengthSwitchFunction then Just (err ["Switch function has incorrect length"])
        else Nothing
        where
            completeSwitchFunction = (Set.fromList $ getColors intype) `Set.isSubsetOf` totalSwitchType
            nonOverlappingSwitchFunction = all (\(t1, t2) -> Set.null $ Set.intersection t1 t2) $ combinations switchResults
            correctLengthSwitchFunction = length preds == getNrOutputs network node
            [intype] = inputTypes network node
            totalSwitchType :: Set Color
            totalSwitchType = Set.unions switchResults
            switchResults :: [Set Color]
            switchResults = map (\p -> Set.fromList $ filter (\c -> predIsTrue p [c]) (getColors intype)) preds
            combinations [] = []
            combinations (a:as) = zip (repeat a) as ++ combinations as
    Merge{} -> Nothing
    Fork{} ->  Nothing
    ControlJoin{} -> Nothing
    FControlJoin _ f -> fmap toError functionResult where
        toError msg = err ["Invalid fcontroljoin function; evaluation of function failed with: " ++show msg]
        functionResult = case resultingType args (XAppliedToB f [XVar 0, XVar 1]) of Left (_::Set Bool) -> Nothing; Right msg -> Just msg; where
        args = IM.fromList [(0, itype1), (1, itype2)]
        itype1:itype2:[] = inputTypes network node
    Match _ f -> fmap toError functionResult where
        toError msg = err ["Invalid match function; evaluation of function failed with: " ++show msg]
        functionResult = case resultingType args (XAppliedToB f [XVar 0, XVar 1]) of Left (_::Set Bool) -> Nothing; Right msg -> Just msg;
        args = IM.fromList [(0, dtype), (1, mtype)]
        mtype:dtype:[] = inputTypes network node
    MultiMatch _ f -> fmap toError functionResult where
        toError msg = err ["Invalid multimatch function; evaluation of function failed with: " ++show msg]
        functionResult = case resultingType args (XAppliedToB f [XVar 0, XVar 1]) of Left (_::Set Bool) -> Nothing; Right msg -> Just msg;
        args = IM.fromList [(0, typeUnions dtypes), (1, typeUnions mtypes)]
        typeUnions = foldr typeUnion nul
        (mtypes, dtypes) = splitAt (getNrOutputs network node) (inputTypes network node)
    LoadBalancer{} -> Nothing
    Automaton _ ins outs n ts _ ->
        if ins <= 0 then Just (err ["Invalid nr of inputs: " ++show ins])
        else if outs <= 0 then Just (err ["Invalid nr of outputs: " ++ show outs])
        else if n <= 0 then Just (err ["Invalid nr of states: " ++ show n])
        else if not (all validTransition ts) then Just (err ["Some transitions are invalid"])
        else Nothing
        where -- TODO(snnw) improve validness with in/out ports checking
            validTransition AutomatonT{startState=start,endState=end} = 0 <= start && start < n && 0 <= end && end < n
    Joitch _ preds ->
        if not completePredicates then Just (err ["Predicates are not complete"])
        else if not uniquePredicates then Just (err ["Predicates are not unique"])
        else if not correctAmmountPredicates then Just (err ["Incorrect number of outputs: expected " ++ show (2 * length preds) ++ ", got " ++ show (getNrOutputs network node)])
        else Nothing
        where
            completePredicates = and $ map or predicateResults
            uniquePredicates = and $ map ((< 2) . length . filter id) predicateResults
            correctAmmountPredicates = 2 * length preds == getNrOutputs network node

            predicateResults :: [[Bool]]
            predicateResults = map (uncurry getResults) allInputs where
                getResults c1 c2 = map (eval $ makeVArguments [c1, c2]) preds
                allInputs = [ (c1, c2) | c1 <- getColors intype1, c2 <- getColors intype2]

            [intype1, intype2] = inputTypes network node
    GuardQueue _ cap -> if cap > 0 then Nothing
        else Just $ err ["Not a valid capacity: " ++ show cap]
    where
        err :: [String] -> Error
        err msg = unlines $ header:map ("  " ++) msg
        header = "Component " ++ (utxt $ getNameText comp) ++ " has invalid arguments:"

----------------
-- Unit Tests --
----------------

#ifdef TESTING

-- | List of tests to execute
unitTests :: [Test]
unitTests = portOrderTests ++ deriveColorTests

-- | Tests to check if 'makeComponentContexts' assigns ports in the right order (i.e. the order of input)
portOrderTests :: [Test]
portOrderTests = [testPortOrderA, testPortOrderB]
testPortOrderA :: Test
testPortOrderA = TestLabel "Port order A" $ TestCase $ assertEqual "port order incorrect" [0,1] (snd ((lookupM (src 792) (0::Int) cMap)::([Int],[Int]))) where
    cMap = makeComponentContexts (NSpec comps chans ports) where
        comps :: [ComponentOrMacro Channel]
        comps = [C (Fork "fork")]
        chans :: [Channel]
        chans = [Channel "a", Channel "b"]
        ports :: [(Text, Text)]
        ports = [("fork", "a"), ("fork", "b")]
testPortOrderB :: Test
testPortOrderB = TestLabel "Port order B" $ TestCase $ assertEqual "port order incorrect" [1,0] (snd ((lookupM (src 795) (0::Int) cMap)::([Int],[Int]))) where
    cMap = makeComponentContexts (NSpec comps chans ports) where
        comps :: [ComponentOrMacro Channel]
        comps = [C (Fork "fork")]
        chans :: [Channel]
        chans = [Channel "a", Channel "b"]
        ports :: [(Text, Text)]
        ports = [("fork", "b"), ("fork", "a")]

-- | Tests to check if channel colors are calculated correctly.
deriveColorTests :: [Test]
deriveColorTests =
       testDeriveSourceColor
    ++ testDerivePatientSourceColor
    ++ testDeriveFunctionColor
    ++ testDeriveQueueColor
    ++ testDeriveSwitchColor
    ++ testDeriveMergeColor
    ++ testDeriveForkColor
    ++ testDeriveControlJoinColor
    ++ testDeriveFControlJoinColor
    ++ testDeriveMatchColor
    ++ testDeriveMatchColor2
    -- todo(tssb) (2) Add testcase for MultiMatch.
    ++ testDeriveLoadBalancerColor
    -- todo(tssb) Add testcase for Joitch.

-- | Tests to check if channel colors are calculated correctly for the source component.
testDeriveSourceColor :: [Test]
testDeriveSourceColor = map makeTest [req, reqAndRsp, reqAndRspD, 
                                      dataA, complex, struct_ab_grby,
                                      struct_A_green] where
    makeTest :: ColorSet -> Test
    makeTest color = TestLabel ("Derive source color " ++ show color) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net color) (colored_net color)
    expected_net color = Madl.Network.mkNetwork (NSpec (comps color) (colored_chans [color]) ports)
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork (NSpec (comps args) chans ports)
    comps :: ColorSet -> [Component]
    comps color = [(Source "source" color), (Sink "sink")]
    chans :: [Channel]
    chans = [Channel "a"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans colors = zip chans colors
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "sink")]

-- | Tests to check if channel colors are calculated correctly for the patient source component.
testDerivePatientSourceColor :: [Test]
testDerivePatientSourceColor = map makeTest [req, reqAndRsp, reqAndRspD] where
    makeTest :: ColorSet -> Test
    makeTest color = TestLabel ("Derive patient source color " ++ show color) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net color) (colored_net color)
    expected_net color = Madl.Network.mkNetwork (NSpec (comps color) (colored_chans [color]) ports)
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork (NSpec (comps args) chans ports)
    comps :: ColorSet -> [Component]
    comps color = [(PatientSource "source" color), (Sink "sink")]
    chans :: [Channel]
    chans = [Channel "a"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans colors = zip chans colors
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "sink")]

-- | Tests to check if channel colors are calculated correctly for the function component.
testDeriveFunctionColor :: [Test]
testDeriveFunctionColor = map makeTest 
                                [(req, toRSP, rsp), 
                                 (reqAndRsp, switchReqRsp, reqAndRsp), 
                                 (reqAndRspD, reqToRsp, rspD),
                                 (struct_ab_grby, mkAGreen, struct_A_green),
                                 (struct_A_B, mkGreenBlue_RedYellow, struct_A_blue_B_yellow)] where
    makeTest :: (ColorSet, MFunctionDisj, ColorSet) -> Test
    makeTest args@(_icolor, fun, _ocolor) = TestLabel ("Derive function color " ++ show fun) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net args)
    expected_net args@(icolor, _fun, ocolor) = Madl.Network.mkNetwork $ NSpec (comps args) (colored_chans [icolor, ocolor]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork (NSpec (comps args) chans ports)
    comps :: (ColorSet, MFunctionDisj, ColorSet) -> [Component]
    comps (color, fun, rt) = [Source "source" color, Function "fun" fun rt, Sink "sink"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "fun"), ("fun", "b"), ("b", "sink")]

-- | Tests to check if channel colors are calculated correctly for the queue component.
testDeriveQueueColor :: [Test]
testDeriveQueueColor = map makeTest [req, reqAndRsp, reqAndRspD] where
    makeTest :: ColorSet -> Test
    makeTest color = TestLabel ("Derive queue color " ++ show color) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net color) (colored_net color)
    expected_net color = Madl.Network.mkNetwork $ NSpec (comps color) (colored_chans [color, color]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: ColorSet -> [Component]
    comps color = [Source "source" color, Queue "q" 2, Sink "sink"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "q"), ("q", "b"), ("b", "sink")]

-- | Tests to check if channel colors are calculated correctly for the switch component.
testDeriveSwitchColor :: [Test]
testDeriveSwitchColor = map makeTest [(req, [XTrue, XFalse], req, nul), (reqAndRsp, [XFalse, XTrue], nul, reqAndRsp), (reqAndRspD, [isReq, isRsp], reqD, rspD)] where
    makeTest :: (ColorSet, [MFunctionBool], ColorSet, ColorSet) -> Test
    makeTest args@(icolor, fun, _, _) = TestLabel ("Derive switch color " ++ show fun) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net (icolor, fun))
    expected_net (icolor, fun, ocolor, ocolor') = Madl.Network.mkNetwork $ NSpec (comps (icolor, fun)) (colored_chans [icolor, ocolor, ocolor']) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: (ColorSet, [MFunctionBool]) -> [Component]
    comps (color, fun) = [Source "source" color, Switch "switch" fun, Sink "sink1", Sink "sink2"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "switch"), ("switch", "b"), ("b", "sink1"), ("switch", "c"), ("c", "sink2")]

-- | Tests to check if channel colors are calculated correctly for the merge component.
testDeriveMergeColor :: [Test]
testDeriveMergeColor = map makeTest [(req, nul, req), (req, rsp, reqAndRsp), (reqAndRspD, aPacketD, reqAndRspAndAD)] where
    makeTest :: (ColorSet, ColorSet, ColorSet) -> Test
    makeTest args@(icolor, icolor', _) = TestLabel ("Derive merge color " ++ show icolor ++ " " ++ show icolor') $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net (icolor, icolor'))
    expected_net (icolor, icolor', ocolor) = Madl.Network.mkNetwork $ NSpec (comps (icolor, icolor')) (colored_chans [icolor, icolor', ocolor]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: (ColorSet, ColorSet) -> [Component]
    comps (color1, color2) = [Source "source1" color1, Source "source2" color2, Merge "merge", Sink "sink"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source1", "a"), ("a", "merge"), ("source2", "b"), ("b", "merge"), ("merge", "c"), ("c", "sink")]

-- | Tests to check if channel colors are calculated correctly for the fork component.
testDeriveForkColor :: [Test]
testDeriveForkColor = map makeTest [req, reqAndRsp, reqAndRspD] where
    makeTest :: ColorSet -> Test
    makeTest color = TestLabel ("Derive fork color " ++ show color) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net color) (colored_net color)
    expected_net color = Madl.Network.mkNetwork $ NSpec (comps color) (colored_chans [color, color, color]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: ColorSet -> [Component]
    comps color = [Source "source" color, Fork "fork", Sink "sink1", Sink "sink2"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "fork"), ("fork", "b"), ("b", "sink1"), ("fork", "c"), ("c", "sink2")]

-- | Tests to check if channel colors are calculated correctly for the controljoin component.
testDeriveControlJoinColor :: [Test]
testDeriveControlJoinColor = map makeTest [(req, nul, nul), (req, rsp, req), (nul, token, nul)] where
    makeTest :: (ColorSet, ColorSet, ColorSet) -> Test
    makeTest args@(icolor, icolor', _) = TestLabel ("Derive controljoin color " ++ show icolor ++ " " ++ show icolor') $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net (icolor, icolor'))
    expected_net (icolor, icolor', ocolor) = Madl.Network.mkNetwork $ NSpec (comps (icolor, icolor')) (colored_chans [icolor, icolor', ocolor]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: (ColorSet, ColorSet) -> [Component]
    comps (color1, color2) = [Source "source1" color1, Source "source2" color2, ControlJoin "cjoin", Sink "sink"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source1", "a"), ("a", "cjoin"), ("source2", "b"), ("b", "cjoin"), ("cjoin", "c"), ("c", "sink")]

-- | Tests to check if channel colors are calculated correctly for the fcontroljoin component.
testDeriveFControlJoinColor :: [Test]
testDeriveFControlJoinColor = map makeTest [(req, nul, nul), (req, rsp, rsp), (rsp, req, req), (req, reqAndRsp, reqAndRsp), (nul, token, nul)] where
    makeTest :: (ColorSet, ColorSet, ColorSet) -> Test
    makeTest args@(icolor, icolor', _) = TestLabel ("Derive fcontroljoin color") $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net (icolor, icolor'))
    expected_net (icolor, icolor', ocolor) = Madl.Network.mkNetwork $ NSpec (comps (icolor, icolor')) (colored_chans [icolor, icolor', ocolor]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: (ColorSet, ColorSet) -> [Component]
    comps (color1, color2) = [Source "source1" color1, Source "source2" color2, FControlJoin "fcjoin" (XMatch (XVar 0) (XVar 1)), Sink "sink"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source1", "a"), ("a", "fcjoin"), ("source2", "b"), ("b", "fcjoin"), ("fcjoin", "c"), ("c", "sink")]

-- | Tests to check if channel colors are calculated correctly for the match component.
testDeriveMatchColor :: [Test]
testDeriveMatchColor = map makeTest [(req, req, nul, req), (reqAndRsp, nul, nul, nul), (reqAndRspD, req, rspD, reqD)] where
    makeTest :: (ColorSet, ColorSet, ColorSet, ColorSet) -> Test
    makeTest args@(icolor, mcolor, _, _) = TestLabel ("Derive match color " ++ show icolor ++ " " ++ show mcolor) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net (mcolor, icolor))
    expected_net (icolor, mcolor, fcolor, tcolor) = Madl.Network.mkNetwork $ NSpec (comps (mcolor, icolor)) (colored_chans [mcolor, icolor, tcolor, fcolor]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: (ColorSet, ColorSet) -> [Component]
    comps (color1, color2) = [Source "source1" color1, Source "source2" color2, Match "match" (XMatch (XVar 0) (XVar 1)), Sink "sink1", Sink "sink2"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c", Channel "d"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source1", "a"), ("a", "match"), ("source2", "b"), ("b", "match"), ("match", "c"), ("c", "sink1"), ("match", "d"), ("d", "sink2")]

-- | Tests to check if channel colors are calculated correctly for the match component.
testDeriveMatchColor2 :: [Test]
testDeriveMatchColor2 = map makeTest [(type2, reqAndRsp, type2, type2)] where
    makeTest :: (ColorSet, ColorSet, ColorSet, ColorSet) -> Test
    makeTest args@(icolor, mcolor, _, _) = TestLabel ("Derive match color " ++ show icolor ++ " " ++ show mcolor) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net args) (colored_net (mcolor, icolor))
    expected_net (icolor, mcolor, fcolor, tcolor) = Madl.Network.mkNetwork $ NSpec (comps (mcolor, icolor)) (colored_chans [mcolor, icolor, tcolor, fcolor]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: (ColorSet, ColorSet) -> [Component]
    comps (color1, color2) = [Source "source1" color1, Source "source2" color2, Match "match" mf, Sink "sink1", Sink "sink2"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c", Channel "d"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source1", "a"), ("a", "match"), ("source2", "b"), ("b", "match"), ("match", "c"), ("c", "sink1"), ("match", "d"), ("d", "sink2")]

    mf :: MFunctionBool
    mf = XSelectB (XVar 1) $ Hash.fromList [("req", XTrue), ("rsp", XFalse)]
    type2 = makeColorSet [("", Right $ bitvecT 1)]

-- | Tests to check if channel colors are calculated correctly for the loadbalancer component.
testDeriveLoadBalancerColor :: [Test]
testDeriveLoadBalancerColor = map makeTest [req, reqAndRsp, reqAndRspD] where
    makeTest :: ColorSet -> Test
    makeTest color = TestLabel ("Derive load-balancer color " ++ show color) $
        TestCase $ assertEqual "Color derivation incorrect" (expected_net color) (colored_net color)
    expected_net color = Madl.Network.mkNetwork $ NSpec (comps color) (colored_chans [color, color, color]) ports
    colored_net = channelTypes . net
    net args = Madl.Network.mkNetwork $ NSpec (comps args) chans ports
    comps :: ColorSet -> [Component]
    comps color = [Source "source" color, LoadBalancer "loadBalancer", Sink "sink1", Sink "sink2"]
    chans :: [Channel]
    chans = [Channel "a", Channel "b", Channel "c"]
    colored_chans :: [ColorSet] -> [WithColors Channel]
    colored_chans types = zip chans types
    ports :: [(Text, Text)]
    ports = [("source", "a"), ("a", "loadBalancer"), ("loadBalancer", "b"), ("b", "sink1"), ("loadBalancer", "c"), ("c", "sink2")]

#endif
