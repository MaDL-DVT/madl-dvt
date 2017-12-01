{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

{-|
Module      : Madl2Verilog.Assertions
Description : Generation of system verilog assertions.
Copyright   : (c) Tessa Belder 2015-2016

This module provides a basic data structure for madl networks.
-}
module Madl2Verilog.Assertions (AssertionOptions(..), SVAssertionMode(..), hasAssertions, assertions) where

-- import Debug.Trace

import qualified Data.HashMap as Hash
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T

import Utils.Map
import Utils.Text

import Madl.Deadlock.DeadlockDetection
import Madl.Deadlock.Formulas
import Madl.Deadlock.Runner
import Madl.Invariants
import Madl.MsgTypes
import Madl.Network

import Madl2Verilog.VerilogConstants
import Madl2Verilog.VerilogGen

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Assertions"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | Options determining which assertions are generated
data AssertionOptions = AssertionOptions {
    invariantAssertions :: SVAssertionMode, -- ^ Assertion of the invariants as calculated in 'Madl.Invariants'
    notFullAssertions :: SVAssertionMode, -- ^ Assertion of queues that cannot be full, as calculated by SMT
    deadlockAssertions :: SVAssertionMode, -- ^ Assertion of the deadlock equations, as calculated in 'Madl.Deadlock.DeadlockDetection'
    naiveAssertions :: SVAssertionMode, -- ^ Assertion of the property @G(irdy -> F trdy)@, for all sources
    liveSourceAssertions :: SVAssertionMode, -- ^ Assertion of live source (unsupported)
    persistentChannelAssertions :: SVAssertionMode -- ^ Assertions of channel persistency @G(irdy /\ !trdy -> X irdy)@ (unsupported)
}

-- | Returns whether any of the assertion options is turned on
hasAssertions :: AssertionOptions -> Bool
hasAssertions (AssertionOptions a b c d e f) = any (/= None) [a, b, c, d, e, f]

-- | Contains the set of colors that should be counted for each queue
type QDataSets = Hash.Map ComponentID (Set (Maybe Color))
-- | Contains the list of colors that should be counted for each queue
type QDataMap = Hash.Map ComponentID [Color]

-- | Produces system verilog assertions. The returned integer is the maximum nr of colors that should be counted for a queue,
-- or @Nothing@ if colors don't have to be counted for any queue.
assertions :: Bool -> FlatColoredNetwork -> AssertionOptions -> Text -> IO (Text, Maybe Int)
assertions useInterface madl opts topLevelName = do

    -- get the network invariants
    let madlInvariants = getInvariants madl
    -- check if the componentIDs of queues that can never be full should be calculated
    let needsNotFullIds = any (/= None) [deadlockAssertions opts, notFullAssertions opts]
    -- calculated componentIDs of queues that can never be full, if necessary
    notFullIds <- if needsNotFullIds then notFullQueues (unflatten madl) Z3 madlInvariants else return []
    let blockvars = BlockVars Seq.empty notFullIds
    let deadlockInfo@(deadlockLiterals, _) = getDeadlockLiterals madl blockvars

    -- Map containing the colors that should be counted for eqch queue
    let qMap = fmap (catMaybes . Set.toList) $ Hash.unionsWith Set.union [
            if invariantAssertions opts == None then Hash.empty else foldr invarQNames Hash.empty madlInvariants,
            if deadlockAssertions opts == None then Hash.empty else foldr deadlockQNames Hash.empty $ Map.elems deadlockLiterals
            ]

    let invarAsserts = concatMap (uncurry $ invariantToAssertion (invariantAssertions opts) madl qMap) $ zip [0..] madlInvariants
    let nfqAsserts = concatMap (queueToAssertion (notFullAssertions opts) madl) notFullIds
    let deadlockAsserts = getDeadlockAssertions (deadlockAssertions opts) madl qMap deadlockInfo
    let naiveAsserts = concatMap (naiveDeadlockProperty (naiveAssertions opts) useInterface) $ getComponents madl
    let liveAsserts = [] -- todo
    let persistencyAsserts = [] --todo

    let topModule = VModule {
            vmoduleName = svAssertionModule topLevelName,
            vmoduleParams = [],
            vmoduleHasTime = False,
            vmoduleHasRst = True,
            vmoduleInterface = [VInterfacePort (Just MInput) (Left Nothing) vAssertUnbound | deadlockAssertions opts /= None],
            vmoduleBody =
                   commentHeader "Data count instantiations" (concatMap (uncurry $ assignQData madl) $ Hash.assocs qMap)
                ++ commentHeader "Invariant assertions" invarAsserts
                ++ commentHeader "Not full queue assertions" nfqAsserts
                ++ commentHeader "Deadlock equation assertions" deadlockAsserts
                ++ commentHeader "Naive deadlock property assertions" naiveAsserts
                ++ commentHeader "Live source assertions" liveAsserts
                ++ commentHeader "Persistent channel assertions" persistencyAsserts
        }

    let sva = T.unlines (
               commentHeader "Assertion macros" vAssertionDefinitions
            ++ commentHeader "Assertion module" (declareModule useInterface topModule)
            )

    -- calculate the maximum nr of colors that must be counted for a queue
    let numDataSize = if Hash.null qMap then Nothing else Just . maximum . map length $ Hash.elems qMap

    return (sva, numDataSize)

--------------------------
-- Invariant Assertions --
--------------------------

-- | Get the colors that should be counted for each queue in order to assert to invariants
invarQNames :: Invariant Int -> QDataSets -> QDataSets
invarQNames inv qmap = case inv of 
    Invariant qMap _ _ -> foldr (uncurry x) qmap (Map.assocs qMap) 
    LeqInvariant qMap _ _ -> foldr (uncurry x) qmap (Map.assocs qMap) 
    where
        x :: ComponentID -> Map (Maybe Color) Int -> QDataSets -> QDataSets
        x cID m = Hash.insertWith (Set.union) cID $ Map.keysSet m

-- | Transform a madl invariant to a system verilog assertion.
invariantToAssertion :: SVAssertionMode -> FlatColoredNetwork -> QDataMap -> Int -> Invariant Int -> VerilogCode
invariantToAssertion mode network dataMap invariantNr inv = createAssertion assertion where
    assertion = SVAssertion{
        svassertionName = svAssertionInvariantName invariantNr,
        svassertionType = svPos mode,
        svassertionBody = svassertionBody',
        svassertionMode = mode
    }
    qMap = case inv of
        Invariant qmap _ _ -> qmap
        LeqInvariant qmap _ _ -> qmap
    svassertionBody' = "0 == " +++ T.intercalate " + " (map f $ Map.assocs qMap) --todo(tssb) (0) sva for automaton invariant
    f (k, m) = T.intercalate " + " (map (f' k) $ Map.assocs m)
    f' cID (color, i) = "(" +++ showT i +++ ") * " +++ esc (getWireName network dataMap cID color)

-------------------------------
-- Not Full Queue Assertions --
-------------------------------

-- | Produce an assertion for a queue that can never be full.
queueToAssertion :: SVAssertionMode -> FlatColoredNetwork -> ComponentID -> VerilogCode
queueToAssertion mode network cID = createAssertion assertion where
    assertion = SVAssertion {
        svassertionName = svAssertionNotFullName cID,
        svassertionType = svPos mode,
        svassertionBody = svassertionBody',
        svassertionMode = mode
    }
    Queue nameList _ = getComponent network cID
    svassertionBody' =  vlog_not . vFull . T.intercalate "." $ map esc nameList

----------------------------------
-- Deadlock equation assertions --
----------------------------------

-- | Get the colors that should be counted for each queue in order to assert the deadlock equations.
deadlockQNames :: Formula -> QDataSets -> QDataSets
deadlockQNames formula qdata = case formula of
    AND fs -> foldr deadlockQNames qdata $ Set.toList fs
    OR fs -> foldr deadlockQNames qdata $ Set.toList fs
    NOT f -> deadlockQNames f qdata
    T -> qdata
    F -> qdata
    Lit l -> deadlockQNames' l qdata
    where
        deadlockQNames' literal qdata' = case literal of
            ContainsNone cID (Just cs) -> Hash.insertWith Set.union cID (Set.fromList . map Just $ getColors cs) qdata'
            _ -> qdata'

-- | Get all deadlock literals produced from the formula stating the no source is ever blocked.
getDeadlockLiterals :: FlatColoredNetwork -> BlockVariables -> (Map Literal Formula, Formula)
getDeadlockLiterals network vars = (deadlockLiterals, deadlockFormula) where
    deadlockLiterals = unfold_formula network vars deadlockFormula
    deadlockFormula = NOT . OR . Set.fromList $ map (Lit . BlockSource) sourceIDs
    sourceIDs = map fst . filter (\(_, c) -> case c of Source _ msg -> not $ emptyColorSet msg; _ -> False) $ getComponentsWithID network

-- | Get the assertions for the deadlock equations belonging to the deadlock literals.
getDeadlockAssertions :: SVAssertionMode -> FlatColoredNetwork -> QDataMap -> (Map Literal Formula, Formula) -> VerilogCode
getDeadlockAssertions None _ _ _ = []
getDeadlockAssertions mode network dataMap (deadlockLiterals, deadlockFormula) = literals ++ [""] ++ createAssertion assertion where
    literals = literalWires ++ literalAssignments
    assertion = SVAssertion {
        svassertionName = svAssertionDeadLockName,
        svassertionType = svPos mode,
        svassertionBody = esc vAssertUnbound +++ " |=> " +++ formulaToVerilog network dataMap deadlockFormula,
        svassertionMode = mode
    }
    literalWires = concatMap (declareRegister (src 233) (0, 1) . literalToVerilog network dataMap) $ Map.keys deadlockLiterals
    literalAssignments =
        ["always @(posedge " +++ vinterfaceName vClk +++ ") begin"]
        ++ indent (
               ["if (" +++ esc vAssertUnbound +++ ") begin"]
            ++ indent (concatMap (uncurry $ declareLiteralInVerilog network dataMap) $ Map.assocs deadlockLiterals)
            ++ ["end"])
        ++ ["end"]

-- | Declare a register to contain the value of a deadlock literal
declareLiteralInVerilog :: FlatColoredNetwork -> QDataMap -> Literal -> Formula -> VerilogCode
declareLiteralInVerilog network dataMap literal formula = (vlog_comment $ showT formula) :
    assignRegister (literalToVerilog network dataMap literal) (formulaToVerilog network dataMap formula)

-- | Translate a formula to verilog
formulaToVerilog :: FlatColoredNetwork -> QDataMap -> Formula -> Text
formulaToVerilog network dataMap formula = case formula of
    AND fs -> vlog_and . map (formulaToVerilog network dataMap) $ Set.toList fs
    OR fs -> vlog_or . map (formulaToVerilog network dataMap) $ Set.toList fs
    NOT f -> vlog_not $ formulaToVerilog network dataMap f
    T -> vlog_true
    F -> vlog_false
    Lit l -> literalToVerilog network dataMap l

-- | Translate a literal to verilog
literalToVerilog :: FlatColoredNetwork -> QDataMap -> Literal -> Text
literalToVerilog network dataMap literal = case literal of
    Is_Full cID -> vFull . T.intercalate "." . map esc . getName $ getComponent network cID
    Is_Not_Full cID -> vlog_not . literalToVerilog network dataMap $ Is_Full cID
    ContainsNone cID Nothing -> vEmpty . T.intercalate "." . map esc . getName $ getComponent network cID --isEmpty
    ContainsNone cID (Just cs) -> vlog_and . map vContainsNone $ getColors cs where
        vContainsNone c = vlog_equals (getWireName network dataMap cID $ Just c) "0"
    Any_At_Head cID Nothing -> vlog_not . literalToVerilog network dataMap $ ContainsNone cID Nothing --notIsEmpty
    Any_At_Head cID (Just cs) -> vlog_or . map (vHead . dataEncoding te) $ getColors cs where
        name = T.intercalate "." . map esc . getName $ getComponent network cID
        vHead enc = vlog_and [vlog_not $ vEmpty name, vDataMatches (vDataAtHead name) enc]
        te = typeEncoding $ head $ inputTypes network cID
    All_Not_At_Head cID Nothing -> literalToVerilog network dataMap $ ContainsNone cID Nothing --isEmpty
    All_Not_At_Head cID cs -> vlog_not . literalToVerilog network dataMap $ Any_At_Head cID cs
    Select cID i -> vlog_equals (vSelect . T.intercalate "." . map esc . getName $ getComponent network cID) (showT i)
    MSelect cID (i, j) -> vlog_equals (vSelect . T.intercalate "." . map esc . getName $ getComponent network cID) (showT v) where
        v = i * dIns + j
        dIns = getNrInputs network cID  - getNrOutputs network cID
    InState _cID _s -> fatal 233 "unimplemented" --todo(tssb) (0) InState in verilog
    TSelect _cID _i _t -> fatal 234 "unimplemented" --todo(tssb) (0) TSelect in verilog
    Sum_Compare{} -> fatal 235 "Illegal literal: Sum_Compare"
    BlockSource cID -> vlog_src_block network cID
    BlockAny _ xID cs -> vlog_block network xID cs
    IdleAll _ xID cs -> vlog_idle network xID cs

-- | Names to use for the block and idle literals in verilog
vlog_block, vlog_idle :: FlatColoredNetwork -> ChannelID -> Maybe ColorSet -> Text
vlog_block net xID Nothing = esc $ "block" >. (vlog_channel_name net xID)
vlog_block net xID (Just cs) = esc . ("block" >.) . ((vlog_channel_name net xID) >.) . txt $ showColorSetNoSpaces cs
vlog_idle net xID Nothing = esc $ "idle" >. (vlog_channel_name net xID)
vlog_idle net xID (Just cs) = esc . ("idle" >.) . ((vlog_channel_name net xID) >.) . txt $ showColorSetNoSpaces cs

vlog_channel_name :: FlatColoredNetwork -> ChannelID -> Text
vlog_channel_name net = T.intercalate "$" . channelName . fst . getChannel net

vlog_src_block :: FlatColoredNetwork -> ComponentID -> Text
vlog_src_block net cID = esc $ "block_src" >. (T.intercalate "$" . getName $ getComponent net cID)

----------------------------------------
-- Naive deadlock property assertions --
----------------------------------------

-- | Produce the naive deadlock property for a single component
naiveDeadlockProperty :: SVAssertionMode -> Bool -> FlatComponent -> VerilogCode
naiveDeadlockProperty mode useInterface component = case component of
    Source nameList _ -> createAssertion assertion where
        assertion = SVAssertion {
                svassertionName = svAssertionBlockName $ T.intercalate "$" nameList,
                svassertionType = svPos mode,
                svassertionBody = nameIrdy +++ " |-> ##[0:$] " +++ nameTrdy,
                svassertionMode = mode
            }
        nameIrdy = T.intercalate "." $ map esc (nameList ++ [vIrdy useInterface port])
        nameTrdy = T.intercalate "." $ map esc (nameList ++ [vTrdy useInterface port])
        [port] = outputPorts (component, 1)
    _ -> []

--------------------------
-- Nr of Packets        --
--------------------------

-- | Assign the types of data that must be counted to the given queue
assignQData :: FlatColoredNetwork -> ComponentID -> [Color] -> VerilogCode
assignQData network cID = concatMap (uncurry assignQData') . zip [0..] where
    assignQData' :: Int -> Color -> VerilogCode
    assignQData' i c = assignWire (name +++".data[" +++showT i +++"]") (dataEncoding te c) where
        name = T.intercalate "." $ map esc nameList
        Queue nameList _ = getComponent network cID
        te = typeEncoding intype
        intype = head $ inputTypes network cID

-- | Get the name of the wire that contains information about the number of packets in the given queue of the given color.
getWireName :: FlatColoredNetwork -> QDataMap -> ComponentID -> Maybe Color -> Text
getWireName network dataMap cID color = name +++ case color of
    Nothing -> ".nr_of_packets"
    Just t -> ".nr_of_packets_data[" +++showT dataIndex +++"]" where
        dataIndex = fromMaybe (fatal 245 "Invalid data map") . elemIndex t $ lookupM (src 245) cID dataMap
    where
        name = T.intercalate "." $ map esc nameList
        Queue nameList _ = getComponent network cID

-- | Encode a 'Color' in binary, according to the given 'TypeEncoding'
dataEncoding :: TypeEncoding -> Color -> Text
dataEncoding (TE dmap) color = showT (disjRangeSize dmap) +++ "'b" +++ dataEncodingDisj dmap color
-- | Encode a 'Color' in binary, according to the given 'DisjMap'
dataEncodingDisj :: DisjMap -> Color -> Text
dataEncodingDisj dmap c = case Hash.lookup (colorKey c) dmap of
    Nothing -> fatal 83 "Invalid color"
    Just (v, r, cmap, r') -> toBinary (rSize r) v +++ either (dataEncodingConj cmap) (dataEncodingBV $ rSize r') (colorContent c)
                                +++ T.replicate (contentRangeSize dmap - rSize r') "x"
-- | Encode a 'VStruct' in binary, according to the given 'ConjMap'
dataEncodingConj :: ConjMap -> VStruct -> Text
dataEncodingConj cmap vstruct = concatMapT f (Hash.assocs cmap) where
    f (key, (r, TE dmap)) = case lookup' key vstruct of
        Nothing -> T.replicate (rSize r) "x"
        Just disjOrBV -> either (dataEncodingDisj dmap) (dataEncodingBV $ rSize r) disjOrBV
-- | Encode a 'Value' in binary, according to the given size
dataEncodingBV :: Int -> Value -> Text
dataEncodingBV size val = toBinary size $ valValue val

-- | Convert a decimal value to a binary value of the given length
toBinary :: Int -> Int -> Text
toBinary x 0 = T.replicate x "0"
toBinary x n = T.replicate (x - length result) "0" +++ (T.concat $ map showT result) where
    result = reverse (helper n)
    helper 0 = []
    helper m = let (q,r) = m `divMod` 2 in r : helper q

---------------------
-- Queue Functions --
---------------------

-- | Check if queue is full
vFull :: Text -> Text
vFull = (+++ ".full")

-- | Check if queue is empty
vEmpty :: Text -> Text
vEmpty q = "(("+++q+++".in=="+++q+++".out) && !"+++q+++".full)"

-- | Get the data at the head of the queue
vDataAtHead :: Text -> Text
vDataAtHead q = q+++".data$addr ["+++q+++".out]"

-- | Check if inputdata matches the given encoding
vDataMatches :: Text -> Text -> Text
vDataMatches inputdata enc = "((" +++ inputdata +++ " & " +++ bitmask enc +++ ") === " +++ expected enc +++")"

-- | Get the bitmask of the given encoding. I.e. positions we care about are converted to a 1, and positions we don't care about are converted to a 0.
bitmask :: Text -> Text
bitmask = T.map (\c -> if c == '0' then '1' else if c == 'x' then '0' else c)
-- | Get the expected value of color matching the given encoding. I.e. all positions we don't care about should contain a 0,
-- and all position we do care about should contain the value of the given encoding.
expected :: Text -> Text
expected = T.map (\c -> if c == 'x' then '0' else c)