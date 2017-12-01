{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

{-|
Module      : Madl.Cycles
Description : Provides a combinatorial cycle checker for madl networks.
Copyright   : (c) Sanne Wouda 2016

Provides a combinatorial cycle checker for madl networks.
-}
module Madl.Cycles (checkCycles) where

import Control.Arrow(first)
import Control.Monad(ap)

import Data.Function(on)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree(Gr)
import Data.Graph.Inductive.Dot(fglToDotGeneric,showDot)
import qualified Data.Map as M
import Data.List(nubBy,unfoldr,(\\))
import Data.Maybe(fromJust)

import Utils.Tuple(swap,mapFst)
import Utils.Text(Text,utxt,txt)
import Utils.Map(lookupM,lookupM')

import Madl.Network

-- import Debug.Trace

-- Error function
fileName :: Text
fileName = "Madl.Cycles"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++ utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

data WireType = Irdy | Trdy
    deriving (Show,Eq,Ord)

type Wire c = (ChannelID, XChannel c, WireType)

wire2key :: Wire c -> (ChannelID, WireType)
wire2key (xID, _x, w) = (xID, w)

-- Borrowing some code from Graphalyze (pulling in that package is a nightmare)
-- BSD licensed so don't worry

-- | A grouping of 'Node's.
type NGroup = [Node]

-- | A grouping of 'LNode's.
type LNGroup a = [LNode a]

-- | Return true if and only if the list contains a single element.
single     :: [a] -> Bool
single [_] = True
single  _  = False

-- | Makes the graph a simple one, by removing all duplicate edges and loops.
--   The edges removed if duplicates exist are arbitrary.
mkSimple :: (DynGraph gr) => gr a b -> gr a b
mkSimple = gmap simplify where
    rmLoops n = filter ((/=) n . snd)
    rmDups = nubBy ((==) `on` snd)
    simpleEdges n = rmDups . rmLoops n
    simplify (p,n,l,s) = (p',n,l,s') where
        p' = simpleEdges n p
        s' = simpleEdges n s

-- | Obtain the labels for a list of 'Node's.
--   It is assumed that each 'Node' is indeed present in the given graph.
addLabels    :: (Graph g) => g a b -> [Node] -> [LNode a]
addLabels gr = map (ap (,) (fromJust . lab gr))


-- | Find all cycles in the given graph.
cyclesIn   :: (DynGraph g) => g a b -> [LNGroup a]
cyclesIn g = map (addLabels g) (cyclesIn' g)

-- | Find all cycles in the given graph, returning just the nodes.
cyclesIn' :: (DynGraph g) => g a b -> [NGroup]
cyclesIn' = concat . unfoldr findCycles . mkSimple

-- | Find all cycles containing a chosen node.
findCycles :: (DynGraph g) => g a b -> Maybe ([NGroup], g a b)
findCycles g
    | isEmpty g = Nothing
    | otherwise = Just . getCycles . matchAny $ g where
    getCycles (ctx,g') = (cyclesFor (ctx, g'), g')

-- | Find all cycles for the given node.
cyclesFor :: (DynGraph g) => GDecomp g a b -> [NGroup]
cyclesFor = map init .
            filter isCycle .
            pathTree .
            first Just
    where
      isCycle p = not (single p) && (head p == last p)


-- | Find all possible paths from this given node, avoiding loops,
--   cycles, etc.
pathTree             :: (DynGraph g) => Decomp g a b -> [NGroup]
pathTree (Nothing,_) = []
pathTree (Just ct,g)
    | isEmpty g = []
    | null sucs = [[n]]
    | otherwise = (:) [n] . map (n:) . concatMap (subPathTree g') $ sucs
    where
      n = node' ct
      sucs = suc' ct
      -- Avoid infinite loops by not letting it continue any further
      ct' = makeLeaf ct
      g' = ct' & g
      subPathTree gr n' = pathTree $ match n' gr

-- | Remove all outgoing edges
makeLeaf           :: Context a b -> Context a b
makeLeaf (p,n,a,_) = (p', n, a, [])
    where
      -- Ensure there isn't an edge (n,n)
      p' = filter (\(_,n') -> n' /= n) p

-- | Return all combinatorial cycles from the given network.
checkCycles :: forall c. (Show c) => XFlattenedNetwork c -> [LNGroup (Wire c)]
checkCycles = cyclesIn
    . (if debugWireGraph then wireGraphFatal else id)
    . makeWireGraph where
    debugWireGraph = False
    wireGraphFatal = fatal 134 . txt . showDot . (\g -> fglToDotGeneric g showChannel (const "") id)
    showChannel (xID, _, w) = show (xID, w)

makeWireGraph :: forall c . (Show c) => XFlattenedNetwork c -> Gr (Wire c) ()
makeWireGraph net = mkGraph wireNodes es where
    wireNodes :: [(Node, (ChannelID, XChannel c, WireType))]
    wireNodes = zip (newNodes (length wires) (empty::Gr (Wire c) ())) wires
    wires = concatMap mkWires . getChannelsWithID $ net
    mkWires (xID, x) = [(xID, x, Irdy), (xID, x, Trdy)]
    xIDmap = M.fromList . map (mapFst wire2key . swap) $ wireNodes
    cs :: [(ComponentID, ([ChannelID], XComponent c, [ChannelID]))]
    cs = map (\cID -> (cID, getComponentContext net cID)) (getComponentIDs net)
    es :: [(Node, Node, ())]
    es = map (\(w0, w1) -> (lookupM' (src 137) xIDmap (wire2key w0), lookupM' (src 138) xIDmap (wire2key w1), ())) (dependsContext cs)
    dependsContext :: [(ComponentID, ([ChannelID], XComponent c, [ChannelID]))] -> [(Wire c, Wire c)]
    dependsContext ctx = concatMap dependsIrdy ctx ++ concatMap dependsTrdy ctx
    dependsIrdy :: (ComponentID, ([ChannelID], XComponent c, [ChannelID])) -> [(Wire c, Wire c)]
    dependsIrdy (cID, (_is, c, ts)) = concatMap g (zip [0..] ts) where
        g :: (Int, ChannelID) -> [(Wire c, Wire c)]
        g = (\(p, xID) -> map (f xID) (depends net c cID Irdy p))
        f :: ChannelID -> Wire c -> (Wire c, Wire c)
        f xID = (\w -> ((xID, getChannel net xID, Irdy), w))
    dependsTrdy :: (ComponentID, ([ChannelID], XComponent c, [ChannelID])) -> [(Wire c, Wire c)]
    dependsTrdy (cID, (is, c, _ts)) = concatMap g (zip [0..] is) where
        g :: (Int, ChannelID) -> [(Wire c, Wire c)]
        g = (\(p, xID) -> map (f xID) (depends net c cID Trdy p))
        f :: ChannelID -> Wire c -> (Wire c, Wire c)
        f xID = (\w -> ((xID, getChannel net xID, Trdy), w))

depends :: Show c => XFlattenedNetwork c -> XComponent c -> ComponentID -> WireType -> Int -> [Wire c]
depends _   (Queue{}) _ Irdy _ = []  -- o.irdy = size > 0
depends _   (Queue{}) _ Trdy _ = []  -- i.trdy = size < cap

depends _   (Source{}) _ Irdy _ = []
depends _   (Source{}) _ Trdy _ = fatal 172 "trdy of a Source does not exist"
depends _   (PatientSource{}) _ Irdy _ = []
depends _   (PatientSource{}) _ Trdy _ = fatal 174 "trdy of a PatientSource does not exist"
depends _   (Sink{}) _ _ _ = []
depends _   (DeadSink{}) _ _ _ = []

depends net (Function{}) cID Irdy _ = irdyInputs net cID   -- o.irdy = i.irdy
depends net (Function{}) cID Trdy _ = trdyOutputs net cID  -- i.trdy = o.trdy

depends net (Switch{}) cID Irdy _ = irdyInputs net cID
        -- o_k.irdy = i.irdy && f_k(i.data), for all 1 <= k <= n
depends net (c@Switch{}) cID Trdy _ = depends net c cID Irdy 0 ++ trdyOutputs net cID
        -- i.trdy = ∃k : o_k.irdy && o_k.trdy

depends net (Merge{}) cID Irdy _ = irdyInputs net cID
        -- o.irdy = OR { i_j.irdy && sel == j | 1≤j≤n }
depends net (Merge{}) cID Trdy p = inputIrdyWire net p cID : trdyOutputs net cID
        -- i_j.trdy = i_j.irdy && sel == j && o.trdy, for all 1≤j≤n

depends net (Fork{}) cID Irdy p = trdyOutputsExcept net cID [p] ++ irdyInputs net cID
        -- o_j.irdy = AND {o_j'.trdy | 1≤j'≤n, j'≠j } && i.irdy, for all 1≤j≤ n
depends net (Fork{}) cID Trdy _ = trdyOutputs net cID
        -- i.trdy = AND { o_j.trdy | 1≤j≤ n }

depends net (ControlJoin{}) cID Trdy p = irdyInputsExcept net cID [p] ++ trdyOutputs net cID
        -- i_j.trdy = AND { i_j'.irdy | 1≤j'≤n, j'≠j } && o.trdy, for all 1≤j≤n
depends net (ControlJoin{}) cID Irdy _ = irdyInputs net cID
        -- o.irdy = AND { i_j.irdy | 1≤j≤n }, for all 1≤j≤n
depends net (FControlJoin{}) cID Trdy p = irdyInputsExcept net cID [p] ++ trdyOutputs net cID
        -- i_1.trdy = i_2.irdy && o.trdy
        -- i_2.trdy = i_1.irdy && o.trdy
depends net (FControlJoin{}) cID Irdy _ = irdyInputs net cID
        -- o.irdy = i_1.irdy && i_2.irdy

-- o_1.irdy = i_1.irdy && i_2.irdy &&  f(i_2.data, i_1.data)
-- o_2.irdy = i_1.irdy && i_2.irdy && ¬f(i_2.data, i_1.data)
depends net (Match{}) cID Irdy _ = irdyInputs net cID
depends net (Match{}) cID Trdy p = if p == 0
    -- i_1.trdy = i_2.irdy && f(i_2.data, i_1.data) && o_1.trdy
    then [inputIrdyWire net 1 cID, outputTrdyWire net 0 cID]
    -- i_2.trdy = i_1.irdy &&
    -- ( (f(i_2.data, i_1.data) && o_1.trdy) || (¬f(i_2.data, i_1.data) && o_2.trdy) )
    else inputIrdyWire net 0 cID : trdyOutputs net cID

depends net (MultiMatch{}) cID Irdy p = inputIrdyWire net p cID : map (irdyOf net cID) (mmAllData net cID)
        -- o_j.irdy = mSel == j && mI_j.irdy && ∃k: dSel == k && dI_k.irdy && f(dI_k.data, mI_j.data), for all 1 <= j <= n
depends net (c@MultiMatch{}) cID Trdy p
    | mmIsMatch net cID p = outputTrdyWire net p cID : depends net c cID Irdy p
        -- mI_j.trdy = o_j.trf, for all 1 <= j <= n
    | otherwise           =  inputIrdyWire net p cID : map (irdyOf net cID) (mmAllData net cID) ++ trdyOutputs net cID
        -- dI_k.trdy = dSel == k && ∃j: o_j.trf, for all 1 <= k <= m

depends net (LoadBalancer{}) cID Trdy _ = trdyOutputs net cID
depends net (LoadBalancer{}) cID Irdy p = outputTrdyWire net p cID : irdyInputs net cID

depends _   (Automaton{}) _ _ _ = fatal 204 "Automaton unimplemented"
depends _   (Joitch{}) _ _ _ = fatal 205 "Joitch unimplemented"
depends net (Vars{}) cID Irdy _ = irdyInputs net cID
depends net (Vars{}) cID Trdy _ = trdyOutputs net cID

depends _ (Cut{}) _ Irdy _ = [] -- Cut cycles
depends _ (Cut{}) _ Trdy _ = []

depends net (GuardQueue{}) cID Irdy _ = [inputIrdyWire net 1 cID]
        -- o.irdy = (!Empty(gq) && sel == 0) || (Empty(gq) && sel == 1 && i_g.irdy)
depends net (GuardQueue{}) cID Trdy _ = trdyOutputs net cID
        -- i_b.trdy = !Full(gq) && sel == 0; i_g.trdy = o.trdy && Empty(gq) && sel == 1

mmIsData, mmIsMatch :: XFlattenedNetwork c -> ComponentID -> Int -> Bool
mmIsData net cID p = p >= length (getOutChannels net cID)
mmIsMatch net cID = not . mmIsData net cID

mmAllData :: XFlattenedNetwork c -> ComponentID -> [Int]
mmAllData net cID = [length (getOutChannels net cID)..length (getInChannels net cID) - 1]

trdyOutputs, irdyInputs :: XFlattenedNetwork c -> ComponentID -> [Wire c]
trdyOutputs net cID = map (trdyOf net cID) (outputPorts net cID)
irdyInputs net cID = map (irdyOf net cID) (inputPorts net cID)

inputPorts, outputPorts :: XFlattenedNetwork c -> ComponentID -> [Int]
inputPorts net cID =  [0..(length (getInChannels net cID) - 1)]
outputPorts net cID =  [0..(length (getOutChannels net cID) - 1)]

irdyInputsExcept, trdyOutputsExcept :: XFlattenedNetwork c -> ComponentID -> [Int] -> [Wire c]
irdyInputsExcept net cID ps = map (irdyOf net cID) (inputPorts net cID \\ ps)
trdyOutputsExcept net cID ps = map (trdyOf net cID) (outputPorts net cID \\ ps)

irdyOf, trdyOf :: XFlattenedNetwork c -> ComponentID -> Int -> Wire c
irdyOf net = flip (inputIrdyWire net)
trdyOf net = flip (outputTrdyWire net)

outputTrdyWire, inputIrdyWire :: XFlattenedNetwork c -> Int -> ComponentID -> Wire c
outputTrdyWire net p cID = (xID, getChannel net xID, Trdy) where
    xID :: ChannelID
    xID = lookupM (src 81) p (getOutChannels net cID)

inputIrdyWire net p cID = (xID, getChannel net xID, Irdy) where
    xID :: ChannelID
    xID = lookupM (src 88) p (getInChannels net cID)
