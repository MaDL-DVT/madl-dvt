{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Madl2Verilog.Library
Description : Library of verilog components.
Copyright   : (c) Tessa Belder 2016

Produces a library of verilog components.
-}
module Madl2Verilog.Library (madlLibrary) where

-- import Debug.Trace

import qualified Data.Set as Set
import qualified Data.Text as T

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes
import Madl.Network
import Madl2Verilog.VerilogConstants
import Madl2Verilog.VerilogGen

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Library"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

--------------------------------------------
-- Library data type
--------------------------------------------

data Library = Library {
    controlJoinModules :: Set Int,
    deadSinkModule :: Bool,
    fControlJoinModule :: Bool,
    forkModules :: Set Int,
    joitchModules :: Set Int,
    loadBalancerModules :: Set Int,
    matchModule :: Bool,
    mergeModules :: Set Int,
    multiMatchModules :: Set (Int, Int),
    queueModule :: Bool,
    sinkModule :: Bool,
    sourceModule :: Bool,
    switchModules :: Set Int,
    varsModule :: Bool
}

emptyLibrary :: Library
emptyLibrary = Library {
    controlJoinModules = Set.empty,
    deadSinkModule = False,
    fControlJoinModule = False,
    forkModules = Set.empty,
    joitchModules = Set.empty,
    loadBalancerModules = Set.empty,
    matchModule = False,
    mergeModules = Set.empty,
    multiMatchModules = Set.empty,
    queueModule = False,
    sinkModule = False,
    sourceModule = False,
    switchModules = Set.empty,
    varsModule = False
}

--------------------------------------------
-- Library generation
--------------------------------------------

-- | Generates a verilog library for the given network
madlLibrary :: Bool -> Bool -> MadlNetwork -> Text
madlLibrary useInterface hasInvariantAssertions network = T.unlines $
       madlInterface
    ++ arbiters
    ++ componentModules
    where
        madlInterface = if useInterface then chanInterface else []
        arbiters = concatMap (arbiterModuleCode useInterface) [2..maximum (Set.toList arbiterSet)]
        arbiterSet = Set.unions [mergeModules library, loadBalancerModules library, Set.map (\(i, o) -> o * (i - o)) $ multiMatchModules library, Set.singleton 1]
        componentModules =
               (concatMap (controlJoinModuleCode useInterface) (Set.toList $ controlJoinModules library))
            ++ (if deadSinkModule library then deadSinkModuleCode useInterface else [])
            ++ (if fControlJoinModule library then fControlJoinModuleCode useInterface else [])
            ++ (concatMap (forkModuleCode useInterface) (Set.toList $ forkModules library))
            ++ (concatMap (joitchModuleCode useInterface) (Set.toList $ joitchModules library))
            ++ (concatMap (loadBalancerModuleCode useInterface) (Set.toList $ loadBalancerModules library))
            ++ (if matchModule library then matchModuleCode useInterface else [])
            ++ (concatMap (mergeModuleCode useInterface) (Set.toList $ mergeModules library))
            ++ (concatMap (multiMatchModuleCode useInterface) (Set.toList $ multiMatchModules library))
            ++ (if queueModule library then queueModuleCode useInterface hasInvariantAssertions else [])
            ++ (if sinkModule library then sinkModuleCode useInterface else [])
            ++ (if sourceModule library then sourceModuleCode useInterface else [])
            ++ (concatMap (switchModuleCode useInterface) (Set.toList $ switchModules library))
            ++ (if varsModule library then varsModuleCode useInterface else [])

        library = foldr (addToLibrary network) emptyLibrary $ getComponentIDs network

-- | Add a single component to a library
addToLibrary :: IMadlNetwork n => TMadlNetwork n -> ComponentID -> Library -> Library
addToLibrary net cID lib = case (getNrInputs net cID, getComponent net cID, getNrOutputs net cID) of
    (_nrIns, C Automaton{},             _nrOuts) -> lib
    ( nrIns, C ControlJoin{},           _nrOuts) -> lib{controlJoinModules = Set.insert nrIns $ controlJoinModules lib}
    (_nrIns, C DeadSink{},              _nrOuts) -> lib{deadSinkModule = True}
    (_nrIns, C FControlJoin{},          _nrOuts) -> lib{fControlJoinModule = True}
    (_nrIns, C Madl.Network.Function{}, _nrOuts) -> lib
    (_nrIns, C Fork{},                   nrOuts) -> lib{forkModules = Set.insert nrOuts $ forkModules lib}
    (_nrIns, C GuardQueue{},            _nrOuts) -> lib
    (_nrIns, C Joitch{},                 nrOuts) -> lib{joitchModules = Set.insert nrOuts $ joitchModules lib}
    (_nrIns, C LoadBalancer{},           nrOuts) -> lib{loadBalancerModules = Set.insert nrOuts $ loadBalancerModules lib}
    (_nrIns, C Match{},                 _nrOuts) -> lib{matchModule = True}
    ( nrIns, C Merge{},                 _nrOuts) -> lib{mergeModules = Set.insert nrIns $ mergeModules lib}
    ( nrIns, C MultiMatch{},             nrOuts) -> lib{multiMatchModules = Set.insert (nrIns, nrOuts) $ multiMatchModules lib}
    (_nrIns, C PatientSource{},         _nrOuts) -> lib{sourceModule = True}
    (_nrIns, C Queue{},                 _nrOuts) -> lib{queueModule = True}
    (_nrIns, C Sink{},                  _nrOuts) -> lib{sinkModule = True}
    (_nrIns, C Source{},                _nrOuts) -> lib{sourceModule = True}
    (_nrIns, C Switch{},                 nrOuts) -> lib{switchModules = Set.insert nrOuts $ switchModules lib}
    (_nrIns, C Vars{},                  _nrOuts) -> lib{varsModule = True}
    (_nrIns, C Cut{},                   _nrOuts) -> lib{varsModule = True}
    (_, M (MacroInstance _ (Macro _ _ mnet)), _) -> foldr (addToLibrary mnet) lib $ getComponentIDs mnet

--------------------------------------------
-- Generation of individual modules
--------------------------------------------

-- | Generate a verilog module for a controljoin
controlJoinModuleCode :: Bool -> Int -> [Text]
controlJoinModuleCode useInterface nrIns = componentModuleCode useInterface compContext body where
    body = concatMap (\(i, p) -> assignWire (esc $ vTrdy useInterface p) (trdy i)) (zip [0..] inPorts)
        ++ assignWire (esc $ vIrdy useInterface o) irdy
        ++ assignWire (esc $ vData useInterface o) xdata

    trdy :: Int -> Text
    trdy i = vlog_and $ (esc $ vTrdy useInterface o) : (map (esc . vIrdy useInterface . snd) . filter ((/= i) . fst) $ zip [0..] inPorts)
    irdy :: Text
    irdy = vlog_and $ map (esc . vIrdy useInterface) inPorts
    xdata :: Text
    xdata = esc . vData useInterface $ head inPorts

    inPorts = inputPorts (nrIns, comp)
    [o] = outputPorts (comp, nrOuts)
    compContext@(_, comp, nrOuts) = (nrIns, ControlJoin "", 1)

-- | Generate a verilog module for a dead sink
deadSinkModuleCode :: Bool -> [Text]
deadSinkModuleCode useInterface = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface i) (vlog_false)
    [i] = inputPorts (nrIns, comp)
    compContext@(nrIns, comp, _) = (1, DeadSink "", 0)

-- | Generate a verilog module for an fcontroljoin
fControlJoinModuleCode :: Bool -> [Text]
fControlJoinModuleCode useInterface = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface inPort0) trdy0
        ++ assignWire (esc $ vTrdy useInterface inPort1) trdy1
        ++ assignWire (esc $ vIrdy useInterface o) irdy
        ++ assignWire (esc $ vData useInterface o) xdata

    trdy0, trdy1, irdy, xdata :: Text
    trdy0 = vlog_and [esc $ vTrdy useInterface o, esc $ vIrdy useInterface inPort1]
    trdy1 = vlog_and [esc $ vTrdy useInterface o, esc $ vIrdy useInterface inPort0]
    irdy = vlog_and [esc $ vIrdy useInterface inPort0, esc $ vIrdy useInterface inPort1]
    xdata = esc $ vData useInterface fPort

    [fPort] = map fst3 $ functionInputPorts compContext
    inPort0:inPort1:[] = inputPorts (nrIns, comp)
    [o] = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, nrOuts) = (2, FControlJoin "" XTrue, 1)

-- | Generate a verilog module for a fork
forkModuleCode :: Bool -> Int -> [Text]
forkModuleCode useInterface nrOuts = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface i) trdy
        ++ concatMap (\(i', p) -> assignWire (esc $ vIrdy useInterface p) (irdy i')) (zip [0..] outPorts)
        ++ concatMap (\p -> assignWire (esc $ vData useInterface p) xdata) outPorts

    trdy :: Text
    trdy = vlog_and $ map (esc . vTrdy useInterface) outPorts
    irdy :: Int -> Text
    irdy i' = vlog_and $ (esc $ vIrdy useInterface i) : (map (esc . vTrdy useInterface . snd) . filter ((/= i') . fst) $ zip [0..] outPorts)
    xdata :: Text
    xdata = esc $ vData useInterface i

    [i] = inputPorts (nrIns, comp)
    outPorts = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, _) = (1, Fork "", nrOuts)

-- | Generate a verilog module for a joitch
joitchModuleCode :: Bool -> Int -> [Text]
joitchModuleCode useInterface nrOuts = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface inPort0) trdy0
        ++ assignWire (esc $ vTrdy useInterface inPort1) trdy1
        ++ concatMap (\(i, p) -> assignWire (esc $ vIrdy useInterface p) (irdy i)) (zip [0..] outPorts)
        ++ concatMap (\(i, p) -> assignWire (esc $ vData useInterface p) (xdata i)) (zip [0..] outPorts)

    trdy0, trdy1 :: Text
    trdy0 = vlog_and [esc $ vIrdy useInterface inPort1, vlog_or . map selected_and_trdy . zip [0..] $ pairs outPorts]
    trdy1 = vlog_and [esc $ vIrdy useInterface inPort0, vlog_or . map selected_and_trdy . zip [0..] $ pairs outPorts]
    selected_and_trdy (i, (o0, o1)) = vlog_and $ [selected i, esc $ vTrdy useInterface o0, esc $ vTrdy useInterface o1]
    selected = vlog_equals (esc $ vData useInterface selPort) . vlog_number (nrBits $ length preds)
    irdy, xdata :: Int -> Text
    irdy i = vlog_and [selected (i `div` 2), esc $ vIrdy useInterface inPort0, esc $ vIrdy useInterface inPort1]
    xdata i = esc . vData useInterface $ lookupM (src 187) i fPorts

    selPort:fPorts = map fst3 $ functionInputPorts compContext
    inPort0:inPort1:[] = inputPorts (nrIns, comp)
    outPorts = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, _) = (2, Joitch "" preds, nrOuts)
    preds = XTrue : replicate ((nrOuts `div` 2) - 1) XFalse

    pairs [] = []
    pairs [_] = fatal 197 "Illegal component"
    pairs (a0:a1:as) = (a0, a1) : pairs as

-- | Generate a verilog module for a loadbalancer
loadBalancerModuleCode :: Bool -> Int -> [Text]
loadBalancerModuleCode useInterface nrOuts = componentModuleCode useInterface compContext body where
    body = declareEmptyRangedWire (src 199) (0, nrBits nrOuts) vSelWire
        ++ instantiateModule useInterface arbiter
        ++ assignWire (esc $ vTrdy useInterface i) trdy
        ++ concatMap (\(i', p) -> assignWire (esc $ vIrdy useInterface p) (irdy i')) (zip [0..] outPorts)
        ++ concatMap (\p -> assignWire (esc $ vData useInterface p) xdata) outPorts

    arbiter = VModuleInstance {
        vinstanceModule = arbiterModuleName nrOuts,
        vinstancePrimitive = False,
        vinstanceName = "arb",
        vinstanceParams = [],
        vinstanceHasTime = False,
        vinstanceHasRst = True,
        vinstanceInterface = vinstanceInterface'
    }
    vinstanceInterface' =
           map (\(i', p) -> (arbiterModuleClientPort i', esc $ vTrdy useInterface p, SingleChannel)) (zip [0..] outPorts)
        ++ [(arbiterModuleTransferPort, vlog_and[esc $ vIrdy useInterface i, esc $ vTrdy useInterface i], SingleChannel)]
        ++ [(arbiterModuleSelPort, vSelWire, SingleChannel)]

    trdy :: Text
    trdy = vlog_or $ map selected [0..length outPorts-1]
    irdy :: Int -> Text
    irdy i' = vlog_and [selected i', esc $ vIrdy useInterface i]
    xdata :: Text
    xdata = esc $ vData useInterface i

    selected :: Int -> Text
    selected i' = vlog_and[vlog_equals (esc vSelWire) (vlog_number (nrBits nrOuts) i'), esc . vTrdy useInterface $ lookupM (src 229) i' outPorts]

    [i] = inputPorts (nrIns, comp)
    outPorts = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, _) = (1, LoadBalancer "", nrOuts)

-- | Generate a verilog module for a match
matchModuleCode :: Bool -> [Text]
matchModuleCode useInterface = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface inPort0) trdy0
        ++ assignWire (esc $ vTrdy useInterface inPort1) trdy1
        ++ assignWire (esc $ vIrdy useInterface outPort0) irdy0
        ++ assignWire (esc $ vIrdy useInterface outPort1) irdy1
        ++ assignWire (esc $ vData useInterface outPort0) xdata0
        ++ assignWire (esc $ vData useInterface outPort1) xdata1

    trdy0, trdy1, irdy0, irdy1, xdata0, xdata1 :: Text
    trdy0 = transfer inPort0
    trdy1 = vlog_or [transfer outPort0, transfer outPort1]
    transfer p = vlog_and [esc $ vTrdy useInterface p, esc $ vIrdy useInterface p]
    irdy0 = vlog_and [esc $ vIrdy useInterface inPort0, esc $ vIrdy useInterface inPort1, esc $ vData useInterface matchPort]
    irdy1 = vlog_and [esc $ vIrdy useInterface inPort0, esc $ vIrdy useInterface inPort1, vlog_not . esc $ vData useInterface matchPort]
    xdata0 = esc $ vData useInterface f0Port
    xdata1 = esc $ vData useInterface f1Port

    matchPort:f0Port:f1Port:[] = map fst3 $ functionInputPorts compContext
    inPort0:inPort1:[] = inputPorts (nrIns, comp)
    outPort0:outPort1:[] = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, nrOuts) = (2, Match "" XTrue, 2)

-- | Generate a verilog module for a merge
mergeModuleCode :: Bool -> Int -> [Text]
mergeModuleCode useInterface nrIns = componentModuleCode useInterface compContext body where
    body = instantiateModule useInterface arbiter
        ++ concatMap (\(i, p) -> assignWire (esc $ vTrdy useInterface p) (trdy i)) (zip [0..] inPorts)
        ++ assignWire (esc $ vIrdy useInterface o) irdy
        ++ assignWire (esc $ vData useInterface o) xdata

    arbiter = VModuleInstance {
        vinstanceModule = arbiterModuleName nrIns,
        vinstancePrimitive = False,
        vinstanceName = "arb",
        vinstanceParams = [],
        vinstanceHasTime = False,
        vinstanceHasRst = True,
        vinstanceInterface = vinstanceInterface'
    }
    vinstanceInterface' =
           map (\(i, p) -> (arbiterModuleClientPort i, esc $ vIrdy useInterface p, SingleChannel)) (zip [0..] inPorts)
        ++ [(arbiterModuleTransferPort, vlog_and[esc $ vIrdy useInterface o, esc $ vTrdy useInterface o], SingleChannel)]
        ++ [(arbiterModuleSelPort, selWire, SingleChannel)]

    trdy :: Int -> Text
    trdy i = vlog_and [selected i, esc $ vTrdy useInterface o]
    irdy :: Text
    irdy = vlog_or $ map (esc . vIrdy useInterface) inPorts
    xdata :: Text
    xdata = esc $ vData useInterface fPort

    selected :: Int -> Text
    selected i = vlog_and [vlog_equals (esc selWire) (vlog_number (nrBits nrIns) i), esc . vIrdy useInterface $ lookupM (src 288) i inPorts]

    [selWire] = map (fst . snd) $ functionOutputPorts compContext
    [fPort] = map fst3 $ functionInputPorts compContext
    inPorts = inputPorts (nrIns, comp)
    [o] = outputPorts (comp, nrOuts)
    compContext@(_, comp, nrOuts) = (nrIns, Merge "", 1)

-- | Generate a verilog module for a multi-match
multiMatchModuleCode :: Bool -> (Int, Int) -> [Text]
multiMatchModuleCode useInterface (nrIns, nrOuts) = componentModuleCode useInterface compContext body where
    body = declareEmptyRangedWire (src 199) (0, nrBits nrMatches) vSelWire -- vSelWire div dIns = mSel, selarb mod dIns = dSel
        ++ instantiateModule useInterface arbiter
        ++ concatMap (flip assignWire vSelWire) selWires
        ++ concatMap (\(i, p) -> assignWire (esc $ vTrdy useInterface p) (trdy i)) (zip [0..] inPorts)
        ++ concatMap (\(i, p) -> assignWire (esc $ vIrdy useInterface p) (irdy i)) (zip [0..] outPorts)
        ++ concatMap (\(i, p) -> assignWire (esc $ vData useInterface p) (xdata i)) (zip [0..] outPorts)

    arbiter = VModuleInstance {
        vinstanceModule = arbiterModuleName nrMatches,
        vinstancePrimitive = False,
        vinstanceName = "arb",
        vinstanceParams = [],
        vinstanceHasTime = False,
        vinstanceHasRst = True,
        vinstanceInterface = vinstanceInterface'
    }
    vinstanceInterface' =
           map (\(i, (mp, dp)) -> (arbiterModuleClientPort i, client i mp dp, SingleChannel)) (zip [0..] matchCombos)
        ++ [(arbiterModuleTransferPort, transfer, SingleChannel)]
        ++ [(arbiterModuleSelPort, vSelWire, SingleChannel)]
    client :: Int -> Text -> Text -> Text
    client i mp dp = vlog_and[esc $ vIrdy useInterface mp, esc $ vIrdy useInterface dp, esc . vData useInterface $ lookupM (src 317) i functionInPorts]
    transfer :: Text
    transfer = vlog_or $ map (\p -> vlog_and[esc $ vIrdy useInterface p, esc $ vTrdy useInterface p]) outPorts
    matchCombos = [(mIn, dIn) | mIn <- take mIns inPorts, dIn <- drop mIns inPorts]

    trdy, trdy_m, trdy_d :: Int -> Text
    trdy i = if i < length outPorts then trdy_m i else trdy_d i
    trdy_m i = vlog_and [esc . vTrdy useInterface $ lookupM (src 324) i outPorts, irdy i]
    trdy_d i = vlog_or [ vlog_and[esc . vTrdy useInterface $ lookupM (src 325) j outPorts, selected (j*dIns + (i - mIns)) ] | j <- [0..mIns-1]]
    irdy :: Int -> Text
    irdy i = vlog_or[selected j| j <- map (+ (i*dIns)) [0..dIns-1]]
    xdata :: Int -> Text
    xdata i = esc . vData useInterface $ lookupM (src 329) (nrMatches + i) functionInPorts

    selected :: Int -> Text
    selected i = vlog_and[
          vlog_equals (esc vSelWire) $ vlog_number (nrBits nrMatches) i
        , esc . vIrdy useInterface $ lookupM (src 334) (i `div` dIns) inPorts -- match input irdy
        , esc . vIrdy useInterface $ lookupM (src 335) (mIns + i `mod` dIns) inPorts -- data input irdy
        , esc . vData useInterface $ lookupM (src 336) i functionInPorts -- packets from match and data inputs match
        ]

    dIns = nrIns - nrOuts
    mIns = nrOuts
    nrMatches = mIns * dIns
    selWires = map (fst . snd) $ functionOutputPorts compContext
    functionInPorts = map fst3 $ functionInputPorts compContext
    inPorts = inputPorts (nrIns, comp)
    outPorts = outputPorts (comp, nrOuts)
    compContext@(_, comp, _) = (nrIns, MultiMatch "" XTrue, nrOuts)

-- | Generate a verilog module for a queue
queueModuleCode :: Bool -> Bool -> [Text]
queueModuleCode useInterface hasInvariantAssertions = componentModuleCode useInterface compContext body where
    body = [
         "// highest bit needed to encode " +++qLength +++" positions"
        ,"localparam s = " +++qLength +++" < 2 ? 0 : $clog2(" +++qLength +++") - 1;"
        ,"localparam t = (" +++qLength +++" + 1) < 2 ? 0 : $clog2(" +++qLength +++" + 1) - 1;"
        ,"localparam l = " +++qDatasize +++" < 1 ? 0 : " +++qDatasize +++" - 1;"
        ,""
        ,"reg [s:0] in;"
        ,"reg [s:0] out;"
        ,"reg [l:0] data$addr [0:(" +++qLength +++"-1)];"
        ,"reg full;"
        ,""
        ,"wire [s:0] nextin = (in==(" +++qLength +++"-1)) ? 1'b 0 : (in+1'b1);"
        ,"wire [s:0] nextout = (out==(" +++qLength +++"-1)) ? 1'b 0 : (out+1'b1);"]
        ++ assignWire (esc $ vTrdy useInterface i) trdy
        ++ assignWire (esc $ vIrdy useInterface o) irdy
        ++ assignWire (esc $ vData useInterface o) xdata
        ++ declareWire "writing" (vlog_and [esc $ vIrdy useInterface i, esc $ vTrdy useInterface i])
        ++ declareWire "reading" (vlog_and [esc $ vIrdy useInterface o, esc $ vTrdy useInterface o])
        ++ [
         ""
        ,"always @(posedge clk) in <= rst ? 1'b 0 : (writing ? nextin : in);"
        ,"always @(posedge clk) out <= rst ? 1'b 0 : (reading ? nextout : out);"
        ,"always @(posedge clk) full <= (rst || reading) ? 1'b 0 : ((nextin==out && writing) ? 1'b 1 : full);"
        ,""
        ,"generate"
        ,"  genvar i;"
        ,"  for (i = 0; i < " +++qLength +++"; i = i + 1) begin: calcNewDataTypes"
        ,"      always @(posedge clk) begin"
        ,"          data$addr [i] <= (writing && (in==(i))) ? " +++esc (vData useInterface i) +++" : data$addr [i];"
        ,"      end"
        ,"  end"
        ,"endgenerate"
        ] ++ (if hasInvariantAssertions then[
             ""
            ,"wire[t:0] nr_of_packets = full ? " +++qLength +++" : in - out + (in < out ? " +++qLength +++" : 0);"
            ,""
            ,"wire[t:0] nr_of_packets_data[" +++qNumData +++"-1:0];"
            ,"wire[l:0] data[" +++qNumData +++"-1:0];"
            ,""
            ,""
            ,"wire has_data[0:" +++qLength +++"-1] ;"
            ,"generate"
            ,"  genvar i;"
            ,"  for (i = 0; i < " +++qLength +++"; i++) begin: hasData"
            ,"    assign has_data[i] = (full || out <= i && i < in) || (in < out && (out <= i || i < in));"
            ,"  end"
            ,"endgenerate"
            ,""
            ,"wire[t:0] tmp[0:" +++qLength +++"][" +++qNumData +++"-1:0];"
            ,"wire matches_data[0:" +++qLength +++"-1][" +++qNumData +++"-1:0];"
            ,""
            ,"wire tmp_match[0:l+1][0:" +++qLength +++"][" +++qNumData +++"-1:0];"
            ,"generate"
            ,"  genvar i, j, k;"
            ,"  for (k = 0; k < " +++qNumData +++"; k++) begin: countData"
            ,"    assign tmp[0][k] = 0;"
            ,"    for (i = 0; i < " +++qLength +++"; i++) begin: ADD"
            ,"      assign tmp[i+1][k] = matches_data[i][k] + tmp[i][k];"
            ,"      assign tmp_match[0][i][k] = 1 == 1;"
            ,""
            ,"      for (j = 0; j <= l; j++) begin"
            ,"        // ==? interprets x as a wildcard (matches anything)"
            ,"        assign tmp_match[j+1][i][k] = tmp_match[j][i][k] && (data$addr[i][j] ==? data[k][j]);"
            ,"      end"
            ,""
            ,"      assign matches_data[i][k] = has_data[i] && tmp_match[l+1][i][k];"
            ,"    end"
            ,"    assign nr_of_packets_data[k] = tmp[" +++qLength +++"][k];"
            ,"  end"
            ,"endgenerate"
            ] else [])

    trdy, irdy, xdata :: Text
    trdy = "!full"
    irdy = "!(in==out) || full"
    xdata = "(0 <= out && out < " +++qLength +++") ? data$addr [out] : data$addr [" +++qLength +++"-1]"

    [qLength, qNumData] = map fst $ parameters 0 comp
    [qDatasize] = map snd $ datasizeParameters useInterface compContext
    [i] = inputPorts (nrIns, comp)
    [o] = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, nrOuts) = (1, Queue "" 1, 1)

-- | Generate a verilog module for a sink
sinkModuleCode :: Bool -> [Text]
sinkModuleCode useInterface = componentModuleCode useInterface compContext body where
    body = ["assume_eager_sink: assume property (@(posedge clk) (" +++esc unbound +++" == 1));"]
        ++ [""]
        ++ ["reg " +++esc trdy +++";"]
        ++ [""]
        ++ ["always @(posedge clk) begin"]
        ++ indent (
               assignRegister trdy (vlog_ite (vlog_band[vlog_not . esc $ vIrdy useInterface i, esc trdy]) (esc trdy) (esc unbound))
            )
        ++ ["end"]
        ++ [""]
        ++ assignWire (esc $ vTrdy useInterface i) (esc trdy)

    trdy :: Text
    trdy = "trdy"

    [unbound] = map fst $ unboundInputPorts comp
    [i] = inputPorts (nrIns, comp)
    compContext@(nrIns, comp, _) = (1, Sink "", 0)

-- | Generate a verilog module for a source
sourceModuleCode :: Bool -> [Text]
sourceModuleCode useInterface = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vIrdy useInterface o) (esc unbound)
        ++ assignWire (esc $ vData useInterface o) (esc unbound_data)
        ++ [""]
        ++ ["assume property (@(posedge clk) (##[0:$] " +++esc unbound +++"));"]
        ++ [""]
        ++ ["reg [" +++datasize +++"-1:0] " +++esc xdata +++";"]
        ++ ["always @(posedge clk) begin"]
        ++ indent (
            assignRegister xdata (esc $ unbound_data)
            )
        ++ ["end"]
        ++ [""]
        ++ ["assume property (@(posedge clk) (" +++ esc (vIrdy useInterface o) +++ " & !"
             +++ esc (vTrdy useInterface o) +++ "|=> " +++ esc (vIrdy useInterface o) +++ "));"]
        ++ ["assume property (@(posedge clk) (" +++ esc (vIrdy useInterface o) +++ " & !"
             +++ esc (vTrdy useInterface o) +++ "|=> " +++ esc (vData useInterface o) +++ " == " +++ esc xdata +++ "));"]

    xdata :: Text
    xdata = "data"

    [unbound, unbound_data] = map fst $ unboundInputPorts comp
    [o] = outputPorts (comp, nrOuts)
    [datasize] = map snd $ datasizeParameters useInterface compContext
    compContext@(_, comp, nrOuts) = (0, Source "" nul, 1)

-- | Generate a verilog module for a switch
switchModuleCode :: Bool -> Int -> [Text]
switchModuleCode useInterface nrOuts = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface i) trdy
        ++ concatMap (\(i', p) -> assignWire (esc $ vIrdy useInterface p) (irdy i')) (zip [0..] outPorts)
        ++ concatMap (\(i', p) -> assignWire (esc $ vData useInterface p) (xdata i')) (zip [0..] outPorts)

    trdy :: Text
    trdy = vlog_or $ map (\p -> vlog_and[esc $ vIrdy useInterface p, esc $ vTrdy useInterface p]) outPorts
    irdy, selected :: Int -> Text
    irdy i' = vlog_and [esc $ vIrdy useInterface i, selected i']
    selected i' = vlog_equals (esc $ vData useInterface sel) (vlog_number (nrBits nrOuts) i')
    xdata :: Int -> Text
    xdata i' = esc . vData useInterface $ lookupM (src 336) i' dataInPorts

    sel:dataInPorts = map fst3 $ functionInputPorts compContext
    [i] = inputPorts (nrIns, comp)
    outPorts = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, _) = (1, Madl.Network.Switch "" (replicate nrOuts XTrue), nrOuts)

-- | Generate a verilog module for a vars component
varsModuleCode :: Bool -> [Text]
varsModuleCode useInterface = componentModuleCode useInterface compContext body where
    body = assignWire (esc $ vTrdy useInterface i)  (esc $ vTrdy useInterface o)
        ++ assignWire (esc $ vIrdy useInterface o) (esc $ vIrdy useInterface i)
        ++ assignWire (esc $ vData useInterface o) (esc $ vData useInterface i)

    [i] = inputPorts (nrIns, comp)
    [o] = outputPorts (comp, nrOuts)
    compContext@(nrIns, comp, nrOuts) = (1, Vars "", 1)

-- | Generate a verilog module for a fair arbiter with the given number of clients
arbiterModuleCode :: Bool -> Int -> [Text]
arbiterModuleCode useInterface nrClients = declareModule useInterface vmodule where
    vmodule = VModule {
        vmoduleName = arbiterModuleName nrClients,
        vmoduleParams = [],
        vmoduleHasTime = False,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface',
        vmoduleBody = body
    }

    vmoduleInterface' =
           map (\i -> VInterfacePort (Just MInput) (Left Nothing) (arbiterModuleClientPort i)) [0..nrClients-1]
        ++ [VInterfacePort (Just MInput) (Left Nothing) arbiterModuleTransferPort]
        ++ [VInterfacePort (Just MOutput) (Left . Just . Left $ nrBits nrClients) arbiterModuleSelPort]

    body =
           (if nrClients > 2 then declareEmptyRangedWire (src 423) (0, nrBits $ nrClients-1) "sel2" else [])
        ++ (if nrClients > 2 then instantiateModule useInterface arbiter else [])
        ++ [
         "reg " +++declareRange (src 426) (0, nrBits nrClients) +++" prevSel;"
        ,"reg transferReg;"
        ,""
        ,"always @(posedge clk) prevSel <= rst ? 1'b 0 : " +++arbiterModuleSelPort +++";"
        ,"always @(posedge clk) transferReg <= rst ? 1'b 0 : " +++arbiterModuleTransferPort +++";"
        ]
        ++ assignWire arbiterModuleSelPort (
            vlog_ite "rst" "1'b 0" $
                vlog_ite (vlog_and [vlog_not $ arbiterModuleClientPort i | i <- [0..nrClients-2]]) maxClient $
                    vlog_ite (vlog_not . arbiterModuleClientPort $ nrClients - 1) otherArb $
                        vlog_ite "transferReg"
                            (vlog_ite (vlog_equals "prevSel" maxClient) otherArb maxClient)
                            "prevSel"
            )
    maxClient = (vlog_number (nrBits nrClients) (nrClients-1))
    otherArb = if nrClients > 2 then "sel2" else vlog_number 1 0

    arbiter = VModuleInstance {
        vinstanceModule = arbiterModuleName (nrClients-1),
        vinstancePrimitive = False,
        vinstanceName = "arb",
        vinstanceParams = [],
        vinstanceHasTime = False,
        vinstanceHasRst = True,
        vinstanceInterface = vinstanceInterface'
    }
    vinstanceInterface' =
           map (\i -> (arbiterModuleClientPort i, arbiterModuleClientPort i, SingleChannel)) [0..nrClients-2]
        ++ [(arbiterModuleTransferPort, arbiterModuleTransferPort, SingleChannel)]
        ++ [(arbiterModuleSelPort, "sel2", SingleChannel)]

-- | Generate a verilog module for a general verilog component
componentModuleCode :: Bool -> (Int, Component, Int) -> [Text] -> [Text]
componentModuleCode useInterface compContext@(nrIns, comp, nrOuts) body = declareModule useInterface vmodule where
    vmodule = VModule {
        vmoduleName = moduleName compContext,
        vmoduleParams = map (\(n, v) -> (n, v comp)) (parameters 0 comp) ++ map (\(_, n) -> (n, "1")) (datasizeParameters useInterface compContext),
        vmoduleHasTime = hasTime comp,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface',
        vmoduleBody = body
    }
    vmoduleInterface' =
           map (uncurry inputToInterface ) (zip [0..] $ inputPorts (nrIns, comp))
        ++ map (uncurry outputToInterface) (zip [0..] $ outputPorts (comp, nrOuts))
        ++ map functionInToInterface (functionInputPorts compContext)
        ++ map (functionOutToInterface . snd) (functionOutputPorts compContext)
        ++ map unboundToInterface (unboundInputPorts comp)

    inputToInterface :: Int -> Text -> VInterfacePort
    inputToInterface i portName = VInterfacePort (Just MInput) (Right . Just . Data $ Right datasize) portName where
        datasize = lookupM (src 201) i $ inputDataSize (nrIns, comp)

    outputToInterface :: Int -> Text -> VInterfacePort
    outputToInterface i portName = VInterfacePort (Just MOutput) (Right . Just . Data $ Right datasize) portName where
        datasize = lookupM (src 205) i $ outputDataSize (comp, nrOuts)

    functionInToInterface :: VFPort -> VInterfacePort
    functionInToInterface (portName, _, vfporttype) = VInterfacePort (Just MInput) (Right $ Just vporttype) portName where
        vporttype = case vfporttype of
            Output i -> Madl2Verilog.VerilogConstants.Function (Right datasize) where
                datasize = lookupM (src 205) i $ outputDataSize (comp, nrOuts)
            Selection cs -> Madl2Verilog.VerilogConstants.Function (Left $ encodingSize cs)

    functionOutToInterface :: (VPortName, ColorSet) -> VInterfacePort
    functionOutToInterface (portName, cs) = VInterfacePort (Just MOutput) (Left $ fmap Left size) portName where
        size = case encodingSize cs of 0 -> Nothing; 1 -> Nothing; n -> Just n;

    unboundToInterface :: (VPortName, UnboundTarget) -> VInterfacePort
    unboundToInterface (portName, target) = VInterfacePort (Just MInput) (Left size) portName where
        size = case target of XIrdy{} -> Nothing; XTrdy{} -> Nothing; XData i -> Just . Right $ datasize i;
        datasize :: Int -> Text
        datasize i = lookupM (src 571) i $ outputDataSize (comp, nrOuts)

--------------------------------------------
-- Madl channel interface
--------------------------------------------

-- | Generate a system verilog interface for madl channels
chanInterface :: [Text]
chanInterface = [
     "interface chan #(parameter SIZE = 1);"
    ,""
    ,"    // highest bit needed to encoded the given size"
    ,"    localparam S = SIZE < 1 ? 0 : SIZE - 1;"
    ,""
    ,"    logic irdy;"
    ,"    logic trdy;"
    ,"    logic [S:0] data;"
    ,""
    ,"    modport data_input (input irdy, input data, output trdy);"
    ,"    modport token_input (input irdy, output trdy);"
    ,"    modport data_output (output irdy, output data, input trdy);"
    ,"    modport token_output (output irdy, input trdy);"
    ,"    modport function_input (input data);"
    ,"    modport function_output (output data);"
    ,"endinterface"
    ,""
    ]