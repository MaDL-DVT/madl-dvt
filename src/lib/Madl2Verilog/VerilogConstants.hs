{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Madl2Verilog.VerilogConstants
Description : Constants and naming conventions for verilog generation.
Copyright   : (c) Tessa Belder 2015-2016

Constants and naming conventions for verilog generation.
-}
module Madl2Verilog.VerilogConstants (
    moduleName,
    VPortType(..), VFPortType(..), MPortType(..),
    VChannelName, VPortName,
    VParameter,
    VFPort, VParam, MadlPort,
    inputPorts, functionInputPorts,
    unboundInputPorts, UnboundTarget(..),
    outputPorts, topLevelOutputPorts, functionOutputPorts,
    outputFunctions,
    parameters, datasizeParameters,
    inputDataSize, outputDataSize,
    hasTime, hasTimeFunction,

    arbiterModuleName, arbiterModuleClientPort,
    arbiterModuleTransferPort, arbiterModuleSelPort,
    vSelWire,

    vDefinitions, vToken,
    vAssertionDefinitions,
    modPortName, vChannel,
    vIrdy, vTrdy, vData,
    vDirection, vPortType,

    VInterfacePort(..), wireSize,
    vClk, vRst, vTime,
    vDefaultInterface,
    vWrapperModule, vAssertUnbound,
    vAutomaton,
    vType, vFunction, vTopFunctionName,
    vMatchSwitchName,
    vFunModule, vFunInstance, vFunChan,
    vFunInputPort, vFunOutputPort,
    vMacroTypeParam,
    svAssertionModule, svAssertionModuleName,
    svAssumptionPos, svAssumptionNeg,
    svAssertionPos, svAssertionNeg, svAssertionInvariantName,
    svAssertionNotFullName, svAssertionDeadLockName, svAssertionBlockName,
    mergeFunction, vSelect,
    VerilogCode, indent, indents, (>.), Range, declareRange, declareTextRange, esc
) where

import qualified Data.IntMap as IM
import qualified Data.Text as T

import Utils.Map
import Utils.Text

import Madl.MsgTypes
import qualified Madl.Network as Madl

-- | Error function
fileName :: Text
fileName = "Madl2Verilog.VerilogConstants"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

--------------------------------------------
-- Constants of the basic Madl components --
--------------------------------------------

-- | Modulenames of the basic Madl components
moduleName :: (Int, Madl.XComponent c, Int) -> Text
moduleName (_nrIns, Madl.Source{},        _nrOuts) = "Source"
moduleName (_nrIns, Madl.PatientSource{}, _nrOuts) = "Source"
moduleName (_nrIns, Madl.Sink{},          _nrOuts) = "Sink"
moduleName (_nrIns, Madl.DeadSink{},      _nrOuts) = "DeadSink"
moduleName (_nrIns, Madl.Function{},      _nrOuts) = fatal 46 "Function does not have a standard verilog module"
moduleName (_nrIns, Madl.Queue{},         _nrOuts) = "Queue"
moduleName (_nrIns, Madl.Vars{},          _nrOuts) = "Vars"
moduleName (_nrIns, Madl.Cut{},           _nrOuts) = "Cut"
moduleName (_nrIns, Madl.Switch{},         nrOuts) = "Switch" +++ showT nrOuts
moduleName ( nrIns, Madl.Merge{},         _nrOuts) = "Merge" +++ showT nrIns
moduleName (_nrIns, Madl.Fork{},           nrOuts) = "Fork" +++ showT nrOuts
moduleName ( nrIns, Madl.ControlJoin{},   _nrOuts) = "CTRLJoin" +++ showT nrIns
moduleName (_nrIns, Madl.FControlJoin{},  _nrOuts) = "FCTRLJoin"
moduleName (_nrIns, Madl.Match{},         _nrOuts) = "Match"
moduleName ( nrIns, Madl.MultiMatch{},     nrOuts) = "MultiMatch" +++ showT nrIns >. showT nrOuts
moduleName (_nrIns, Madl.LoadBalancer{},   nrOuts) = "LoadBalancer" +++ showT nrOuts
moduleName (_nrIns, Madl.Joitch{},         nrOuts) = "Joitch" +++ showT (nrOuts `div` 2)
moduleName (_nrIns, Madl.Automaton{},     _nrOuts) = fatal 84 "Automaton does not have a standard verilog module"
moduleName (_nrIns, Madl.GuardQueue{},     _nrOuts) = fatal 99 "GuardQueue does not have a standard verilog module"

-- | Possible types of interface ports
data VPortType =  Data (Either Int Text) | Token | Function (Either Int Text) deriving (Show, Eq)

-- | Possible types of component functions:
-- 1. Output: The function determines the output data of the component. The Int variable determines which output port the data should be written to.
-- 2. Selection: The function returns some selection result. The ColorSet variable describes the type of this selection result.
data VFPortType = Output Int | Selection ColorSet deriving (Eq)
-- | As a single component can have multiple functions, each one of them has an index
type VFPortIndex = Int

-- | Auxiliary datatype for readability
type VChannelName = Text
-- | Auxiliary datatype for readability
type VPortName = Text
-- | Auxiliary datatype for readability
type VParamName = Text
-- | Auxiliary datatype for readability
type VParamValue = Text
-- | Auxiliary datatype for readability
type MadlPortID = Int

-- | A verilog parameter consists of the name of the parameter and value of the parameter
type VParameter = (VParamName, VParamValue)

-- | A madl port is either an input or an output port
data MPortType = MInput | MOutput deriving (Show)

-- | A verilog function port has a name, an index, and a type
type VFPort = (VPortName, VFPortIndex, VFPortType)
-- | A madl port consists of an id number and a type
type MadlPort = (MadlPortID, MPortType)

-- | Input ports of the basic Madl components
inputPorts :: (Int, Madl.XComponent c) -> [VPortName]
inputPorts (_nrIns, Madl.Source{}       ) = []
inputPorts (_nrIns, Madl.PatientSource{}) = []
inputPorts (_nrIns, Madl.Sink{}         ) = ["i0"]
inputPorts (_nrIns, Madl.DeadSink{}     ) = ["i0"]
inputPorts (_nrIns, Madl.Function{}     ) = [vFunInputPort 0]
inputPorts (_nrIns, Madl.Queue{}        ) = ["i0"]
inputPorts (_nrIns, Madl.Vars{}         ) = ["i0"]
inputPorts (_nrIns, Madl.Cut{}          ) = ["i0"]
inputPorts (_nrIns, Madl.Switch{}       ) = ["i0"]
inputPorts ( nrIns, Madl.Merge{}        ) = map (("i" +++) . showT) [0..nrIns-1]
inputPorts (_nrIns, Madl.Fork{}         ) = ["i0"]
inputPorts ( nrIns, Madl.ControlJoin{}  ) = map (("i" +++) . showT) [0..nrIns-1]
inputPorts (_nrIns, Madl.FControlJoin{} ) = ["i0", "i1"]
inputPorts (_nrIns, Madl.Match{}        ) = ["i0", "i1"]
inputPorts ( nrIns, Madl.MultiMatch{}   ) = map (("i" +++) . showT) [0..nrIns-1]
inputPorts (_nrIns, Madl.LoadBalancer{} ) = ["i0"]
inputPorts (_nrIns, Madl.Joitch{}       ) = ["i0", "i1"]
inputPorts ( nrIns, Madl.Automaton{}    ) = map (("i" +++) . showT) [0..nrIns-1]
inputPorts ( nrIns, Madl.GuardQueue{}   ) = map (("i" +++) . showT) [0..nrIns-1]

-- | Inputs of a module that are used to directly drive an output of the module
-- These inputs will be unbound. I.e. they will be exposed in the interface of the top module,
-- so that they can be driven by a test bench.
unboundInputPorts :: Madl.XComponent c -> [(VPortName, UnboundTarget)]
unboundInputPorts comp = case comp of
    Madl.Source{}        -> [("unbound_irdy", XIrdy 0), ("unbound_data", XData 0)]
    Madl.PatientSource{} -> [("unbound_irdy", XIrdy 0), ("unbound_data", XData 0)]
    Madl.Sink{}          -> [("unbound_trdy", XTrdy 0)]
    Madl.DeadSink{}      -> []
    Madl.Function{}      -> []
    Madl.Queue{}         -> []
    Madl.Vars{}          -> []
    Madl.Cut{}           -> []
    Madl.Switch{}        -> []
    Madl.Merge{}         -> []
    Madl.Fork{}          -> []
    Madl.ControlJoin{}   -> []
    Madl.FControlJoin{}  -> []
    Madl.Match{}         -> []
    Madl.MultiMatch{}    -> []
    Madl.LoadBalancer{}  -> []
    Madl.Joitch{}        -> []
    Madl.Automaton{}     -> []
    Madl.GuardQueue{}     -> []

-- | Identifies an output to be driven by an unbound wire.
data UnboundTarget = XIrdy Int | XTrdy Int | XData Int

-- | Function input ports of the basic Madl components
functionInputPorts :: (Int, Madl.Component, Int) -> [VFPort]
functionInputPorts (nrIns, comp, nrOuts) = map (\(i, (n, t)) -> (n, i, t)) . zip [0..] $ case comp of
    Madl.Source{}        -> []
    Madl.PatientSource{} -> []
    Madl.Sink{}          -> []
    Madl.DeadSink{}      -> []
    Madl.Function{}      -> []
    Madl.Queue{}         -> []
    Madl.Vars{}          -> []
    Madl.Cut{}           -> []
    Madl.Switch{}        -> ("sel", Selection $ intColorSet nrOuts) : map (\i -> ("f" +++ showT i, Output i)) [0..nrOuts-1]
    Madl.Merge{}         -> [("f", Output 0)]
    Madl.Fork{}          -> []
    Madl.ControlJoin{}   -> []
    Madl.FControlJoin{}  -> [("f", Output 0)]
    Madl.Match{}         -> [("match", Selection boolColorSet), ("f0", Output 0), ("f1", Output 1)]
    Madl.MultiMatch{}    -> [("match" +++ showT i >. showT j, Selection boolColorSet) | i <- [0..nrOuts-1], j <- [nrOuts..nrIns - 1]]
                            ++ map (\i -> ("f" +++ showT i, Output i)) [0..nrOuts-1]
    Madl.LoadBalancer{}  -> []
    Madl.Joitch{}        -> ("sel", Selection . intColorSet $ nrOuts `div` 2) : map (\i -> ("f" +++ showT i, Output i)) [0..nrOuts-1]
    Madl.Automaton{}     -> []
    Madl.GuardQueue{}    -> [("f", Output 0)]

-- | Output ports of the basic Madl components
outputPorts :: (Madl.XComponent c, Int) -> [VPortName]
outputPorts (Madl.Source{},        _nrOuts) = ["o0"]
outputPorts (Madl.PatientSource{}, _nrOuts) = ["o0"]
outputPorts (Madl.Sink{},          _nrOuts) = []
outputPorts (Madl.DeadSink{},      _nrOuts) = []
outputPorts (Madl.Function{},      _nrOuts) = [vFunOutputPort]
outputPorts (Madl.Queue{},         _nrOuts) = ["o0"]
outputPorts (Madl.Vars{},          _nrOuts) = ["o0"]
outputPorts (Madl.Cut{},           _nrOuts) = ["o0"]
outputPorts (Madl.Switch{},         nrOuts) = map (("o" +++) . showT) [0..nrOuts-1]
outputPorts (Madl.Merge{},         _nrOuts) = ["o0"]
outputPorts (Madl.Fork{},           nrOuts) = map (("o" +++) . showT) [0..nrOuts-1]
outputPorts (Madl.ControlJoin{},   _nrOuts) = ["o0"]
outputPorts (Madl.FControlJoin{},  _nrOuts) = ["o0"]
outputPorts (Madl.Match{},         _nrOuts) = ["o0", "o1"]
outputPorts (Madl.MultiMatch{},     nrOuts) = map (("o" +++) . showT) [0..nrOuts-1]
outputPorts (Madl.LoadBalancer{},   nrOuts) = map (("o" +++) . showT) [0..nrOuts-1]
outputPorts (Madl.Joitch{},         nrOuts) = map (("o" +++) . showT) [0..nrOuts-1]
outputPorts (Madl.Automaton{},      nrOuts) = map (("o" +++) . showT) [0..nrOuts-1]
outputPorts (Madl.GuardQueue{},    _nrOuts) = ["o0"]

-- | Output ports of the basic Madl components that are exposed at top-level
topLevelOutputPorts :: Madl.XComponent c -> [(VPortName, UnboundTarget)]
topLevelOutputPorts comp = case comp of
    Madl.Source{}        -> [("trdy", XTrdy 0)]
    Madl.PatientSource{} -> [("trdy", XTrdy 0)]
    Madl.Sink{}          -> [("irdy", XIrdy 0), ("data", XData 0)]
    Madl.DeadSink{}      -> []
    Madl.Function{}      -> []
    Madl.Queue{}         -> []
    Madl.Vars{}          -> []
    Madl.Cut{}           -> []
    Madl.Switch{}        -> []
    Madl.Merge{}         -> []
    Madl.Fork{}          -> []
    Madl.ControlJoin{}   -> []
    Madl.FControlJoin{}  -> []
    Madl.Match{}         -> []
    Madl.MultiMatch{}    -> []
    Madl.LoadBalancer{}  -> []
    Madl.Joitch{}        -> []
    Madl.Automaton{}     -> []
    Madl.GuardQueue{}    -> []

-- | Outputports of the basic Madl components that are input to one of their functions
functionOutputPorts :: (Int, Madl.XComponent c, Int) -> [(Int, (VPortName, ColorSet))]
functionOutputPorts (_nrIns, Madl.Source{},        _nrOuts) = []
functionOutputPorts (_nrIns, Madl.PatientSource{}, _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Sink{},          _nrOuts) = []
functionOutputPorts (_nrIns, Madl.DeadSink{},      _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Function{},      _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Queue{},         _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Vars{},          _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Cut{},           _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Switch{},        _nrOuts) = []
functionOutputPorts ( nrIns, Madl.Merge{},         _nrOuts) = [(0, (vSelWire, intColorSet nrIns))]
functionOutputPorts (_nrIns, Madl.Fork{},          _nrOuts) = []
functionOutputPorts (_nrIns, Madl.ControlJoin{},   _nrOuts) = []
functionOutputPorts (_nrIns, Madl.FControlJoin{},  _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Match{},         _nrOuts) = []
functionOutputPorts ( nrIns, Madl.MultiMatch{},     nrOuts) = [(i, ("sel" +++ showT i, intColorSet n)) | let n = nrOuts * (nrIns - nrOuts), i <- [n..n+nrOuts-1]]
functionOutputPorts (_nrIns, Madl.LoadBalancer{},  _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Joitch{},        _nrOuts) = []
functionOutputPorts (_nrIns, Madl.Automaton{},     _nrOuts) = []
functionOutputPorts ( nrIns, Madl.GuardQueue{},    _nrOuts) = [(0, (vSelWire, intColorSet nrIns))]

-- | A boolean colorset consists of the values 0 and 1
boolColorSet :: ColorSet
boolColorSet = intColorSet 2

-- | An integer colorset of size n consists of the values 0..n-1
intColorSet :: Int -> ColorSet
intColorSet n = makeColorSet [("", Right $ bitvecFromInts [0..n-1])]

-- | Functions to find the output functions of a component. Amount must match the amount of function input ports of the component, with exception of the function component.
outputFunctions :: (Int, Madl.XComponent c, Int) -> [Either (Madl.XComponent c -> MFunctionDisj) (Madl.XComponent c -> MFunctionBool)]
outputFunctions (_nrIns, Madl.Source{},        _nrOuts) = []
outputFunctions (_nrIns, Madl.PatientSource{}, _nrOuts) = []
outputFunctions (_nrIns, Madl.Sink{},          _nrOuts) = []
outputFunctions (_nrIns, Madl.DeadSink{},      _nrOuts) = []
outputFunctions (_nrIns, Madl.Function{},      _nrOuts) = [Left (flip XAppliedTo [XVar 0] . Madl.function)]
outputFunctions (_nrIns, Madl.Queue{},         _nrOuts) = []
outputFunctions (_nrIns, Madl.Vars{},          _nrOuts) = []
outputFunctions (_nrIns, Madl.Cut{},           _nrOuts) = []
outputFunctions (_nrIns, Madl.Switch{},         nrOuts) = [Left (switchFunction . Madl.switching)] ++ replicate nrOuts (Left . const $ XVar 0)
outputFunctions ( nrIns, Madl.Merge{},         _nrOuts) = [Left (const $ mergeFunction nrIns)]
outputFunctions (_nrIns, Madl.Fork{},          _nrOuts) = []
outputFunctions (_nrIns, Madl.ControlJoin{},   _nrOuts) = []
outputFunctions (_nrIns, Madl.FControlJoin{},  _nrOuts) = [Left (fControlJoinFunction . Madl.matchFunction)]
outputFunctions (_nrIns, Madl.Match{},         _nrOuts) = [Right (flip XAppliedToB [XVar 0, XVar 1] . Madl.matchFunction), Left (const $ XVar 0), Left (const $ XVar 0)]
outputFunctions ( nrIns, Madl.MultiMatch{},     nrOuts) = [Right (multiMatchFunction mIn dIn . Madl.matchFunction) | mIn <- [0..nrOuts-1], dIn <- [nrOuts..nrIns-1]]
                                                        ++ replicate nrOuts (Left . const $ multiMatchFunction2 nrIns nrOuts)
outputFunctions (_nrIns, Madl.LoadBalancer{},  _nrOuts) = []
outputFunctions (_nrIns, Madl.Joitch{},         nrOuts) = [Left (joitchFunction . Madl.predicates)] ++ map (\o -> Left (const . XVar $ o `mod` 2)) [0..nrOuts-1]
outputFunctions (_nrIns, Madl.Automaton{},     _nrOuts) = []
outputFunctions ( nrIns, Madl.GuardQueue{},    _nrOuts) = [Left (const $ mergeFunction nrIns)]

-- | Function of a switch component
switchFunction :: [MFunctionBool] -> MFunctionDisj
switchFunction = switchFunction' 0
switchFunction' :: Int -> [MFunctionBool] -> MFunctionDisj
switchFunction' _ [] = XChoice "" . Right $ XConst 0
switchFunction' i (p:preds) = XIfThenElseD (XAppliedToB p [XVar 0]) (XChoice "" . Right $ XConst i) (switchFunction' (i+1) preds)

-- | Function of an fcontroljoin component
fControlJoinFunction :: MFunctionBool -> MFunctionDisj
fControlJoinFunction p = XIfThenElseD (XAppliedToB p [XVar 0, XVar 1]) (XVar 0) (XVar 1)

-- | Function of a joitch component
joitchFunction :: [MFunctionBool] -> MFunctionDisj
joitchFunction = joitchFunction' 0
joitchFunction' :: Int -> [MFunctionBool] -> MFunctionDisj
joitchFunction' _ [] = XChoice "" . Right $ XConst 0
joitchFunction' i (p:preds) = XIfThenElseD (XAppliedToB p [XVar 0, XVar 1]) (XChoice "" . Right $ XConst i) (joitchFunction' (i+1) preds)

-- | Function of a merge comopnent
mergeFunction :: Int -> MFunctionDisj
mergeFunction = mergeFunction' 0
mergeFunction' :: Int -> Int -> MFunctionDisj
mergeFunction' i nrIns = if i == nrIns then XVar 0
    else XIfThenElseD (XCompare Eq (XChooseVal "" $ XVar nrIns) (XConst i)) (XVar i) (mergeFunction' (i+1) nrIns)

-- | Function of a multimatch component
multiMatchFunction :: Int -> Int -> MFunctionBool -> MFunctionBool
multiMatchFunction mIn dIn = flip XAppliedToB [XVar dIn, XVar mIn]

-- | Arbiter function of a multimatch component
multiMatchFunction2 :: Int -> Int -> MFunctionDisj
multiMatchFunction2 = multiMatchFunction2' 0
multiMatchFunction2' :: Int -> Int -> Int -> MFunctionDisj
multiMatchFunction2' i nrIns nrOuts = if i == mIns * dIns then XVar mIns
    else XIfThenElseD (XCompare Eq (XChooseVal "" $ XVar nrIns) (XConst i)) (XVar $ mIns + (i `mod` dIns)) (multiMatchFunction2' (i+1) nrIns nrOuts) where
        mIns = nrOuts
        dIns = nrIns - nrOuts

-- | A parameter has name and function to derive its value
type VParam c = (VParamName, Madl.XComponent c -> Text)

-- | Parameters of the basic Madl components
parameters :: Int -> Madl.XComponent c -> [VParam c]
parameters numDataSize component = case component of
    Madl.Source{}        -> []
    Madl.PatientSource{} -> []
    Madl.Sink{}          -> []
    Madl.DeadSink{}      -> []
    Madl.Function{}      -> []
    Madl.Queue{}         -> [("LENGTH", showT . Madl.capacity), ("NUM_DATA", \_ -> showT numDataSize)]
    Madl.Vars{}          -> []
    Madl.Cut{}           -> []
    Madl.Switch{}        -> []
    Madl.Merge{}         -> []
    Madl.Fork{}          -> []
    Madl.ControlJoin{}   -> []
    Madl.FControlJoin{}  -> []
    Madl.Match{}         -> []
    Madl.MultiMatch{}    -> []
    Madl.LoadBalancer{}  -> []
    Madl.Joitch{}        -> []
    Madl.Automaton{}     -> []
    Madl.GuardQueue{}    -> [("LENGTH", showT . Madl.capacity), ("NUM_DATA", \_ -> showT numDataSize)]

-- | Tells whether the basic Madl components make internal use of some datasize
datasizeParameters :: Bool -> (Int, Madl.XComponent c, Int) -> [(MadlPort, VParamName)]
datasizeParameters True (_, Madl.Source{},        _) = []
datasizeParameters True (_, Madl.PatientSource{}, _) = []
datasizeParameters True (_, Madl.Sink{},          _) = []
datasizeParameters True (_, Madl.DeadSink{},      _) = []
datasizeParameters True (_, Madl.Function{},      _) = []
datasizeParameters True (_, Madl.Queue{},         _) = [((0, MInput), "DATASIZE")]
datasizeParameters True (_, Madl.Vars{},          _) = []
datasizeParameters True (_, Madl.Cut{},          _) = []
datasizeParameters True (_, Madl.Switch{},        _) = []
datasizeParameters True (_, Madl.Merge{},         _) = []
datasizeParameters True (_, Madl.Fork{},          _) = []
datasizeParameters True (_, Madl.ControlJoin{},   _) = []
datasizeParameters True (_, Madl.FControlJoin{},  _) = []
datasizeParameters True (_, Madl.Match{},         _) = []
datasizeParameters True (_, Madl.MultiMatch{},    _) = []
datasizeParameters True (_, Madl.LoadBalancer{},  _) = []
datasizeParameters True (_, Madl.Joitch{},        _) = []
datasizeParameters True (_, Madl.Automaton{},     _) = []
datasizeParameters True (_, Madl.GuardQueue{},    _) = [((0, MInput), "DATASIZE")]


datasizeParameters False (_nrIns, Madl.Source{},        _nrOuts) = [((0, MOutput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.PatientSource{}, _nrOuts) = [((0, MOutput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.Sink{},          _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.DeadSink{},      _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.Function{},      _nrOuts) = []
datasizeParameters False (_nrIns, Madl.Queue{},         _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.Vars{},          _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.Cut{},           _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.Switch{},         nrOuts) = [((0, MInput), "INPUTSIZE")] ++ map (\i -> ((i, MOutput), "OUTPUTSIZE" +++ showT i)) [0..nrOuts-1]
datasizeParameters False ( nrIns, Madl.Merge{},         _nrOuts) = map (\i -> ((i, MInput), "INPUTSIZE" +++ showT i)) [0..nrIns-1] ++ [((0, MOutput), "OUTPUTSIZE")]
datasizeParameters False (_nrIns, Madl.Fork{},          _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False ( nrIns, Madl.ControlJoin{},   _nrOuts) = map (\i -> ((i, MInput), "INPUTSIZE" +++ showT i)) [0..nrIns-1] ++ [((0, MOutput), "OUTPUTSIZE")]
datasizeParameters False (_nrIns, Madl.FControlJoin{},  _nrOuts) = [((0, MInput), "INPUTSIZE0"), ((1, MInput), "INPUTSIZE1"), ((0, MOutput), "OUTPUTSIZE")]
datasizeParameters False (_nrIns, Madl.Match{},         _nrOuts) = [((0, MInput), "INPUTSIZE0"), ((1, MInput), "INPUTSIZE1"),
                                                                    ((0, MOutput), "OUTPUTSIZE0"), ((1, MOutput), "OUTPUTSIZE1")]
datasizeParameters False ( nrIns, Madl.MultiMatch{},     nrOuts) = map (\i -> ((i, MInput), "INPUTSIZE" +++ showT i)) [0..nrIns-1]
                                                                    ++ map (\i -> ((i, MOutput), "OUTPUTSIZE" +++ showT i)) [0..nrOuts-1]
datasizeParameters False (_nrIns, Madl.LoadBalancer{},  _nrOuts) = [((0, MInput), "DATASIZE")]
datasizeParameters False (_nrIns, Madl.Joitch{},         nrOuts) = [((0, MInput), "INPUTSIZE0"), ((1, MInput), "INPUTSIZE1")]
                                                                    ++ map (\i -> ((i, MOutput), "OUTPUTSIZE" +++ showT i)) [0..nrOuts-1]
datasizeParameters False (_nrIns, Madl.Automaton{},     _nrOuts) = []
datasizeParameters False ( nrIns, Madl.GuardQueue{},    _nrOuts) = map (\i -> ((i, MInput), "INPUTSIZE" +++ showT i)) [0..nrIns-1] ++ [((0, MOutput), "OUTPUTSIZE")] ++ [((0, MInput), "DATASIZE")]

-- | Input datasize parameters of the basic madl components
inputDataSize :: (Int, Madl.XComponent c) -> IntMap VParamName
inputDataSize (_nrIns, Madl.Source{}       ) = IM.empty
inputDataSize (_nrIns, Madl.PatientSource{}) = IM.empty
inputDataSize (_nrIns, Madl.Sink{}         ) = IM.singleton 0 "DATASIZE"
inputDataSize (_nrIns, Madl.DeadSink{}     ) = IM.singleton 0 "DATASIZE"
inputDataSize (_nrIns, Madl.Function{}     ) = IM.empty
inputDataSize (_nrIns, Madl.Queue{}        ) = IM.singleton 0 "DATASIZE"
inputDataSize (_nrIns, Madl.Vars{}         ) = IM.singleton 0 "DATASIZE"
inputDataSize (_nrIns, Madl.Cut{}          ) = IM.singleton 0 "DATASIZE"
inputDataSize (_nrIns, Madl.Switch{}       ) = IM.singleton 0 "INPUTSIZE"
inputDataSize ( nrIns, Madl.Merge{}        ) = IM.fromList $ map (\i -> (i, "INPUTSIZE" +++ showT i)) [0..nrIns-1]
inputDataSize (_nrIns, Madl.Fork{}         ) = IM.singleton 0 "DATASIZE"
inputDataSize ( nrIns, Madl.ControlJoin{}  ) = IM.fromList $ map (\i -> (i, "INPUTSIZE" +++ showT i)) [0..nrIns-1]
inputDataSize (_nrIns, Madl.FControlJoin{} ) = IM.fromList $ [(0, "INPUTSIZE0"), (1, "INPUTSIZE1")]
inputDataSize (_nrIns, Madl.Match{}        ) = IM.fromList $ [(0, "INPUTSIZE0"), (1, "INPUTSIZE1")]
inputDataSize ( nrIns, Madl.MultiMatch{}   ) = IM.fromList $ map (\i -> (i, "INPUTSIZE" +++ showT i)) [0..nrIns-1]
inputDataSize (_nrIns, Madl.LoadBalancer{} ) = IM.singleton 0 "DATASIZE"
inputDataSize (_nrIns, Madl.Joitch{}       ) = IM.fromList $ [(0, "INPUTSIZE0"), (1, "INPUTSIZE1")]
inputDataSize (_nrIns, Madl.Automaton{}    ) = IM.empty
inputDataSize ( nrIns, Madl.GuardQueue{}   ) = IM.fromList $ map (\i -> (i, "INPUTSIZE" +++ showT i)) [0..nrIns-1]

-- | Output datasize parameters of the basic madl comoponents
outputDataSize :: (Madl.XComponent c, Int) -> IntMap VParamName
outputDataSize (Madl.Source{},        _nrOuts) = IM.singleton 0 "DATASIZE"
outputDataSize (Madl.PatientSource{}, _nrOuts) = IM.singleton 0 "DATASIZE"
outputDataSize (Madl.Sink{},          _nrOuts) = IM.empty
outputDataSize (Madl.DeadSink{},      _nrOuts) = IM.empty
outputDataSize (Madl.Function{},      _nrOuts) = IM.empty
outputDataSize (Madl.Queue{},         _nrOuts) = IM.singleton 0 "DATASIZE"
outputDataSize (Madl.Vars{},          _nrOuts) = IM.singleton 0 "DATASIZE"
outputDataSize (Madl.Cut{},           _nrOuts) = IM.singleton 0 "DATASIZE"
outputDataSize (Madl.Switch{},         nrOuts) = IM.fromList $ map (\i -> (i, "OUTPUTSIZE" +++ showT i)) [0..nrOuts-1]
outputDataSize (Madl.Merge{},         _nrOuts) = IM.singleton 0 "OUTPUTSIZE"
outputDataSize (Madl.Fork{},           nrOuts) = IM.fromList $ map (\i -> (i, "DATASIZE")) [0..nrOuts-1]
outputDataSize (Madl.ControlJoin{},   _nrOuts) = IM.singleton 0 "OUTPUTSIZE"
outputDataSize (Madl.FControlJoin{},  _nrOuts) = IM.singleton 0 "OUTPUTSIZE"
outputDataSize (Madl.Match{},         _nrOuts) = IM.fromList $ [(0, "OUTPUTSIZE0"), (1, "OUTPUTSIZE1")]
outputDataSize (Madl.MultiMatch{},     nrOuts) = IM.fromList $ map (\i -> (i, "OUTPUTSIZE" +++ showT i)) [0..nrOuts-1]
outputDataSize (Madl.LoadBalancer{},   nrOuts) = IM.fromList $ map (\i -> (i, "DATASIZE")) [0..nrOuts-1]
outputDataSize (Madl.Joitch{},         nrOuts) = IM.fromList $ map (\i -> (i, "OUTPUTSIZE" +++ showT i)) [0..nrOuts-1]
outputDataSize (Madl.Automaton{},     _nrOuts) = IM.empty
outputDataSize (Madl.GuardQueue{},    _nrOuts) = IM.singleton 0 "OUTPUTSIZE"

-- | Tells whether the basic Madl components make use of the global time
hasTime :: Madl.XComponent c -> Bool
hasTime Madl.Source{}        = True
hasTime Madl.PatientSource{} = True
hasTime Madl.Sink{}          = True
hasTime Madl.DeadSink{}      = True
hasTime Madl.Function{}      = False
hasTime Madl.Queue{}         = False
hasTime Madl.Vars{}          = False
hasTime Madl.Cut{}           = False
hasTime Madl.Switch{}        = False
hasTime Madl.Merge{}         = False
hasTime Madl.Fork{}          = False
hasTime Madl.ControlJoin{}   = False
hasTime Madl.FControlJoin{}  = False
hasTime Madl.Match{}         = False
hasTime Madl.MultiMatch{}    = False
hasTime Madl.LoadBalancer{}  = False
hasTime Madl.Joitch{}        = False
hasTime Madl.Automaton{}     = False
hasTime Madl.GuardQueue{}    = False

-- | Tells whether generated functions make use of the global time
hasTimeFunction :: Bool
hasTimeFunction = False

------------------------------------
-- Arbiter Module characteristics --
------------------------------------

-- | Name of the arbiter module
arbiterModuleName :: Int -> Text
arbiterModuleName = ("arbiter" +++) . showT
-- | Name of an arbiter module client port
arbiterModuleClientPort :: Int -> Text
arbiterModuleClientPort = ("client" +++) . showT
-- | Name of the arbiter module transfer port
arbiterModuleTransferPort :: Text
arbiterModuleTransferPort = "transfer"
-- | Name of the arbiter module selection port
arbiterModuleSelPort :: Text
arbiterModuleSelPort = "sel"

-- | Name of the wire carrying the arbiter output
vSelWire :: Text
vSelWire = "sel"

-------------------------
-- TopLevel Definition --
-------------------------

-- | Auxiliary datatype for readability
type VDefinitionName = Text
-- | Auxiliary datatype for readability, @Left@ for same line, @Right@ for new line
type VDefinitionValue = Either Text Text
-- | Auxiliary datatype for readability
type VDefinitionComment = Text

-- | A toplevel definition consists of a name, a value and a comment to display with the definition
type VDefinition = (VDefinitionName, VDefinitionValue, VDefinitionComment)

-- | Token definition, used in generated functions
vToken :: VDefinition
vToken = ("TOKEN", Left "0", "Constant value to use for data of size 0, since wire size 0 is not possible in verilog")

-- | List of all top level definitions
vDefinitionsList :: [VDefinition]
vDefinitionsList = [vToken]

-- | Verilog code for top level definitions
vDefinitions :: VerilogCode
vDefinitions = concatMap define vDefinitionsList where
    define (name, Left val, comment) = ("// " +++ comment) :
        ["`define " +++ name +++ " " +++ val]
    define (name, Right val, comment) = ("// " +++ comment) :
        ("`define " +++ name +++ " \\") : indent [val]

-- | SVAssertion macro, used for System Verilog assertions on the positive edge of the clock
vAssertClkPos :: VDefinition
vAssertClkPos = (svAssertionPos +++ "(arg)",
    Right $ "assert property (@(posedge " +++ (vinterfaceName vClk)
        +++ ") disable iff (" +++ (vinterfaceName vRst) +++ ") arg)", "Macro for assertion on the positive edge of the clock")

-- | SVAssertion macro, used for System Verilog assertions on the negative edge of the clock
vAssertClkNeg :: VDefinition
vAssertClkNeg = (svAssertionNeg +++ "(arg)",
    Right $ "assert property (@(negedge " +++ (vinterfaceName vClk)
        +++ ") disable iff (" +++ (vinterfaceName vRst) +++ ") arg)", "Macro for assertion on the negative edge of the clock")

-- | SVAssertion macro, used for System Verilog assumptions on the positive edge of the clock
vAssumeClkPos :: VDefinition
vAssumeClkPos = (svAssumptionPos +++ "(arg)",
    Right $ "assume property (@(posedge " +++ (vinterfaceName vClk)
        +++ ") disable iff (" +++ (vinterfaceName vRst) +++ ") arg)", "Macro for assumption on the positive edge of the clock")

-- | SVAssertion macro, used for System Verilog assumptions on the negative edge of the clock
vAssumeClkNeg :: VDefinition
vAssumeClkNeg = (svAssumptionNeg +++ "(arg)",
    Right $ "assume property (@(negedge " +++ (vinterfaceName vClk)
        +++ ") disable iff (" +++ (vinterfaceName vRst) +++ ") arg)", "Macro for assumption on the negative edge of the clock")

-- | List of all top level assertion definitions
vAssertionDefinitionsList :: [VDefinition]
vAssertionDefinitionsList = [vAssertClkPos, vAssertClkNeg, vAssumeClkPos, vAssumeClkNeg]

-- | Verilog code for top level assertion definitions
vAssertionDefinitions :: VerilogCode
vAssertionDefinitions = concatMap define vAssertionDefinitionsList where
    define (name, Left val, comment) = ("// " +++ comment) :
        ["`define " +++ name +++ " " +++ val]
    define (name, Right val, comment) = ("// " +++ comment) :
        ("`define " +++ name +++ " \\") : indent [val]

------------------------------------------------
-- Constants of the Verilog Channel interface --
------------------------------------------------

-- | Modportname based on portDirection and portType
modPortName :: Bool -> Maybe VPortType -> Maybe MPortType -> Text -> Text
modPortName True (Just ptype) (Just dir) name = T.unwords[vChannel +++ T.cons '.' (vPortType ptype .> vDirection dir), esc name]
modPortName True Nothing Nothing name = T.unwords[vChannel, esc name]
modPortName True _ _ _ = fatal 192 "Illegal modport"

modPortName False (Just (Function size)) (Just MInput) name = T.unwords [addSize size $ vDirection MInput, esc $ vData False name]
modPortName False (Just (Function size)) (Just MOutput) name = T.unwords [addSize size $ vDirection MOutput, esc name]
modPortName False (Just (Data size)) (Just dir) name = T.intercalate ", " [
      T.unwords[vDirection dir, esc $ vIrdy False name]
    , T.unwords[addSize size $ vDirection dir, esc $ vData False name]
    , T.unwords[vOtherDirection dir, esc $ vTrdy False name]
    ]
modPortName False (Just Token) (Just dir) name = T.intercalate ", " [
      T.unwords[vDirection dir, esc $ vIrdy False name]
    , T.unwords[vOtherDirection dir, esc $ vTrdy False name]
    ]
modPortName False _ _ _ = fatal 390 "Illegal modport"

-- | Name of the verilog channel interface
vChannel :: Text
vChannel = "chan"

-- | Name of the irdy interface field
vIrdy :: Bool -> Text -> Text
vIrdy True  = (+++ " .irdy")
vIrdy False = (>.    "irdy")
-- | Name of the trdy interface field
vTrdy :: Bool -> Text -> Text
vTrdy True  = (+++ " .trdy")
vTrdy False = (>.    "trdy")
-- | Name of the data interface field
vData :: Bool -> Text -> Text
vData True  = (+++ " .data")
vData False = (>.    "data")

-- | Names associated to portDirections
vDirection :: MPortType -> Text
vDirection MInput = "input"
vDirection MOutput = "output"

-- | Names associated to opposite portDirections
vOtherDirection :: MPortType -> Text
vOtherDirection MInput = vDirection MOutput
vOtherDirection MOutput = vDirection MInput

-- | Names associated to portTypes
vPortType :: VPortType -> Text
vPortType Data{} = "data"
vPortType Token = "token"
vPortType Function{} = "function"

-- | An interface port has a direction, a type, and a name.
data VInterfacePort = VInterfacePort {
    vinterfaceDirection :: Maybe MPortType,
    vinterfaceType :: Either (Maybe (Either Int Text)) (Maybe VPortType), -- (Left wire) or (Right chan)
    vinterfaceName :: Text
} deriving (Show)

-- | Needed wiresize based on type
wireSize :: ColorSet -> Maybe Int
wireSize t = if encSize > 1 then Just encSize else Nothing where
    encSize = encodingSize t

-- | Clock interface port
vClk :: VInterfacePort
vClk = VInterfacePort {
    vinterfaceDirection = Just MInput,
    vinterfaceType = Left Nothing, -- wire of size 1
    vinterfaceName = "clk"
}

-- | Reset interface port
vRst :: VInterfacePort
vRst = VInterfacePort {
    vinterfaceDirection = Just MInput,
    vinterfaceType = Left Nothing, -- wire of size 1
    vinterfaceName = "rst"
}

-- | Time interface port
vTime :: VInterfacePort
vTime = VInterfacePort {
    vinterfaceDirection = Just MInput,
    vinterfaceType = Left (Just $ Left 64), -- wire of size 64
    vinterfaceName = "t"
}

-- | The default interface ports for each module
vDefaultInterface :: Bool -> Bool -> [VInterfacePort]
vDefaultInterface hasrst hastime = [vClk]
    ++ (if hasrst then [vRst] else [])
    ++ (if hastime then [vTime] else [])

-- | Name of the wrapper module
vWrapperModule :: Text
vWrapperModule = "wrapper"

-- | Name of the unbound port
vAssertUnbound :: Text
vAssertUnbound = "unbound"

-------------------------
-- Component Functions --
-------------------------

-- | Selection value
vSelect :: Text -> Text
vSelect = (+++ ("."+++vSelWire))

------------------------
-- Naming Conventions --
------------------------

-- | Naming conventions for modules that have multiple types
vType :: Maybe Int -> Text -> Text
vType Nothing name = name
vType (Just i) name = name >. "type" +++ showT i

-- | Default name for the top wire in generated function components
vTopFunctionName :: Text
vTopFunctionName = "f"

-- | Name prefix for the top wires for each choice in generated switch functions
vMatchSwitchName :: Text
vMatchSwitchName = "match"

-- | Modulename prefix for automaton component modules
vAutomaton :: Text -> Text
vAutomaton compname = "FSM" >. compname

-- | Modulename prefix for function component modules
vFunction :: Text -> Text
vFunction compname = "FUN" >. compname

-- | Prefix for names of generated function instantiations
vFunInstancePrefix :: VFPortType -> Text
vFunInstancePrefix Selection{} = "sfun"
vFunInstancePrefix Output{} = "ofun"

-- | Generated function instantiations names
vFunInstance :: VFPort -> Text -> Text
vFunInstance (_, i, ftype) compname = vFunInstancePrefix ftype .> showT i .> compname

-- | Prefix for names of channels of generated functions
vFunChanPrefix :: VFPortType  -> Text
vFunChanPrefix Selection{} = "sfunchan"
vFunChanPrefix Output{} = "ofunchan"

-- | Generated function channel names
vFunChan :: VFPort -> Text -> Text
vFunChan (_, i, ftype) compname = vFunChanPrefix ftype .> showT i .> compname

-- | Modulename prefix for generated functions
vFunModulePrefix :: VFPortType -> Text
vFunModulePrefix Selection{} = "SFUN"
vFunModulePrefix Output{} = "OFUN"

-- | Generated function module names
vFunModule :: VFPort -> Text -> Text
vFunModule (_, i, ftype) compname = vFunModulePrefix ftype .> showT i >. compname

-- | Names for the input ports of generated functions
vFunInputPort :: Int -> Text
vFunInputPort i = "i" +++ showT i
-- | Names for the output port of generated functions
vFunOutputPort :: Text
vFunOutputPort = "o0"

-- | Name of the type parameter for macro modules
vMacroTypeParam :: Text
vMacroTypeParam = "TYPE"

-- | Name of the module containing SVAs
svAssertionModule :: Text -> Text
svAssertionModule = ("pLib" .>)

-- | Name of the SVAmodule instantiation
svAssertionModuleName :: Text -> Text
svAssertionModuleName = (.> "assertions")

-- | SVAssertion name for assertion on the positive edge of the clock
svAssertionPos :: Text
svAssertionPos = "assert_clk_pos"

-- | SVAssertion name for assertion on the negative edge of the clock
svAssertionNeg :: Text
svAssertionNeg = "assert_clk_neg"

-- | SVAssertion name for assumption on the positive edge of the clock
svAssumptionPos :: Text
svAssumptionPos = "assume_clk_pos"

-- | SVAssertion name for assumption on the negative edge of the clock
svAssumptionNeg :: Text
svAssumptionNeg = "assume_clk_neg"

-- | SVAssertion name for invariant assertions
svAssertionInvariantName :: Int -> Text
svAssertionInvariantName i = "Invariant" .> showT i

-- | SVAssertion name for not full queue assertions
svAssertionNotFullName :: Madl.ComponentID -> Text
svAssertionNotFullName cID = "NotFull" .> showT cID

-- | SVAssertion name for deadlock assertion
svAssertionDeadLockName :: Text
svAssertionDeadLockName = "NoDeadlock"

-- | SVAssertion name for block assertion
svAssertionBlockName :: Text -> Text
svAssertionBlockName = ("NoDeadLockNoEqs" >.)

--------------------------------
-- VerilogCode ::
--------------------------------

-- | A range is defined by a lower bound, and an upper bound. The upper bound is not included.
type Range = (Int, Int)

-- | Add a range to a variable (if needed)
addSize :: Either Int Text -> Text -> Text
addSize (Left  size) name = T.unwords[name, declareRange (src 629) (0, max 1 size)]
addSize (Right size) name = T.unwords[name, "[" +++ size +++ "-1" +++ ":0]"]

-- | Declare a range
declareRange :: (Text, Int) -> Range -> Text
declareRange source (l, h) = if l == h
    then fatal 491 $ "Cannot declare range of size 0. Source: " +++ showT source
    else "[" +++ showT (max (h-1) 0) +++ ":" +++ showT l +++ "]"

-- | Declare a range where the size is given in a textual format
declareTextRange :: Text -> Text
declareTextRange size = "[" +++size +++ "-1:0]"

-- | Escape a variable
esc :: Text -> Text
esc var = if T.head var == '(' then var
    else if T.head var == '\\' && T.last var == ' ' then var
    else if T.head var == '\\' then T.snoc var ' '
    else if T.last var == ' ' then T.cons '\\' var
    else T.cons '\\' $ T.snoc var ' '

-- | Type for verilog code
type VerilogCode = [Text]

-- | Indent a block of verilog code
indent :: VerilogCode -> VerilogCode
indent = map ("  " +++)

-- | Indent a block of verilog code twice
indents :: VerilogCode -> VerilogCode
indents = indent . indent

-- | Postfix verilog style
(>.) :: Text -> Text -> Text
(>.) prefix postfix = prefix +++ "$" +++ postfix