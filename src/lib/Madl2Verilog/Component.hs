{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

{-|
Module      : Madl2Verilog.Component
Description : Conversion of MaDL components to System Verilog.
Copyright   : (c) 2015-2017 Eindhoven University of Technology
Authors     : Tessa Belder 2015-2016

Contains functions to transform madl components to verilog code.
-}
module Madl2Verilog.Component (
    ComponentInfo(..),
    deriveComponentInfo,
    deriveTopLevelPortsInfo,
    instantiateComponent,
    declareFunctionChannels,
    topInterfacePort,
    hasTimeFromInfo
) where

import qualified Data.HashMap as Hash
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import qualified Data.Text as T

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes
import Madl.Network hiding (XComponent(..), macroName)
import qualified Madl.Network as Madl (XComponent(..))

import Madl2Verilog.VerilogConstants
import Madl2Verilog.VerilogGen

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Component"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

----------------
-- Data Types --
----------------

-- | All component information necessary to generate verilog
data ComponentInfo = ComponentInfo {
    compIdentifier :: [Text],
    compComponent :: Component,
    compPorts :: [(VPortName, VChannelName, VChannelType)],
    compUnboundPorts :: [(VPortName, VChannelName, VChannelType)],
    compTopLevelOutPorts :: [(VPortName, VChannelName)],
    compInputTypes :: [ColorSet],
    compOutputTypes :: [ColorSet],
    compParams :: [VParameter]
} deriving (Show)

-----------------------------------------------
-- Functions to derive necessary information --
-----------------------------------------------

-- | Derive all component information necessary to generate verilog
deriveComponentInfo :: IMadlNetwork n  => Bool -> [Text] -> Hash.Map [Text] ColorSet -> Int -> TMadlNetwork n -> Map ComponentID ComponentInfo
deriveComponentInfo useInterface prefix channelTypesMap numDataSize network  = M.fromList
        [(a, getInfo a c) | (a, C c) <- getComponentsWithID network] where
    getInfo :: ComponentID -> Component -> ComponentInfo
    getInfo node comp = ComponentInfo {
        compIdentifier = compIdentifier',
        compComponent = comp,
        compPorts = compPorts',
        compUnboundPorts = compUnboundPorts',
        compTopLevelOutPorts = compTopLevelOutPorts',
        compInputTypes = compInputTypes',
        compOutputTypes = compOutputTypes',
        compParams = compParams'
    } where

        compInputTypes' = map (lookupM' (src 86) channelTypesMap) inputChannelNames

        inputChannelNames = map ((prefix ++) . getNameList . (getChannel network)) inChannels
        inChannels = getInChannels network node
        compOutputTypes' = map (lookupM' (src 90) channelTypesMap) outputChannelNames
        outputChannelNames = map ((prefix ++) . getNameList . (getChannel network)) outChannels
        outChannels = getOutChannels network node

        compIdentifier' = getNameList comp
        compPorts'= map (\(v, c) -> (v, c, MadlBus)) (inports ++ outports) ++ funports
        compUnboundPorts' = map (unboundport . fst) (unboundInputPorts comp)
        compTopLevelOutPorts' = map (topleveloutput) (topLevelOutputPorts comp)

        inports, outports :: [(VPortName, VChannelName)]
        inports = zip (inputPorts (length inChannels, comp)) (map (getName . getChannel network) inChannels)
        outports = zip (outputPorts (comp, length outChannels)) (map (getName . getChannel network) outChannels)
        funports, funOutputPorts :: [(VPortName, VChannelName, VChannelType)]
        funports = map funport (functionInputPorts (length inChannels, comp, length outChannels)) ++ funOutputPorts
        funport p = (fst3 p, vFunChan p (getName comp), MadlData)

        funOutputPorts = [(pname, pname .> (getName comp), SingleChannel) | (_, (pname, _)) <- functionOutputPorts (length inChannels, comp, length outChannels)]

        unboundport pname = (pname, T.intercalate "$" compIdentifier' >. pname, SingleChannel)
        topleveloutput (pname, target) = (T.intercalate "$" compIdentifier' >. pname, targetchan) where
            targetchan = case target of
                XIrdy i -> esc . vIrdy useInterface $ snd (lookupM (src 104) i inports :: (VPortName, VChannelName))
                XData i -> esc . vData useInterface $ snd (lookupM (src 105) i inports :: (VPortName, VChannelName))
                XTrdy i -> esc . vTrdy useInterface $ snd (lookupM (src 106) i outports :: (VPortName, VChannelName))

        compParams' = [(pname, value_fun comp) | (pname, value_fun) <- parameters numDataSize comp] ++
            [(paramname, datasize madlport) | (madlport, paramname) <- datasizeParameters useInterface (length inChannels, comp, length outChannels)]

        datasize :: MadlPort -> Text
        datasize (portindex, portdirection) = case portdirection of
            MInput -> showT . max 1 . encodingSize $ lookupM (src 108) portindex compInputTypes'
            MOutput -> showT . max 1 . encodingSize $ lookupM (src 109) portindex compOutputTypes'

-- | Get all ports that should be declared in the interface of the toplevel module
deriveTopLevelPortsInfo :: IMadlNetwork n  => [Text] -> Hash.Map [Text] ColorSet -> TMadlNetwork n -> [VInterfacePort]
deriveTopLevelPortsInfo prefix channelTypesMap network = concatMap (uncurry getInfo) (getComponentsWithID network) where
    getInfo node (C comp) = map toInputPort (unboundInputPorts comp) ++ map toOutputPort (topLevelOutputPorts comp) where
        toInputPort (name, target) = VInterfacePort (Just MInput) (Left size) (T.intercalate "$" namelist >. name) where
            size = case target of XIrdy{} -> Nothing; XTrdy{} -> Nothing; XData i -> Just . Left $ outputsize i;
        toOutputPort (name, target) = VInterfacePort (Just MOutput) (Left size) (T.intercalate "$" namelist >. name) where
            size = case target of XIrdy{} -> Nothing; XTrdy{} -> Nothing; XData i -> Just . Left $ inputsize i;
        namelist = prefix ++ getNameList comp
        inputsize i = max 1 . encodingSize $ lookupM (src 124) (prefix ++ [getName $ input i]) channelTypesMap
        input i = getChannel network . lookupM (src 125) i $ getInChannels network node
        outputsize i = max 1 . encodingSize $ lookupM (src 115) (prefix ++ [getName $ output i]) channelTypesMap
        output i = getChannel network . lookupM (src 117) i $ getOutChannels network node
    getInfo _ (M (MacroInstance name macro)) = deriveTopLevelPortsInfo (prefix ++ [name]) channelTypesMap (macroNetwork macro)

-----------------------------------
-- Functions to generate Verilog --
-----------------------------------

-- | Instantiate component
instantiateComponent :: Bool -> Maybe (Text, Maybe Int) -> ComponentInfo -> VerilogCode
instantiateComponent useInterface macroName comp =
           concatMap (uncurry assignWire) (compTopLevelOutPorts comp)
        ++ instantiateModule useInterface componentInstance
        ++ componentFunctionInstantiations where
    componentInstance = VModuleInstance {
        vinstanceModule = compModule,
        vinstancePrimitive = True,
        vinstanceName = compName,
        vinstanceParams = compParams comp,
        vinstanceHasTime = hasTimeFromInfo comp,
        vinstanceHasRst = True,
        vinstanceInterface = compPorts comp ++ compUnboundPorts comp
    }
    compName = T.intercalate "_" $ compIdentifier comp
    compModule = case compComponent comp of
        Madl.Function{} -> case macroName of
            Nothing -> vFunction compName
            Just (name, mtype) -> vFunction . vType mtype $ (name .> compName)
        Madl.Automaton{} -> case macroName of
            Nothing -> vAutomaton compName
            Just (name, mtype) -> vAutomaton . vType mtype $ (name .> compName)
        _ -> moduleName (nrInChannels, compComponent comp, nrOutChannels)

    componentFunctionInstantiations = concatMap (instantiateModule useInterface . componentFunctionInstance) $
        functionInputPorts (nrInChannels, compComponent comp, nrOutChannels)

    nrInChannels = length $ compInputTypes comp
    nrOutChannels = length $ compOutputTypes comp

    componentFunctionInstance :: VFPort -> VModuleInstance
    componentFunctionInstance p@(_, fnr, _) =
        VModuleInstance {
            vinstanceModule = vinstanceModule',
            vinstancePrimitive = False,
            vinstanceName = vFunInstance p compName,
            vinstanceParams = [],
            vinstanceHasTime = hasTimeFunction,
            vinstanceHasRst = True,
            vinstanceInterface = inports ++ outports
        } where
            vinstanceModule' = case macroName of
                Nothing -> vFunModule p compName
                Just (name, mtype) -> vFunModule p . vType mtype $ (name .> compName)

            inports, outports :: [(VPortName, VChannelName, VChannelType)]
            inports = (map (\(i, (_, chan, _)) -> (vFunInputPort i, chan, MadlData)) $ zip [0..nrInChannels-1] (compPorts comp))
                ++ (mapMaybe (\(i, (n, _)) -> if i == fnr then Just (n, n .> compName, SingleChannel) else Nothing) (functionOutputPorts (nrInChannels, compComponent comp, nrOutChannels)))
            outports = [(vFunOutputPort, vData useInterface $ vFunChan p compName, SingleChannel)]

-- | Declare channels between a components and its function
declareFunctionChannels :: Bool -> ComponentInfo -> VerilogCode
declareFunctionChannels useInterface comp = functionChannels where
    functionOutputChannels = map (functionOutputChannel . snd) $ functionOutputPorts (nrInChannels, compComponent comp, nrOutChannels)
    functionOutputChannel :: (Text, ColorSet) -> Text
    functionOutputChannel (n, t) = declareChannel False (encodingSize t) (n .> compName)

    nrInChannels = length $ compInputTypes comp
    nrOutChannels = length $ compOutputTypes comp

    compName = T.intercalate "_" $ compIdentifier comp
    chanName :: VFPort -> Text
    chanName = flip vFunChan compName
    functionChannels :: [Text]
    functionChannels = concatMap functionChannel (functionInputPorts (nrInChannels, compComponent comp, nrOutChannels)) ++ functionOutputChannels
    functionChannel :: VFPort -> VerilogCode
    functionChannel p@(_, _, ftype) = [declareChannel useInterface dataSize . vData useInterface $ chanName p] where
        dataSize = case ftype of
            Output i -> encodingSize $ lookupM (src 182) i (compOutputTypes comp)
            Selection cs -> encodingSize cs

-- | Declare portname for converted IO component
topInterfacePort :: (MPortType, Int) -> Text -> VInterfacePort
topInterfacePort (dir, size) name = VInterfacePort {
    vinterfaceDirection = Just dir,
    vinterfaceType = Right (Just . Data $ Left size),
    vinterfaceName = name
}

-------------------------
-- Auxiliary functions --
-------------------------

-- | True if the specified MaDL component can make use of the global "t" (time tick) internally
hasTimeFromInfo :: ComponentInfo -> Bool
hasTimeFromInfo compInfo = hasTime $ compComponent compInfo