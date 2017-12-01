{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

{-|
Module      : Madl2Verilog.Macro
Description : Conversion of madl macro to verilog.
Copyright   : (c) Tessa Belder 2015-2016

Contains functions to transform madl macros to verilog code.
-}
module Madl2Verilog.Macro (
    MacroInfo, MacroInstanceInfo,
    deriveMacroInfo,
    deriveMacroInstanceInfo,
    macro2VMacro,
    declareMacro,
    instantiateMacro
) where

-- import Debug.Trace

import Data.Function (on)
import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM
import Data.List (sortBy, groupBy, isPrefixOf)
import qualified Data.Map as M
import Data.Maybe
import Data.Ord (comparing)
import qualified Data.Text as T

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.Network hiding (macroName, inputTypes, instanceName)
import qualified Madl.Network as Madl (macroName)
import Madl.MsgTypes

import Madl2Verilog.VerilogConstants
import Madl2Verilog.VerilogGen
import Madl2Verilog.Automaton
import Madl2Verilog.Component
import Madl2Verilog.Channel
import Madl2Verilog.Functions

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Macros"

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

-- | Macrodata to be converted to Verilog
data VMacro = VMacro {
    vmacroName :: Text,
    vmacroHastime :: Bool,
    vmacroComponentinfo :: IntMap (Map ComponentID ComponentInfo),
    vmacroMacroinstinfo :: IntMap ([MacroInstanceInfo]),
    vmacroChannelinfo :: IntMap ([ChannelInfo]),
    vmacroPorts :: IntMap [(Text, ColorSet, MPortType)], --[Text]
    vmacroUnboundPorts :: [VInterfacePort],
    vmacroTypes :: [Int],
    vmacroParams :: [VParameter]
}

-- | All macro info necessary to compute MacroInstanceInfo
data MacroInfo = MacroInfo {
    macroName :: Text,
    macroHastime :: Bool,
    macroInputPorts :: IntMap [(VPortName, ColorSet)],
    macroOutputPorts :: IntMap [(VPortName, ColorSet)],
    macroUnboundPorts :: [VInterfacePort],
    macroInputTypes :: IntMap [Text],
    macroInstanceTypes :: Hash.Map [Text] Int,
    macroParams :: [VParameter],
    globalChannelTypes :: Hash.Map [Text] ColorSet
} deriving (Show)

-- | All macro instance information necessary to generate verilog
data MacroInstanceInfo = MacroInstanceInfo {
    macroinstIdentifier :: [Text],
    macroinstMacro :: MacroInfo,
    macroinstPorts :: [(VPortName, VChannelName, VChannelType)],
    macroinstParams :: [VParameter],
    macroinstType :: Maybe Int -- TODO(tssb) : remove once you know how to deal with assertions
} deriving (Show)

-----------------------------------------------
-- Functions to derive necessary information --
-----------------------------------------------

-- | Derive all macro information necessary to compute MacroInstanceInfo
deriveMacroInfo :: MadlNetwork -> Hash.Map [Text] ColorSet -> Hash.Map Text MacroInfo
deriveMacroInfo network channelTypeMap = Hash.fromList [(getName macro, getInfo macro) | macro <- getMacros network] where
    getInfo :: Macro Channel -> MacroInfo
    getInfo macro' = MacroInfo {
        macroName = macroName',
        macroHastime = hasTimeM macro',
        macroInputPorts = macroInputPorts',
        macroOutputPorts = macroOutputPorts',
        macroUnboundPorts = macroUnboundPorts',
        macroInputTypes = macroInputTypes',
        macroInstanceTypes = macroInstanceTypes',
        macroParams = macroParams',
        globalChannelTypes = channelTypeMap
    } where
        macroName' = getName macro'
        mNet = macroNetwork macro'
        (inInterface, outInterface) = splitInterface macro'
        macroInputPorts', macroOutputPorts' :: IntMap [(Text, ColorSet)]
        macroInputPorts' = IM.fromList $ [(i, zip macroInputPortNames inTypes) | (i, list) <- typeGroups, let (inTypes, _, _) = head list]
        macroOutputPorts' = IM.fromList $ [(i, zip macroOutputPortNames outTypes) | (i, list) <- typeGroups, let (_, outTypes, _) = head list]
        macroInputPortNames = map (getName . getChannel mNet) inInterface
        macroOutputPortNames = map (getName . getChannel mNet) outInterface

        macroUnboundPorts' = deriveTopLevelPortsInfo [] mChannelTypeMap mNet
        mChannelTypeMap = Hash.fromList . map (mapFst $ drop $ length representative) . filter (isPrefixOf representative . fst) $ Hash.toList channelTypeMap
        representative = head macroInstances

        macroInstances :: [[Text]]
        macroInstances = getMacroInstances network macroName'

        macroInputTypes'= IM.fromList $ [(i, name) | (i, list) <- typeGroups, let (_, _, name) = head list]
        macroInstanceTypes' = Hash.fromList $ [(name, i) | (i, list) <- typeGroups, (_, _, name) <- list]
        typeGroups :: [(Int, [([ColorSet], [ColorSet], [Text])])]
        typeGroups = zip [0..] $ groupBy ((==) `on` fst3) $ sortBy (comparing fst3) $ inputTypes
        inputTypes :: [([ColorSet], [ColorSet], [Text])]
        inputTypes = [(map (channelType name) macroInputPortNames, map (channelType name) macroOutputPortNames, name) | name <- macroInstances]
        channelType :: [Text] -> Text -> ColorSet
        channelType instanceName chanName = lookupM (src 146) (instanceName ++ [chanName]) channelTypeMap

        macroParams' = [("TYPE", "0")]


-- | Derive all macro instance information necessary to generate verilog
deriveMacroInstanceInfo :: IMadlNetwork n => Hash.Map Text MacroInfo -> [Text] -> TMadlNetwork n -> [MacroInstanceInfo]
deriveMacroInstanceInfo macroMap prefix network = [ getInfo a m | (a, M m) <- getComponentsWithID network] where
    getInfo :: ComponentID -> MacroInstance Channel -> MacroInstanceInfo
    getInfo node macroinst = MacroInstanceInfo {
        macroinstIdentifier = macroinstIdentifier',
        macroinstMacro = macroinstMacro',
        macroinstPorts = inports ++ outports ++ unboundports,
        macroinstParams = macroinstParams'', -- TODO(tssb) : change back to macroinstParams' once you know how to deal with assertions
        macroinstType = if multipleTypes then Just macroType else Nothing -- todo(tssb): remove once you know how to deal with assertions
    } where
        macroinstIdentifier' = getNameList macroinst
        macroinstMacro' = lookupM (src 162) ((getName $ instanceMacro macroinst)::Text) macroMap

        multipleTypes = IM.size (macroInputTypes macroinstMacro') > 1
        _macroinstParams' = if multipleTypes then [(vMacroTypeParam, showT macroType)] else []
        macroinstParams'' = []
        macroType :: Int
        macroType = lookupM (src 167) prefix' (macroInstanceTypes macroinstMacro')

        prefix' = prefix ++ macroinstIdentifier'

        inports, outports, unboundports :: [(VPortName, VChannelName, VChannelType)]
        inports = zip3 macroInPorts inchans (repeat MadlBus)
        outports = zip3 macroOutPorts outchans (repeat MadlBus)
        unboundports = map ((\n -> (n, T.intercalate "$" macroinstIdentifier' >. n, SingleChannel)) . vinterfaceName) $ macroUnboundPorts macroinstMacro'

        macroInPorts, macroOutPorts :: [VPortName]
        macroInPorts = map fst (lookupM (src 177) macroType (macroInputPorts macroinstMacro') :: [(VPortName, ColorSet)])
        macroOutPorts = map fst (lookupM (src 177) macroType (macroOutputPorts macroinstMacro') :: [(VPortName, ColorSet)])
        inchans, outchans :: [VChannelName]
        inchans = map (getName . getChannel network) $ getInChannels network node
        outchans = map (getName . getChannel network) $ getOutChannels network node

-- | Derive data from a Madl macro
macro2VMacro :: Bool -> Int -> Hash.Map Text MacroInfo -> Macro Channel-> VMacro
macro2VMacro useInterface numDataSize macroinfo macro = VMacro {
        vmacroName = vmacroName',
        vmacroComponentinfo = vmacroComponentinfo',
        vmacroMacroinstinfo = vMacroinstinfo',
        vmacroChannelinfo = vmacroChannelinfo',
        vmacroHastime = hasTimeM macro,
        vmacroPorts = vmacroPorts',
        vmacroUnboundPorts = macroUnboundPorts macroinfo',
        vmacroTypes = IM.keys macrotypes,
        vmacroParams = macroParams macroinfo'
    } where
        vmacroName' = getName macro
        network = macroNetwork macro
        vmacroComponentinfo' = fmap (\prefix -> deriveComponentInfo useInterface prefix chantypes numDataSize network) macrotypes
        vMacroinstinfo' = fmap (\prefix -> deriveMacroInstanceInfo macroinfo prefix network) macrotypes
        macroinfo' = lookupM (src 200) vmacroName' macroinfo
        macrotypes = macroInputTypes macroinfo'
        vmacroChannelinfo' = fmap (\prefix -> deriveChannelInfo prefix chantypes network) macrotypes
        chantypes = globalChannelTypes macroinfo'
        vmacroPorts' = IM.unionWith (++)
            (fmap (map $ \(n, t) -> (n, t, MInput))  $ macroInputPorts  macroinfo')
            (fmap (map $ \(n, t) -> (n, t, MOutput)) $ macroOutputPorts macroinfo')


-----------------------------------
-- Functions to generate Verilog --
-----------------------------------

-- | Declare top macro module
declareMacro :: Bool -> VMacro -> VerilogCode
declareMacro useInterface macro =
       (if multipleTypes then [] else declareModule useInterface macroModule) -- TODO(tssb) : Remove if-then-else once you know how to deal with assertions
    ++ auxiliaryModules where
    macroModule = VModule {
        vmoduleName = vmacroName macro,
        vmoduleParams = macroParameters,
        vmoduleHasTime = vmacroHastime macro,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface' ++ vmacroUnboundPorts macro,
        vmoduleBody = macroBody
    }
    macroParameters = if multipleTypes
        then vmacroParams macro
        else []
    vmoduleInterface' = map createInterfacePort (head . IM.elems $ vmacroPorts macro) where
        createInterfacePort (n, t, d) = if useInterface
        then VInterfacePort Nothing (Right Nothing) n
        else VInterfacePort (Just d) (Right . Just . Data . Left $ encodingSize t) n

    multipleTypes = length (vmacroTypes macro) > 1

    macroBody = if multipleTypes
        then caseDistinction
        else declareMacroBody useInterface macro Nothing
    caseDistinction = ["","case (" +++ vMacroTypeParam +++ ")"] -- TODO(tssb): Clean code generation
        ++ indent (map instantiateMacroType (vmacroTypes macro))
        ++ ["endcase", ""]
    instantiateMacroType :: Int -> Text
    instantiateMacroType i = showT i +++ " : "
        +++ esc (vmacroName macro >. "type" +++ showT i) +++ "macro("
        +++ ".\\clk (\\clk ), .\\rst (\\rst )" +++ (if vmacroHastime macro then ", .\\t (\\t )" else "")
        +++ T.concat (map declarePort (map fst3 . head . IM.elems $ vmacroPorts macro))  +++  ");"
    declarePort :: Text -> Text
    declarePort n = T.concat . map (", " +++) $ instantiatePort useInterface False (n, n, MadlBus)

    auxiliaryModules = if multipleTypes
        then declareMacroTypes
        else declareAuxiliaryModules useInterface macro Nothing
    declareMacroTypes = concatMap (declareMacroType useInterface macro) $ vmacroTypes macro

-- | Declare macro module for a specific type
declareMacroType :: Bool -> VMacro -> Int -> VerilogCode
declareMacroType useInterface macro mtype =
       declareModule useInterface macroModule
    ++ declareAuxiliaryModules useInterface macro (Just mtype) where
    macroModule = VModule {
        vmoduleName = vType (Just mtype) (vmacroName macro),
        vmoduleParams = [],
        vmoduleHasTime = vmacroHastime macro,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface' ++ vmacroUnboundPorts macro,
        vmoduleBody = declareMacroBody useInterface macro (Just mtype)
    }
    vmoduleInterface' = map createInterfacePort (lookupM (src 250) mtype $ vmacroPorts macro) where
        createInterfacePort (n, t, d) = if useInterface
        then VInterfacePort Nothing (Right Nothing) n
        else VInterfacePort (Just d) (Right . Just . Data . Left $ encodingSize t) n

-- | Declare macro module body for a specific type
declareMacroBody :: Bool -> VMacro -> Maybe Int -> VerilogCode
declareMacroBody useInterface macro mtype =
       commentHeader "Channel declarations" networkChannels
    ++ commentHeader "Function Channels" functionChannels
    ++ commentHeader "Component and Macro instantiations" (
               instantiateComponents
            ++ instantiateMacros
            ) where
    vmacroChannels :: [ChannelInfo]
    vmacroChannels = lookupM (src 208) (fromMaybe 0 mtype) (vmacroChannelinfo macro)
    vmacroComponents :: Map ComponentID ComponentInfo
    vmacroComponents = lookupM (src 280) (fromMaybe 0 mtype) (vmacroComponentinfo macro)
    vmacroMacroInstances :: [MacroInstanceInfo]
    vmacroMacroInstances = lookupM (src 283) (fromMaybe 0 mtype) (vmacroMacroinstinfo macro)

    networkChannels = concatMap (declareChannelFromInfo useInterface) vmacroChannels
    functionChannels = concatMap (declareFunctionChannels useInterface) vmacroComponents
    instantiateComponents = concatMap (instantiateComponent useInterface $ Just (vmacroName macro, mtype)) vmacroComponents
    instantiateMacros = concatMap (instantiateMacro useInterface) vmacroMacroInstances

-- | Declare auxiliary modules ( (switch)functions ) for a specific type
declareAuxiliaryModules :: Bool -> VMacro -> Maybe Int -> VerilogCode
declareAuxiliaryModules useInterface macro mtype =
       commentHeader (modulename +++ " finite state machines") declareAutomatonComponents
    ++ commentHeader (modulename +++ " function components") declareFunctionComponents
    ++ commentHeader (modulename +++ " switch functions") declareOtherFunctions where
    modulename = vmacroName macro
    vmacroComponents :: Map ComponentID ComponentInfo
    vmacroComponents = lookupM (src 295) (fromMaybe 0 mtype) (vmacroComponentinfo macro)
    automata = filter (isAutomaton . compComponent) (M.elems vmacroComponents)
    functions = filter (isFunction . compComponent) (M.elems vmacroComponents)

    declareAutomatonComponents = concatMap (declareAutomatonComponent useInterface mtype . prefixName) automata
    declareFunctionComponents = concatMap (declareFunctionComponent useInterface mtype . prefixName) functions
    declareOtherFunctions = concatMap (declareFunctions useInterface mtype . prefixName) vmacroComponents

    prefixName :: ComponentInfo -> ComponentInfo
    prefixName cinfo = cinfo{compIdentifier = modulename : compIdentifier cinfo}

-- | Instantiate macro
instantiateMacro :: Bool -> MacroInstanceInfo -> VerilogCode
instantiateMacro useInterface macroinst = instantiateModule useInterface macroInstance where
    macroInstance = VModuleInstance {
        vinstanceModule = vinstanceModule', -- TODO(tssb) : change back to (macroName macro) once you know how to deal with assertions
        vinstancePrimitive = False,
        vinstanceName = T.intercalate "_" $ macroinstIdentifier macroinst,
        vinstanceParams = macroinstParams macroinst,
        vinstanceHasTime = macroHastime macro,
        vinstanceHasRst = True,
        vinstanceInterface = macroinstPorts macroinst
    }
    vinstanceModule' = case macroinstType macroinst of
        Nothing -> macroName macro
        Just i -> (macroName macro) >. ("type" +++ showT i)
    macro = macroinstMacro macroinst

-------------------------
-- Auxiliary functions --
-------------------------

-- | True if the specified macro can make use of the global "t" (time tick) internally
hasTimeM :: Macro Channel -> Bool
hasTimeM = hasTimeM' [] where
    hasTimeM' :: [Text] -> Macro Channel -> Bool
    hasTimeM' list macro = if Madl.macroName macro `elem` list then False
        else or [hasTime comp | (C comp) <- macro_comps] ||
             or [hasTimeM' newList $ instanceMacro macro' | (M macro') <- macro_comps] where
            macro_comps = getComponents $ macroNetwork macro
            newList = Madl.macroName macro : list