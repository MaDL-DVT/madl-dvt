{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Madl2Verilog.Madl
Description : Conversion of madl network to verilog.
Copyright   : (c) Tessa Belder 2015-2016

Contains functions to transform madl network to verilog code.
-}
module Madl2Verilog.Madl (
    CommandLineOptions(..), defaultOptions,
    Verilog,
    madl2Verilog
) where

import qualified Data.HashMap as Hash
import qualified Data.Map as M
import qualified Data.Text as T

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.Network hiding (macroName)
import Madl2Verilog.VerilogGen
import Madl2Verilog.VerilogConstants hiding (Output)
import Madl2Verilog.Component
import Madl2Verilog.Automaton
import Madl2Verilog.Functions
import Madl2Verilog.Channel
import Madl2Verilog.Macro
import Madl2Verilog.Assertions

import Madl.MsgTypes

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Madl"

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

-- | Commandline options for the madl-to-verilog tool
data CommandLineOptions = CommandLineOptions {
    optTop :: Text, -- ^ Name of the top-level verilog module.
    optOut :: FilePath, -- ^ File to write the verilog code to.
    argNetwork :: Either Text FilePath, -- ^ The network to be converted. Either @Left predefinedNet@, or @Right fileName@.
    argFlatten :: Bool, -- ^ Flatten the specified network before converting to Verilog.
    argTypeCheck :: Bool, -- ^ Typecheck the specified network (deprecated: typechecking should always be performed).
    forceRst :: Bool, -- ^ Don't expose the @rst@ wire in the interface of the top-level module, but force its value to 0 inside the top-level module.
    useInterface :: Bool, -- ^ Use system verilog interfaces to represent madl channels.
    generateLibrary :: Bool, -- ^ Generate a verilog library of madl components (deprecated: this library should always be generated).
    assertionOptions :: AssertionOptions -- ^ System verilog assertions that should be produced.
}

-- | Default commandline options
defaultOptions :: CommandLineOptions
defaultOptions = CommandLineOptions {
    optTop = "top",
    optOut = "out.sv",
    argNetwork = Left "twoagents10",
    argFlatten = False,
    argTypeCheck = True,
    forceRst = False,
    useInterface = False,
    generateLibrary = True,
    assertionOptions = AssertionOptions None None None None None None
}

-- | Data to be converted to Verilog
data Verilog = Verilog {
    componentinfo :: Map ComponentID ComponentInfo,
    macroinstinfo :: [MacroInstanceInfo],
    macroinfo :: Hash.Map Text MacroInfo,
    macros :: [Macro Channel],
    channelinfo :: [ChannelInfo],
    unboundportinfo :: [VInterfacePort],
    commandLineOptions :: CommandLineOptions
}

-----------------------------------------------
-- Functions to derive necessary information --
-----------------------------------------------

-- | Derive data from a Madl Network
madl2Verilog :: MadlNetwork -> CommandLineOptions -> Int -> Text
madl2Verilog madl cmdLine numDataSize = vlog numDataSize netVerilog where
    netVerilog = Verilog {
        componentinfo = deriveComponentInfo (useInterface cmdLine) [] channelTypeMap' numDataSize madl,
        macroinstinfo = deriveMacroInstanceInfo macroinfo' [] madl,
        macroinfo = macroinfo',
        macros = getMacros madl,
        channelinfo = deriveChannelInfo [] channelTypeMap' madl,
        unboundportinfo = deriveTopLevelPortsInfo [] channelTypeMap' madl,
        commandLineOptions = cmdLine
    }

    macroinfo' = deriveMacroInfo madl channelTypeMap'

    (flatNetwork, nameMap) = unfoldMacrosWithNameMap madl
    typedNetwork :: FlatColoredNetwork
    typedNetwork = channelTypes flatNetwork
    typedChannels = getChannels typedNetwork

    channelTypeMap' :: Hash.Map [Text] ColorSet
    channelTypeMap = Hash.fromList $ map (mapFst getName) typedChannels
    channelTypeMap' = Hash.foldWithKey (\k v m -> Hash.insert k (lookupM (src 138) v m) m) channelTypeMap nameMap

-----------------------------------
-- Functions to generate Verilog --
-----------------------------------

-- | Generate complete Verilog code from Verilog Data
vlog :: Int -> Verilog -> Text
vlog numDataSize v = T.unlines $
           commentHeader "Top Level Definitions" vDefinitions
        ++ commentHeader "Macro modules" declareMacros
        ++ commentHeader "Top level finite state machines" declareAutomatonComponents
        ++ commentHeader "Top level function components" declareFunctionComponents
        ++ commentHeader "Top level switch functions" declareOtherFunctions
        ++ commentHeader "Top level module" (declareModule useinterface topModule)
        ++ (if hasassertions then commentHeader "Assertion-module binding" $ bindModule useinterface assertionBinding else [])
        ++ (if hasWrapper then commentHeader "Wrapper module" $ declareModule useinterface wrapperModule else []) where
    declareMacros = concatMap (declareMacro useinterface . macro2VMacro useinterface numDataSize (macroinfo v)) $ macros v

    declareAutomatonComponents = concatMap (declareAutomatonComponent useinterface Nothing) automata
    automata = filter (isAutomaton . compComponent) (M.elems $ componentinfo v)

    declareFunctionComponents = concatMap (declareFunctionComponent useinterface Nothing) functions
    functions = filter (isFunction . compComponent) (M.elems $ componentinfo v)

    declareOtherFunctions = concatMap (declareFunctions useinterface Nothing) $ componentinfo v

    topModule = VModule {
        vmoduleName = optTop (commandLineOptions v),
        vmoduleParams = [],
        vmoduleHasTime = True,
        vmoduleHasRst = True,
        vmoduleInterface = unboundInterfacePorts,
        vmoduleBody =
               commentHeader "Channel declarations" networkChannels
            ++ commentHeader "Function Channels" functionChannels
            ++ commentHeader "Component and Macro instantiations" (
                       instantiateComponents
                    ++ instantiateMacros
                )
    }

    hasWrapper = forceRst $ commandLineOptions v
    wrapperModule = VModule {
        vmoduleName = vWrapperModule,
        vmoduleParams = [],
        vmoduleHasTime = True,
        vmoduleHasRst = not $ forceRst $ commandLineOptions v,
        vmoduleInterface = unboundInterfacePorts,
        vmoduleBody =
               (if (forceRst $ commandLineOptions v) then declareWire (vinterfaceName vRst) "1'b 0" else [])
            ++ instantiateModule useinterface topInstance
    }

    assertionBinding = VBindModule {
        vbindTargetModule = optTop (commandLineOptions v),
        vbindTargetPrimitive = False,
        vbindModule = svAssertionModule $ optTop (commandLineOptions v),
        vbindPrimitive = False,
        vbindModuleName = svAssertionModuleName $ optTop (commandLineOptions v),
        vbindHasTime = False,
        vbindHasRst = True,
        vbindInterface = []
    }

    topInstance = VModuleInstance {
        vinstanceModule = optTop (commandLineOptions v),
        vinstancePrimitive = False,
        vinstanceName = optTop (commandLineOptions v),
        vinstanceParams = [],
        vinstanceHasTime = True,
        vinstanceHasRst = True,
        vinstanceInterface = map ((\x -> (x, x, SingleChannel)) . vinterfaceName) unboundInterfacePorts
    }

    unboundInterfacePorts = unboundportinfo v

    networkChannels = concatMap (declareChannelFromInfo useinterface) $ channelinfo v
    functionChannels = concatMap (declareFunctionChannels useinterface) $ componentinfo v

    instantiateComponents = concatMap (instantiateComponent useinterface Nothing) $ componentinfo v
    instantiateMacros = concatMap (instantiateMacro useinterface) $ macroinstinfo v

    useinterface = useInterface $ commandLineOptions v
    hasassertions = hasAssertions . assertionOptions $ commandLineOptions v