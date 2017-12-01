{-# LANGUAGE CPP, OverloadedStrings #-}

module Main (main) where

import System.Console.GetOpt

import qualified Data.HashMap as Hash
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Utils.Executable
import Utils.File
import Utils.Text

import Examples

import Madl.Network

import Madl2Verilog.Library
import Madl2Verilog.Madl
import Madl2Verilog.Assertions

-- | CommandLine options
exeOptions :: [OptDescr (CommandLineOptions -> CommandLineOptions)]
exeOptions =
    [ Option "t" ["top"]
        (ReqArg (\t opts -> opts {optTop = txt t}) "TOPMODULE")
        "Top level Verilog module name (default is 'top')."
    , Option "o" ["out"]
        (ReqArg (\o opts -> opts {optOut = o}) "OUTFILE")
        "System Verilog output file name (default is 'out.sv').\n"

    , Option "x" []
        (ReqArg (\x opts -> opts {argNetwork = Left $ txt x}) "MaDLNETWORK")
        "MaDL network name (default is 'twoagents10')."
    , Option "f" ["network"]
        (ReqArg (\x opts -> opts {argNetwork = Right x}) "MaDLFILE")
        "MaDL file name.\n"

    , Option "" ["flatten"]
        (NoArg (\opts -> opts {argFlatten = True}))
        "Flatten (unfold all macro instances) the MaDL network before converting to verilog."
    , Option "" ["no-typecheck"]
        (NoArg (\opts -> opts {argTypeCheck = False}))
        "Don't typecheck the given MaDL file.\n"

    , Option "i" ["invariantAssertions"]
        (OptArg (\mode opts -> opts {assertionOptions = (assertionOptions opts) {invariantAssertions =
            case mode of Just "assume" -> Assume; _ -> Assert}}) "AssertionMode")
        "Produce SystemVerilog Assertions from invariants. AssertionMode: assert = Assert (default), assume = Assume."
    , Option "d" ["deadlockAssertions"]
        (OptArg (\mode opts -> opts {assertionOptions = (assertionOptions opts) {deadlockAssertions =
            case mode of Just "assume" -> Assume; _ -> Assert}}) "AssertionMode")
        "Produce SystemVerilog Assertions from deadlock equations. AssertionMode: assert = Assert (default), assume = Assume."
    , Option "q" ["quick"]
        (OptArg (\mode opts -> opts {assertionOptions = (assertionOptions opts) {naiveAssertions =
            case mode of Just "assume" -> Assume; _ -> Assert}}) "AssertionMode")
        "Produce SystemVerilog Assertions from naive deadlock properties for each source. AssertionMode: assert = Assert (default), assume = Assume."
    , Option "" ["notFullAssertions"]
        (OptArg (\mode opts -> opts {assertionOptions = (assertionOptions opts) {notFullAssertions =
            case mode of Just "assume" -> Assume; _ -> Assert}}) "AssertionMode")
        "Produce SystemVerilog Assertions for queues that cannot be full. AssertionMode: assert = Assert (default), assume = Assume."
    , Option "l" ["liveSourceAssertions"]
        (OptArg (\mode opts -> opts {assertionOptions = (assertionOptions opts) {liveSourceAssertions =
            case mode of Just "assume" -> Assume; _ -> Assert}}) "AssertionMode")
        "Produce SystemVerilog Assertions to verify liveness of sources. AssertionMode: assert = Assert (default), assume = Assume. (not supported)"
    , Option "p" ["persistentChannelAssertions"]
        (OptArg (\mode opts -> opts {assertionOptions = (assertionOptions opts) {persistentChannelAssertions =
            case mode of Just "assume" -> Assume; _ -> Assert}}) "AssertionMode")
        "Produces SystemVerilog Assertions to verify channel persistancy. AssertionMode: assert = Assert (default), assume = Assume. (not supported)\n"

    , Option "" ["force-rst"]
        (NoArg (\opts -> opts {forceRst = True}))
        "Removes the rst wire from the wrapper interface and sets its value to 0."
    , Option "" ["use-interface"]
        (NoArg (\opts -> opts {useInterface = True}))
        "Use SystemVerilog interfaces to group the irdy, trdy and data wires of a MaDL channel."
    ]

-- | Main entry point
main :: IO ()
main = do
    cmdLine <- parseArgs exeOptions defaultOptions
    network <- case argNetwork cmdLine of
        Left netname -> case Hash.lookup netname networkMap of
            Nothing -> ioError . userError $ "Unknown network " ++ utxt netname ++ ", pick one of: " ++ show (Hash.keys Examples.networkMap)
            Just net -> return net -- Assume that all predefined networks are valid.
        Right filename -> do
            networkOrError <- readNetworkFromFile defaultReadOptions{readTypeCheck = argTypeCheck cmdLine} filename
            case networkOrError of
                Left err -> ioError $ userError err
                Right net -> return net
    let network' = if argFlatten cmdLine then removeMacros network else network

    let typedNetwork = channelTypes $ unfoldMacros network'
    (assertionCode, numDataSize) <- assertions (useInterface cmdLine) typedNetwork (assertionOptions cmdLine) (optTop cmdLine)

    let networkCode = madl2Verilog network' cmdLine (case numDataSize of Nothing -> 0; Just s -> max 1 s)

    let library = madlLibrary (useInterface cmdLine) (isJust numDataSize) network'
    TIO.writeFile (optOut cmdLine) . T.unlines $ [library, networkCode] ++ [assertionCode | hasAssertions $ assertionOptions cmdLine]

    putStrLn $ "Succes! Output written to " ++optOut cmdLine ++ "."

-- | Remove macros from a network
removeMacros :: MadlNetwork -> MadlNetwork
removeMacros = unflatten . removeMacros' where
    removeMacros' :: MadlNetwork -> XMadlNetwork [Text]
    removeMacros' = cast' . unfoldMacros