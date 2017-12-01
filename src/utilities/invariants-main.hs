{-# LANGUAGE OverloadedStrings, CPP #-}

module Main (main) where

import qualified Data.HashMap as Hash

import qualified Data.Text as T
import Control.Monad (when)
import System.Console.GetOpt

import Utils.Executable
import Utils.File
import Utils.Text

import Madl.Cycles
import Madl.Invariants (showInvariants, matrix)
import Madl.Network
import Madl.SourceInformation

import qualified Examples

-- | Error function
fileName :: Text
fileName = "invariants-main"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-------------------------
-- CommandLine Options
-------------------------

data CommandLineOptions = CommandLineOptions {
    argNetwork :: Either Text FilePath,
    argTypeCheck      :: Bool,
    checkValid        :: Bool,
    cycleCheck        :: Bool,
    showChannelTypes  :: Bool,
    showChannelSource :: Bool,
    showChannelConnections :: Bool,
    showMatrix        :: Bool
}

defaultOptions :: CommandLineOptions
defaultOptions = CommandLineOptions {
    argNetwork          = Left "twoagents10",
    argTypeCheck        = True,
    checkValid          = False,
    cycleCheck          = False,
    showChannelTypes    = False,
    showChannelSource   = False,
    showChannelConnections = False,
    showMatrix          = False
}

exeOptions :: [OptDescr (CommandLineOptions -> CommandLineOptions)]
exeOptions =
    [ Option "x" []
        (ReqArg (\x opts -> opts {argNetwork = Left $ txt x}) "MaDLNETWORK")
        "Name of predefined MaDL network (default is 'twoagents10')."
    , Option "f" ["network"]
        (ReqArg (\f opts -> opts {argNetwork = Right f}) "MaDLFILE")
        "MaDL file name.\n"
    , Option "" ["no-typecheck"]
        (NoArg (\opts -> opts {argTypeCheck = False}))
        "Don't typecheck the given MaDL file.\n"
    , Option "c" ["check"]
        (NoArg (\opts -> opts {checkValid = True}))
        "Check whether chosen network is a valid Madl Network."
    , Option "t" ["channeltypes"]
        (NoArg (\opts -> opts {showChannelTypes = True}))
        "Show the calculated channeltypes of the network."
    , Option "s" ["channelsource"]
        (NoArg (\opts -> opts {showChannelSource = True}))
        "Show source information for all channels."
    , Option "" ["channelConnect"]
        (NoArg (\opts -> opts {showChannelConnections = True}))
        "Show initiators and targets of channels."
    , Option "" ["cycle"]
        (NoArg (\opts -> opts {cycleCheck = True}))
        "Check whether chosen network contains combinatorial cycles."
    , Option "" ["matrix"]
        (NoArg (\opts -> opts {showMatrix = True}))
        "Show the invariant matrix."
    ]

-------------------------
-- Main entry point
-------------------------

main :: IO ()
main = do
    opts <- parseArgs exeOptions defaultOptions
    (network, sourceinfo) <- case argNetwork opts of
        Left netname -> case Hash.lookup netname Examples.networkMapTyped of
            Nothing -> ioError . userError $ "Unknown network " ++ utxt netname ++ ", use -x to pick one of: " ++ show (Hash.keys Examples.networkMap)
            Just net -> return (net, Nothing)
        Right filename -> do
            networkOrError <- readColoredNetworkFromFileWithSource defaultReadOptions{readNetworkCheck = False, readTypeCheck = argTypeCheck opts} filename
            case networkOrError of
                Left err -> ioError $ userError err
                Right (net, specsrc) -> return (net, Just specsrc)
    let noColorNetwork = removeColors network
    when (checkValid opts) $ case validMaDLNetwork $ cast' noColorNetwork of
        Just err -> putStrLn err
        Nothing -> putStrLn "Valid network!"
    when (cycleCheck opts) $ case checkCycles noColorNetwork of
        [] -> putStrLn "The network contains no cycles"
        cycles -> do
            putStrLn "The network contains cycles:"
            mapM_ (putStrLn . show) cycles
    let comps = getComponents network
     -- Print some general network statistics.
    putStrLn $ "#Components: " ++ (show $ length comps)
    putStrLn $ "#Queues: " ++ (show $ length (filter isQueue comps))
    putStrLn $ "#Automata: " ++ (show $ length (filter isAutomaton comps))
    putStrLn $ "#CtrlJoins: " ++ (show $ length (filter isCJoin comps))
    putStrLn $ "#Forks: " ++ (show $ length (filter isFork comps))    
    putStrLn $ "#Largest cc: " ++ (show $ largestConnectedComponent network)
    when (showChannelTypes opts) $ putStrLn "ChannelTypes:"
    when (showChannelTypes opts) $ mapM_ (putStrLn . show) (getChannelsWithID network)
    when (showChannelConnections opts) $ mapM_ (putStrLn . show . withInitAndTarget network) (getChannelIDs network)
    when (showChannelConnections opts) $ mapM_ (putStrLn . show) (getComponentsWithID network)
    when (showChannelSource opts) $ case sourceinfo of
        Nothing -> return ()
        Just srcinfo -> do
            putStrLn "ChannelSource:"
            mapM_ (putStrLn . uncurry showSource) (Hash.assocs $ channelSource srcinfo)
    putStrLn "Invariants:"
    putStrLn $ utxt (showInvariants network)
    when (showMatrix opts) $ mapM_ (putStrLn . show) (matrix network)

withInitAndTarget :: Network a b -> ChannelID -> (ComponentID, ChannelID, ComponentID)
withInitAndTarget network xID = (getInitiator network xID, xID, getTarget network xID)

showSource :: [Text] -> SourceInformation -> String
showSource name info = utxt (T.intercalate "_" name) ++ ": " ++ show info