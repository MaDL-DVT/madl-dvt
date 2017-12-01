{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Main
Description : Main module for the dlockdetect tool.
Copyright   : (c) Sanne Wouda 2015, Tessa Belder 2015-2016

This module is the main module of the dlockdetect tool.
It contains the commandline options of this tool, and a @main@ function to handle user I/O.
-}
module Main(main) where

import Control.Monad (when)

--import qualified Data.Text as T
import Data.Char (isDigit)
import qualified Data.HashMap as Hash
import GHC.Conc (numCapabilities)
import System.Console.GetOpt

import Utils.Executable
import Utils.File
import Utils.Text
import Utils.Tuple

import Madl.Deadlock.Runner
import qualified Examples

import Madl.Network
import Madl.Invariants (getInvariants,showInvariants2)
import Madl.Cycles
import Madl.Rings (findRings, showRing, combineRings, getRingInvariants)
import Madl.Livelock (findPossibleLivelocks)
--import Madl.SourceInformation


-- Error function
fileName :: Text
fileName = "dlockdetect.main"

fatal :: Int -> String -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++ s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | CommandLine Options
exeOptions :: [OptDescr (CommandLineOptions -> CommandLineOptions)]
exeOptions =
    [  Option "x" []
        (ReqArg (\x opts -> opts {argNetwork = Left $ txt x}) "MaDLNETWORK")
        "Specify input network from a list of predefined networks."
    , Option "f" ["network"]
        (ReqArg (\f opts -> opts {argNetwork = Right f}) "MaDLFILE")
        "Specify input network as filename.\n "
    , Option "t" ["channeltypes"]
        (NoArg (\opts -> opts {showChannelTypes = True}))
        "Show the calculated channeltypes of the network."
    , Option "s" ["channelsource"]
        (NoArg (\opts -> opts {showChannelSource = True}))
        "Show source information for all channels."
    , Option "" ["channelConnect"]
        (NoArg (\opts -> opts {showChannelConnections = True}))
        "Show initiators and targets of channels."
    , Option "" ["no-typecheck"]
        (NoArg (\opts -> opts {argTypeCheck = False}))
        "Don't typecheck the given MaDL file.\n"
    , Option "" ["no-cyclecheck"]
        (NoArg (\opts -> opts {argCycleCheck = False}))
        "Don't search for combinatorial cycles.\n"
    , Option "" ["stop-at-first"]
        (NoArg (\opts -> opts {argSources = ONE}))
        "Stop deadlock detection after the first source with a deadlock has been found (default)."
    , Option "" ["all-sources"]
        (NoArg (\opts -> opts {argSources = ALL}))
        "Run deadlock detection for all sources of the network."
    , Option "v" ["verbose"]
        (NoArg (\opts -> opts {argVerbose = ON}))
        "Print verbose output.\n "
    , Option "" ["no-invariants"]
        (NoArg (\opts -> opts {argUseInvariants = False}))
        "Don't calculate network invariants.\n "
    , Option "" ["smt-only"]
        (NoArg (\opts -> opts {argRunMode = SmtOnly}))
        "Liveness proof using only SMT."
    , Option "" ["reachability-only"]
        (NoArg (\opts -> opts {argRunMode = ReachabilityOnly}))
        "Liveness proof using only reachability."
    , Option "" ["reachability-after-smt"]
        (NoArg (\opts -> opts {argRunMode = ReachabilityAfterSmt}))
        "Liveness proof by first trying SMT. If deadlock found, then perform reachability analysis (default)."
    , Option "" ["nuxmv-model-only"]
        (NoArg (\opts -> opts {argRunMode = NuxmvModelOnly}))
        "Create SMV model of the network and write it to model.nuxmv.\n "
    , Option "" ["keep-all-models"]
        (NoArg (\opts -> opts {argKeepSMTModel = True,
                argNuxmvOptions = (argNuxmvOptions opts) {keepAigerModel = True, keepNuxmvModel = True}}))
        "Keep the file(s) containing the AIG, SMV and SMT model(s) after performing a liveness proof.\n "
    , Option "" ["keep-aiger-model"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {keepAigerModel = True}}))
        "Keep the file containing the AIG model after performing a liveness proof using ABC.\n "
    , Option "" ["keep-nuxmv-model"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {keepNuxmvModel = True}}))
        "Keep the file containing the SMV model after performing a liveness proof using nuXmv."
    , Option "" ["keep-smt-model"]
        (NoArg (\opts -> opts {argKeepSMTModel = True}))
        "Keep the file(s) containing the SMT model(s) after performing a liveness proof using SMT.\n "
    , Option "" ["z3"]
        (NoArg (\opts -> opts {argSMTSolver = Z3}))
        "Set Z3 as SMT solver (default)."
    --, Option "" ["cvc4"]
    --    (NoArg (\opts -> opts {argSMTSolver = CVC4}))
    --    "Set CVC4 as SMT solver.\n "
    , Option "" ["abc"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = ABC PDR}}))
        "Proof using ABC with PDR."
    , Option "" ["abc-bmc"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = ABC BMC}}))
        "Proof using ABC with BMC with dynamic unrolling (bmc3)."
    , Option "" ["ic3"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV IC3}}))
        "NuXmv invariant proof with ic3 search."
    , Option "" ["ic3m"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV IC3M}}))
        "NuXmv invariant proof with ic3 search using SMT. (default)"
    , Option "" ["bdd"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV BDD}}))
        "NuXmv invariant proof with BDD search."
    , Option "" ["forward"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV FWD}}))
        "NuXmv invariant proof with forward BDD search."
    , Option "" ["backward"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV BWD}}))
        "NuXmv invariant proof with backward BDD search."
    , Option "" ["forward-backward"]
        (NoArg (\opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV FWDBWD}}))
        "NuXmv invariant proof with forward-backward BDD search."
    , Option "" ["bdd-bmc"]
        (OptArg (\depth opts -> opts {argNuxmvOptions = (argNuxmvOptions opts) {reachabilityEngine = NUXMV $ BDDBMC (case depth of
                    Nothing -> 20
                    Just n -> if all isDigit n && (read n :: Int) > 0 then read n :: Int
                                else fatal 94 $ "Unvalid argument: bdd-bmc depth " ++n)}})
            "search-depth")
        "NuXmv invariant proof with bdd-bmc search."
    , Option "" ["showrings"]
        (NoArg (\opts -> opts {showRings = True}))
        "Display detailed ring information."

    ]

-- | Main entry point
main :: IO ()
main = do
    -- Fetch user input
    options <- parseArgs exeOptions defaultOptions
    -- Print the number of cores in use.
    putStrLn $ "Using " ++ show numCapabilities ++ " cores."
    -- Print some output for the users not to wait in front of a blank screen
    putStrLn $ "Reading network ..."
    -- Fetch the network specified by the user
    network<-  case argNetwork options of
        -- If the name of a predefined network has been given, check if a predefined network with this name indeed exists
        Left netname -> case Hash.lookup netname Examples.networkMapTyped of
            Nothing -> fatal 30 $ "Unknown network " ++ utxt netname ++ ", use -x to pick one of: " ++ show (Hash.keys Examples.networkMap)
            Just net -> return net
        -- If a filename has been given, try to parse and translate this file
        Right filepath -> do
            parsedNet <-  {-# SCC "ReadingNetwork" #-} readColoredNetworkFromFile defaultReadOptions{readTypeCheck = argTypeCheck options} filepath
            case parsedNet of
                Left err -> fatal 191 err
                Right net -> return net
    -- Print some output for the users not to wait in front of a blank screen
    putStrLn $ "Reading network completed."            
    let comps = getComponents network                 
    -- Print some general network statistics.
    when (argVerbose options == ON) $ putStrLn $ "#Components: " ++ (show $ length comps)
    when (argVerbose options == ON) $ putStrLn $ "#Queues: " ++ (show $ length (filter isQueue comps))
    when (argVerbose options == ON) $ putStrLn $ "#Automata: " ++ (show $ length (filter isAutomaton comps))
    when (argVerbose options == ON) $ putStrLn $ "#Forks: " ++ (show $ length  (filter isFork comps))
    when (argVerbose options == ON) $ putStrLn $ "#CtrlJoins: " ++ (show $ length (filter isCJoin comps) )
    when (argVerbose options == ON) $ putStrLn $ "#Switches: " ++ (show $ length  (filter isSwitch comps))      
    when (argVerbose options == ON) $ putStrLn $ "#Merges: " ++ (show $ length  (filter isMerge comps))      
    when (argVerbose options == ON) $ putStrLn $ "#Functions: " ++ (show $ length  (filter isFunction comps)) 
    when (argVerbose options == ON) $ putStrLn $ "#LoadBalancers: " ++ (show $ length  (filter isLoadBalancer comps))           
    when (argVerbose options == ON) $ putStrLn $ "#Largest cc: " ++ (show $ largestConnectedComponent network)
    when (showChannelTypes options) $ putStrLn "ChannelTypes:"
    when (showChannelTypes options) $ mapM_ (putStrLn . show) (getChannelsWithID network)
    when (showChannelConnections options) $ mapM_ (putStrLn . show . withInitAndTarget network) (getChannelIDs network)
    when (showChannelConnections options) $ mapM_ (putStrLn . show) (getComponentsWithID network)
    --when (showChannelSource options) $ case sourceinfo of
    --    Nothing -> return ()
    --    Just srcinfo -> do
    --        putStrLn "ChannelSource:"
    --        mapM_ (putStrLn . uncurry showSource) (Hash.assocs $ channelSource srcinfo)
    when (argCycleCheck options) $ putStrLn $ "Checking for combinatorial cycles."
    let cycles = {-# SCC "CheckingForCycles" #-} if argCycleCheck options then checkCycles noColorNetwork else [] 
                where noColorNetwork = removeColors network
    putStrLn $ "The network contains " ++ show (length cycles) ++ " cycles."
    when (argVerbose options == ON) $ putStrLn $ "Cycles:\n" 
    when (argVerbose options == ON) $ mapM_ (putStrLn . show) cycles

    -- Search possible livelocks
    let liveLock = findPossibleLivelocks network
    putStrLn $ case liveLock of 
        Nothing -> "No possible livelocks found."
        Just loop -> "Found possible livelock." ++ if (argVerbose options == ON)
            then "\n" ++ (show $ map (\(chan, col) -> (channelName $ fst $ snd3 $ getChannelContext network chan, col)) loop)
            else ""

    -- Detect rings
    let rings = findRings network
    putStrLn $ "Found " ++ show (length rings) ++ " base rings."
    when (showRings options) $ mapM_ (putStrLn . (showRing network)) rings
    let combRings = combineRings network rings
    putStrLn $ "Found " ++ (show $ (length combRings)) ++ " combined rings."
    when (showRings options) $ mapM_ (putStrLn . (showRing network)) (filter (\r -> not $ elem r rings) combRings)

    -- Get ring invariants from combined rings
    let ringInvs = getRingInvariants network combRings
    putStrLn $ "Found " ++ (show $ length ringInvs) ++ " ring invariants."
    when (showRings options) $ putStrLn $ utxt (showInvariants2 ringInvs network)

    putStrLn ("Computing network invariants ... ")
    -- Invariants are not computed if there is either no forks or no joins. 
--    let invs = {-# SCC "GenerateInvariants" #-} if argUseInvariants options && (length  (filter isFork comps) > 0 && length (filter isCJoin comps) > 0) then getInvariants network else []
    let invs = {-# SCC "GenerateInvariants" #-} if argUseInvariants options then getInvariants network else []
    putStrLn $ "Found " ++ show (length invs) ++ " invariants."
    when (argVerbose options == ON) $ putStrLn $ "Invariants: \n"
    when (argVerbose options == ON) $ putStrLn $ utxt (showInvariants2 invs network)

    putStrLn $ "Computing never full queues ..."
    nfqs <- {-# SCC "ComputeNeverFullQueues" #-} notFullQueues network (argSMTSolver options) (invs ++ ringInvs)
    putStrLn $ "Found " ++ show (length nfqs) ++ " queues that are never full."
    when (argVerbose options == ON) $ putStrLn ("Never full queues are: " ++ show nfqs)
    putStrLn $ "Running deadlock detection."
    -- Run deadlock detection using the options specified by the user
    result <- runDeadlockDetection network options (invs ++ ringInvs) nfqs
    -- Handle the result of the deadlock detection
    case result of
        Left err -> putStrLn err
        Right (True,_) -> putStrLn "Deadlock!"
        Right (False,_) -> putStrLn "No deadlock found."
    return () 

withInitAndTarget :: Network a b -> ChannelID -> (ComponentID, ChannelID, ComponentID)
withInitAndTarget network xID = (getInitiator network xID, xID, getTarget network xID)


--showSource :: [Text] -> SourceInformation -> String
--showSource name info = utxt (T.intercalate "_" name) ++ ": " ++ show info
