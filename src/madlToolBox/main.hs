{-# LANGUAGE OverloadedStrings, DeriveGeneric, ScopedTypeVariables, PartialTypeSignatures #-}

import qualified Data.Map as Map
import Data.List (isPrefixOf)
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import Data.Aeson
import GHC.Generics
import System.Environment

-- This is awful...
import qualified Data.Text as Text

import Utils.Text
import Utils.File

import Madl.Deadlock.DeadlockDetection
import Madl.Deadlock.Runner
import Madl.Network
--import Madl.Cycles
import Madl.Invariants (Invariant,getInvariants,showInvariants2)
import Madl.Deadlock.SMT (SMTModel,export_literal_to_SMT) -- bi_to_name ,export_formula_to_SMT
import Madl.MsgTypes (showColorSetList,showColorNoSpaces) 
import Madl.Deadlock.Formulas



{-
    The reply from the tool box.
    This datatype is converted to JSON and output back to standard out.
-}
data ServerReply = ServerReply {
    errorOccurred :: Bool,
    errorString :: [String],
    fileParses :: Bool,
    fileTypeChecks :: Bool,
    numCycles :: Int,
    combCycles :: [String],
    hasDeadlock :: Bool,
    deadlock :: SMTModel,
    invariants :: [String],
    blockVars :: SMTModel,
    idleVars :: SMTModel,
    procVars :: SMTModel,
    cTypes :: Map.Map String [String],
    dlGraph :: Map.Map String [String]
    } deriving (Generic, Show)
instance ToJSON ServerReply


-- Uses the function fileParses, fileTypeChecks etc. and thus prevents warnings
defaultServerReply :: ServerReply
defaultServerReply = ServerReply {errorOccurred = False, 
                                  errorString = [], 
                                  fileParses = False, 
                                  fileTypeChecks = False, 
                                  numCycles=0, 
                                  combCycles = [],
                                  hasDeadlock = True, 
                                  deadlock = Map.empty, 
                                  cTypes = Map.empty, 
                                  invariants = [],
                                  blockVars = Map.empty,
                                  idleVars = Map.empty,
                                  procVars = Map.empty,
                                  dlGraph = Map.empty
                              }


-- We remove quotes from error message (to solve some issues in Qt and JSON)
removeQuotes :: String -> String
removeQuotes xs = filter (not . (`elem` ['\"'])) xs

{-
	Main:
	run dlockdetect on the input file.
-}
main :: IO ()
main = do    
    -- Fetch user input
    args <- getArgs
    -- We only expect one filename as args
    if (length args == 0)
        then error $ "No arguments were given.\n"
        else -- we go 
            do 
            parsedNet <- readColoredNetworkFromFile defaultReadOptions (head args)
            case parsedNet of
                Left err -> do 
                    let reply = defaultServerReply{errorString = lines $ removeQuotes err}
                    print $ encode reply
                Right net -> do
                    reply <- (verifyNetwork net) 
                    print $ encode reply


            --     return net
            -- reply <- verifyNetwork network
            -- print $ encode reply           

-- Main verification function
-- TODO: see what options are relevant
verifyNetwork :: ColoredNetwork -> IO ServerReply
verifyNetwork network = do
    putStrLn $ "Reading environment variables ..."
    mwb_path_n <- lookupEnv "MWB_PATH_NUXMV"
    _ <- case mwb_path_n of
        Nothing -> setEnv "MWB_PATH_NUXMV" "/usr/local/bin"
        Just _ -> return ()
    newVal <- getEnv "MWB_PATH_NUXMV"
    putStrLn $ "MWB_PATH_NUXMV = "++newVal
    mwb_path_z <- lookupEnv "MWB_PATH_Z3"  
    _ <- case mwb_path_z of
        Nothing -> setEnv "MWB_PATH_Z3" "/usr/local/bin"
        Just _ -> return ()
    newValZ <- getEnv "MWB_PATH_Z3"
    putStrLn $ "MWB_PATH_Z3 = "++newValZ
    let reply = defaultServerReply{fileParses = True, fileTypeChecks = True}
    -- SMT only, since we need a SMT model 
    let options = Madl.Deadlock.Runner.defaultOptions{argRunMode = ReachabilityAfterSmt, argNuxmvOptions =  ReachabilityOptions { keepAigerModel = False, keepNuxmvModel = False, reachabilityEngine = NUXMV IC3}}
    -- Cycle check        
    numC <- return 0;
    --numC <- return $ length $ checkCycles $ removeColors network
    --cyls <- return $ computeCombiCycles network
    cyls <- return [];
    -- Generate invariants
    invs <- generateInvariants network
    -- Queues that are never full
    nfqs <- neverFullQueues network options invs
    -- Deadlock Detection
    dl <- deadlockDetection network options invs nfqs
    case dl of
        Left err -> return $ reply{errorString = lines $ removeQuotes $ err, 
                                   errorOccurred = True, 
                                   numCycles = numC, 
                                   combCycles = cyls, 
                                   cTypes = createChannelTypeMap network, 
                                   invariants = formatInvariants invs network,
                                   dlGraph = createDlGraph network nfqs

                               }
        Right (b,Nothing) -> return $ reply {hasDeadlock = b, 
                                             numCycles = numC , 
                                             combCycles = cyls, 
                                             cTypes = createChannelTypeMap network, 
                                             invariants = formatInvariants invs network, 
                                             dlGraph = createDlGraph network nfqs

                                           }
        Right (b,Just model) -> do
            return $ reply {hasDeadlock = b, 
                            numCycles = numC, 
                            combCycles = cyls, 
                            deadlock = computeDLOutput model, 
                            cTypes = createChannelTypeMap network, 
                            invariants = formatInvariants invs network,
                            blockVars = extract_block_vars model,
                            idleVars = extract_idle_vars model,
                            procVars = extract_proc_vars model,
                            dlGraph = createDlGraph network nfqs
                        }


-- computeCombiCycles :: ColoredNetwork -> [String]
-- computeCombiCycles net = 
--   lines $ removeQuotes $ show $ checkCycles $ removeColors net

computeDLOutput :: SMTModel -> SMTModel 
computeDLOutput m = Map.mapKeys removeQPrefix 
                  $ Map.filterWithKey isOfInterestVar m

formatInvariants :: [Invariant Int] -> ColoredNetwork -> [String]
formatInvariants invs net = 
  lines $ removeQuotes $ utxt $ showInvariants2 invs net 

showFormula :: ColoredNetwork -> Formula -> [String]
showFormula _ T          = ["T"]
showFormula _ F          = ["F"]
showFormula net (Lit l)  = [export_literal_to_SMT net showColorNoSpaces l]
showFormula _ (NOT _) = [] -- let s' = showFormula net f' in ["not ",s']
showFormula net (AND fs) = let fs' = show $ Set.toList $ Set.map (showFormula net) fs in ["AND",fs'] 
showFormula net (OR fs)  = let fs' = show $ Set.toList $ Set.map (showFormula net) fs in ["OR",fs']

showFormulaWithoutQuotes :: ColoredNetwork -> Formula -> [String]
showFormulaWithoutQuotes net f = map removeQuotes (showFormula net f)

createDlGraph :: ColoredNetwork -> [ComponentID] -> Map.Map String [String]
createDlGraph net nfqs = 
  Map.map (showFormulaWithoutQuotes net)
  $ Map.mapKeys (export_literal_to_SMT net showColorNoSpaces) 
  $ unfold_formula net (BlockVars Seq.empty nfqs) spec
  where    
    mkLiteral i Source{} = Lit (BlockSource i)
    mkLiteral _ _ = F
    spec :: Formula
    spec = disjunctive literals
    -- literals = Seq Formula
    literals = Seq.fromList $ map (uncurry mkLiteral) (getComponentsWithID net)


createChannelTypeMap :: ColoredNetwork -> Map.Map String [String] --Map.Map (XChannel Text) Madl.MsgTypes.ColorSet
createChannelTypeMap network =  Map.map showColorSetList $ Map.mapKeys (Text.unpack . channelName) $  Map.fromDistinctAscList (getChannels network)

extract_block_vars :: SMTModel -> SMTModel
extract_block_vars model = Map.mapKeys removeBlockPrefix $ Map.filterWithKey isBlockVar model

extract_idle_vars :: SMTModel -> SMTModel
extract_idle_vars model = Map.mapKeys removeIdlePrefix $ Map.filterWithKey isIdleVar model

extract_proc_vars :: SMTModel -> SMTModel
extract_proc_vars model = Map.mapKeys removeProcPrefix $ Map.filterWithKey isProcVar model

removeBlockPrefix :: String -> String
removeBlockPrefix = drop 6 

removeIdlePrefix :: String -> String
removeIdlePrefix = drop 5 

removeProcPrefix :: String -> String
removeProcPrefix = drop 4

isBlockVar :: String -> Int -> Bool
isBlockVar var _ = isPrefixOf "block" var

isIdleVar :: String -> Int -> Bool
isIdleVar var _ = isPrefixOf "idle" var

isProcVar :: String -> Int -> Bool
isProcVar var _ = isPrefixOf "P___" var

isSMTQueueVar :: String -> Bool
isSMTQueueVar var = isPrefixOf "Q___" var

isSMTMergeVar :: String -> Bool
isSMTMergeVar var = isPrefixOf "M___" var

isOfInterestVar :: String -> Int -> Bool
isOfInterestVar var _ = (isSMTMergeVar var) || (isSMTQueueVar var) 

removeQPrefix :: String -> String
removeQPrefix = drop 4 

-- cycleCheck :: ColoredNetwork -> IO Int
-- cycleCheck network = do
--     let cycles = checkCycles $ removeColors network
--     let num_cycles = length cycles
--     -- putStrLn $ "The network contains " ++ show num_cycles ++ " cycles."
--     return num_cycles

generateInvariants :: ColoredNetwork -> IO [Invariant Int]
generateInvariants network = do
    let invs = getInvariants network
    --putStrLn $ "Found " ++ show (length invs) ++ " invariants."
    --putStrLn $ "Invariants: \n"
    --putStrLn $ utxt (showInvariants2 invs network)
    return invs 

neverFullQueues :: ColoredNetwork -> CommandLineOptions -> [Invariant Int] -> IO [ComponentID]
neverFullQueues network options invs = do
    --putStrLn $ "Computing never full queues ..."
    nfqs <- notFullQueues network (argSMTSolver options) invs
    --putStrLn $ "Found " ++ show (length nfqs) ++ " queues that are never full."
    --putStrLn ("Never full queues are: " ++ show nfqs)
    return nfqs

deadlockDetection :: ColoredNetwork -> CommandLineOptions -> [Invariant Int] ->[ComponentID] -> IO (Either String (Bool,Maybe SMTModel))
deadlockDetection network options invs nfqs = do
    --putStrLn $ "Running deadlock detection."
    -- Run deadlock detection using the options specified by the user
    result <- runDeadlockDetection network options invs nfqs
    -- Handle the result of the deadlock detection
    return result








