{-# LANGUAGE OverloadedStrings, DeriveGeneric, ScopedTypeVariables, PartialTypeSignatures #-}

-- small executable that only computes the colours of all channels.

import qualified Data.Map as Map
--import Data.List (isPrefixOf)
--import qualified Data.Set as Set
--import qualified Data.Sequence as Seq
import Data.Aeson
import GHC.Generics
import System.Environment

-- This is awful...
import qualified Data.Text as Text

--import Utils.Text
import Utils.File

import Madl.Network
import Madl.MsgTypes (showColorSetList) 
import Madl.Deadlock.SMT (SMTModel) -- bi_to_name ,export_formula_to_SMT

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
    return $ defaultServerReply{fileParses = True, 
                                fileTypeChecks = True, 
                                hasDeadlock = False,
                                cTypes = createChannelTypeMap network}
    
createChannelTypeMap :: ColoredNetwork -> Map.Map String [String] --Map.Map (XChannel Text) Madl.MsgTypes.ColorSet
createChannelTypeMap network =  Map.map showColorSetList $ Map.mapKeys (Text.unpack . channelName) $  Map.fromDistinctAscList (getChannels network)










