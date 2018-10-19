{-# LANGUAGE OverloadedStrings, DeriveGeneric, ScopedTypeVariables, PartialTypeSignatures #-}

-- small executable that produces a string encoding the map for all processes of the network.

import Utils.File
import Madl.Network
import System.Environment

removeQuotes :: String -> String
removeQuotes xs = filter (not . (`elem` ['\"'])) xs


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
                    print $ err
                Right net -> do 
                    print $ (showProcessMaps net) 


showProcessMaps :: ColoredNetwork -> [String]
showProcessMaps net = map (removeQuotes . prettyPrintStateMap) stMaps where
  procs = getAllProcesses net
  stMaps = map getAutomatonStateMapWithProcessName procs
