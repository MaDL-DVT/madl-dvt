{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Parser.IncludeStatement
Description : Handles Madl include statements
Copyright   : (c) Tessa Belder 2016

This module contains an function to resolve include statements from a Madl file.
-}
module Parser.IncludeStatement (removeIncludeStatements) where

import Control.Exception(try, IOException)

import qualified Data.HashMap as Hash
import Data.List
import Data.Maybe
import qualified Data.Set as Set

import System.FilePath.Posix

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.SourceInformation

import Parser.MadlAST
import Parser.MadlParser

-- Error function

-- | The name of this module
fileName :: Text
fileName = "Parser.IncludeStatement"

-- | Produces an error message with the given error code
fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

-- | Pairs the module name with an error code
src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | Replaces an include statement by the list of network statements from the included file. Other types of network statements are unchanged.
transformIncludeStatement :: Hash.Map FilePath [NetworkStatementSrc] -> FilePath -> NetworkStatementSrc
                                -> (Set FilePath, [NetworkStatementSrc]) -> (Set FilePath, [NetworkStatementSrc])
transformIncludeStatement includeFiles currentpath statement (alreadyIncluded, processedStatements) = case removeSourceInfo statement of
    NetworkIncludeStatement includeStatement -> if Set.member includePath alreadyIncluded
        then (alreadyIncluded, processedStatements)
        else (Set.insert includePath alreadyIncluded', includeStatements') where
        (alreadyIncluded', includeStatements') = includeAll includeStatements
        includeAll = foldl' (flip $ transformIncludeStatement includeFiles includePath) (alreadyIncluded, processedStatements)
        includeStatements = lookupM (src 18) includePath includeFiles :: [NetworkStatementSrc]
        includePath = getIncludePath currentpath includeStatement
    _ -> (alreadyIncluded, processedStatements ++ [statement])

-- | Returns the filepaths of all the top-level include files of a given network.
networkIncludePaths :: FilePath -> Network -> [FilePath]
networkIncludePaths base (NetworkStatements statements) = mapMaybe (includePath . removeSourceInfo) statements where
    includePath (NetworkIncludeStatement include) = Just $ getIncludePath base include
    includePath _ = Nothing

-- | Given a base filepath, returns the filepath represented by an include-statement.
getIncludePath :: FilePath -> IncludeStatement -> FilePath
getIncludePath base (IncludeStatement attr) = flip addExtension "madl" . combine (takeDirectory base) . joinPath $ map utxt attr

-- | Replaces all the include statements in a network by the list of network statements they represent.
-- Fails if cycles in the include-tree are found, or if parsing of any of the included files fails.
removeIncludeStatements :: FilePath -> Network -> IO (Either String Network)
removeIncludeStatements filename net@(NetworkStatements statements) = case getIncludeCycles filename net of
    [] -> do
        let includepaths = networkIncludePaths filename net
        includepaths' <- resolveIncludePaths includepaths (return [])
        case includepaths' of
            Left err -> return $ Left err
            Right resolvedPaths -> return . Right $ NetworkStatements statements' where
                (_, statements') = foldl' (flip $ transformIncludeStatement includeFiles filename) (Set.empty, []) statements
                includeFiles = Hash.fromList $ map (mapSnd $ \(NetworkStatements s) -> filter isIncludeStatement s) resolvedPaths
    _cycles -> return $ Left "Specified network has include cycles" --todo(tssb) add cycles to msg

-- | Specifies which statements should be included
isIncludeStatement :: NetworkStatementSrc -> Bool
isIncludeStatement statement = case removeSourceInfo statement of
    NetworkIncludeStatement{} -> True
    NetworkMacro{} -> True
    _ -> False

-- | Parses the given files, and recursively parses all files included in the given files.
-- Fails if the parsing of any of these files fails.
resolveIncludePaths :: [FilePath] -> IO [(FilePath, Network)] -> IO (Either String [(FilePath, Network)])
resolveIncludePaths [] files = fmap Right files
resolveIncludePaths (path:ps) files = do
    alreadyCovered <- fmap (any ((path ==) . fst)) files
    if alreadyCovered then resolveIncludePaths ps files
    else do
        contentsOrError <- tryParseFile path
        case contentsOrError of
            Left err -> return $ Left err
            Right (network, includepaths) -> resolveIncludePaths (ps ++ includepaths) (fmap ((path, network) :) files)

-- | Try to parse the file at the given filepath.
tryParseFile :: FilePath -> IO (Either String (Network, [FilePath]))
tryParseFile filepath = do
    contentsOrError <- try $ readFile filepath
    case contentsOrError of
        Left err -> return . Left $ "Couldn't read file " ++ filepath ++ ": " ++ show (err :: IOException)
        Right contents -> case madlParser filepath contents of
            Left err -> return . Left $ "Error parsing file " ++ filepath ++ ": " ++ show err
            Right network -> return $ Right (network, networkIncludePaths filepath network)

-- | Returns all the include cycles in the given network
getIncludeCycles :: FilePath -> Network -> [a]
getIncludeCycles _ _ = [] --todo(tssb) implement inclusion cycle checker