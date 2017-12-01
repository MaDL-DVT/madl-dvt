{-|
Module      : Utils.File
Description : Utilities for parsing, typechecking and translating madl files
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for parsing, typechecking and translating madl files
-}
module Utils.File(
        ReadOptions(..), defaultReadOptions,
        readNetworkFromFile, readNetworkFromFileWithSource,
        readFlattenedNetworkFromFile, readFlattenedNetworkFromFileWithSource,
        readColoredNetworkFromFile, readColoredNetworkFromFileWithSource
    ) where

import Control.Exception(try, IOException)

import Utils.Tuple

import Madl.Network
import qualified Parser.MadlAST as AST (Network)
import Parser.MadlParser
import Parser.IncludeStatement
import Parser.MadlTypeChecker
import Parser.ASTTranslator

-- | Options for processing the madl file
data ReadOptions = ReadOptions {
    readNetworkCheck :: Bool, -- ^ Check if the specified MaDL network is valid
    readTypeCheck :: Bool -- ^ Typecheck the file after parsing (deprecated: should always be @True@)
}
-- | Default read options: @readNetworkCheck = True@ and @readTypeCheck = True@
defaultReadOptions :: ReadOptions
defaultReadOptions = ReadOptions {
    readNetworkCheck = True,
    readTypeCheck = True
}

-- | Read the specified madl file, and return either an error or the resulting network
readNetworkFromFile :: ReadOptions -> FilePath -> IO (Either String MadlNetwork)
readNetworkFromFile opts = fmap (fmap fst) . readNetworkFromFileWithSource opts

-- | Read the specified madl file, and return either an error, or the resulting network and a 'SpecificationSource' linking back to the provided madl file
readNetworkFromFileWithSource :: ReadOptions -> FilePath -> IO (Either String (MadlNetwork, SpecificationSource))
readNetworkFromFileWithSource opts filepath = (either readError processContents =<<) . try $ readFile filepath where
    processContents :: String -> IO (Either String (MadlNetwork, SpecificationSource))
    processContents = either parseError processNetwork . madlParser filepath
    processNetwork :: AST.Network -> IO (Either String (MadlNetwork, SpecificationSource))
    processNetwork = fmap (either Left processNetwork') . removeIncludeStatements filepath where
        processNetwork' = if readTypeCheck opts then typeCheckNetwork else makeNetwork
    typeCheckNetwork :: AST.Network -> Either String (MadlNetwork, SpecificationSource)
    typeCheckNetwork = either typecheckError makeNetwork . typecheckNetwork
    makeNetwork :: AST.Network -> Either String (MadlNetwork, SpecificationSource)
    makeNetwork network = checkNetwork $ Right (net, specSrc) where
        checkNetwork res = if readNetworkCheck opts then maybe res validNetError $ validMaDLNetwork net else res
        (NSpecSrc spec specSrc) = translateNetwork network
        net = mkNetwork spec

    readError err = return . Left $ "Couldn't read file " ++ filepath ++ ": " ++ show (err :: IOException)
    parseError err = return . Left $ "Error parsing file " ++ filepath ++ ": " ++show err
    typecheckError err = Left $ "Typecheck error:\n" ++showError err
    validNetError err = Left $ "The network specified by file " ++ filepath ++ " is not valid: " ++ err

-- | Read the specified madl file, and return either an error or the resulting network without macro instances
readFlattenedNetworkFromFile :: ReadOptions -> FilePath -> IO (Either String FlattenedNetwork)
readFlattenedNetworkFromFile opts = fmap (fmap fst) . readFlattenedNetworkFromFileWithSource opts

-- | Read the specified madl file, and return either an error, or the resulting network without macro instances
-- and a 'SpecificationSource' linking back to the provided madl file
readFlattenedNetworkFromFileWithSource :: ReadOptions -> FilePath -> IO (Either String (FlattenedNetwork, SpecificationSource))
readFlattenedNetworkFromFileWithSource opts = fmap (fmap $ mapFst unfoldMacros') . readNetworkFromFileWithSource opts where
    unfoldMacros' :: MadlNetwork -> FlattenedNetwork
    unfoldMacros' net = unflatten (unfoldMacros net :: FlatFlattenedNetwork)

-- | Read the specified madl file, and return either an error or the resulting network with channeltypes
readColoredNetworkFromFile :: ReadOptions -> FilePath -> IO (Either String ColoredNetwork)
readColoredNetworkFromFile opts = fmap (fmap fst) . readColoredNetworkFromFileWithSource opts

-- | Read the specified madl file, and return either an error, or the resulting network with channeltypes
-- and a 'SpecificationSource' linking back to the provided madl file
readColoredNetworkFromFileWithSource :: ReadOptions -> FilePath -> IO (Either String (ColoredNetwork, SpecificationSource))
readColoredNetworkFromFileWithSource opts = fmap (fmap $ mapFst channelTypes) . readFlattenedNetworkFromFileWithSource opts