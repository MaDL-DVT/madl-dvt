{-|
Module      : Utils.Executable
Description : Utilities for reading commandline arguments
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for reading commandline arguments. It should be used in all executables of the madl toolset.
-}
module Utils.Executable(parseArgs) where

import Control.Monad (when)
import System.Console.GetOpt
import System.Environment
import System.Exit (exitSuccess)

-- | Extends an options object with a "help" option
data CommandLineOptions a = CommandLineOptions {
    help :: Bool,
    options :: a
}

-- | Default extended options: pairs the given default options with the default "help" flag
defaultOptions :: a -> CommandLineOptions a
defaultOptions opts = CommandLineOptions{
    help = False,
    options = opts
}

-- | Lift the optionsdescription of an options object to an extended optionsdescriptions including the "help (-h)" flag
exeOptions :: [OptDescr (a -> a)] -> [OptDescr (CommandLineOptions a -> CommandLineOptions a)]
exeOptions = (helpOption :) . map liftOption where
    helpOption = Option "h" ["help"] (NoArg (\opts -> opts {help = True})) "Show this help.\n "
    liftOption :: OptDescr (a -> a) -> OptDescr (CommandLineOptions a -> CommandLineOptions a)
    liftOption (Option short long fun descr) = Option short long (lift fun) descr

    lift :: ArgDescr (a -> a) -> ArgDescr (CommandLineOptions a -> CommandLineOptions a)
    lift (NoArg fun) = NoArg (\opts -> opts{options = fun $ options opts})
    lift (ReqArg fun descr) = ReqArg (\arg opts -> opts{options = fun arg $ options opts}) descr
    lift (OptArg fun descr) = OptArg (\arg opts -> opts{options = fun arg $ options opts}) descr

-- | Given an optionsdescription and a set of default options, read user input from commandline and return the selected options
parseArgs :: [OptDescr (a -> a)] -> a -> IO a
parseArgs exeOpts defaultOpts = do
    args <- getArgs
    case getOpt RequireOrder (exeOptions exeOpts) args of
        (opts, [], []) -> do
            let cmdOptions = foldl (flip id) (defaultOptions defaultOpts) opts
            when (help cmdOptions) $ showHelp (exeOptions exeOpts)
            return $ options cmdOptions
        (_, args', []) -> ioError . userError $ "Unsupported arguments: " ++ show args' ++ ".\nUse -h or --help for an overview of supported arguments."
        (_, _, errs) -> ioError . userError $ concat errs ++ "Use -h or --help for an overview of supported options."

-------------------------
-- Help message
-------------------------

-- | Given an optionsdescription, shows a help message
showHelp :: [OptDescr (a -> a)] -> IO()
showHelp exeOpts = do
    putStrLn $ usageInfo helpHeader exeOpts
    exitSuccess

-- | Header of the help message triggered by the "help" flag
helpHeader :: String
helpHeader = unlines [
      "\n(c) Copyright 2015 - 2018 Eindhoven University of Technology"
    , "**********************************************************************"
    , "**                                                                  **"
    , "**              MaDL Design and Verification Environment            **"
    , "**                                                                  **"
    , "**********************************************************************"
    ]