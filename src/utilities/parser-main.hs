{-# LANGUAGE OverloadedStrings, CPP #-}

module Main (main) where

import Control.Exception(try, IOException)
import Control.Monad (when)
import System.Console.GetOpt

import Utils.Executable
import Utils.Text

import Madl.Network

import qualified Parser.MadlAST as AST (Network)
import Parser.MadlParser (madlParser)
import Parser.IncludeStatement
import Parser.MadlTypeChecker
import Parser.ASTTranslator

-- | Error function
fileName :: Text
fileName = "parser-main"

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
    argNetwork :: FilePath,
    typeCheck :: Bool,
    checkValid :: Bool,
    showParseResult :: Bool,
    showNetworkSpecification :: Bool,
    showResultingNetwork :: Bool
}

defaultOptions :: CommandLineOptions
defaultOptions = CommandLineOptions {
    argNetwork = "",
    typeCheck = True,
    checkValid = False,
    showParseResult = False,
    showNetworkSpecification = False,
    showResultingNetwork = False
}

exeOptions :: [OptDescr (CommandLineOptions -> CommandLineOptions)]
exeOptions =
    [ Option "f" ["network"]
        (ReqArg (\f opts -> opts {argNetwork = f}) "MaDLFILE")
        "MaDL file name (mandatory).\n"
    , Option "t" ["typecheck"]
        (NoArg (\opts -> opts {typeCheck = True}))
        "Typecheck the parsed file (default)."
    , Option "" ["no-typecheck"]
        (NoArg (\opts -> opts {typeCheck = False}))
        "Don't typecheck the parsed file."
    , Option "c" ["check"]
        (NoArg (\opts -> opts {checkValid = True}))
        "Check whether the parsed network is a valid Madl Network.\n"
    , Option "p" ["show-parse"]
        (NoArg (\opts -> opts {showParseResult = True}))
        "Print the parse tree (AST)."
    , Option "s" ["show-network-specification"]
        (NoArg (\opts -> opts {showNetworkSpecification = True}))
        "Print the network specification."
    , Option "n" ["show-network"]
        (NoArg (\opts -> opts {showResultingNetwork = True}))
        "Print the network datastructure."
    , Option "v" ["verbose"]
        (NoArg (\opts -> opts {showParseResult = True, showNetworkSpecification = True, showResultingNetwork = True}))
        "Print the parse tree, the network specification, and the network datastructure.\n"
    ]

-------------------------
-- Main entry point
-------------------------

main :: IO ()
main = do
    opts <- parseArgs exeOptions defaultOptions
    when (null $ argNetwork opts) $ ioError . userError $ "Provide an input file using -f or --network."
    contentsOrError <- try . readFile $ argNetwork opts
    case contentsOrError of
        Left err -> ioError . userError $ "Couldn't read file " ++ argNetwork opts ++ ": " ++ show (err :: IOException)
        Right contents -> case madlParser (argNetwork opts) contents of
            Left err -> ioError . userError $ "Error parsing file " ++ argNetwork opts ++ ": " ++ show err
            Right ast -> do
                putStrLn "File was succesfully parsed."
                astOrError <- removeIncludeStatements (argNetwork opts) ast
                case astOrError of
                    Left err -> ioError $ userError err
                    Right ast' -> if not (typeCheck opts) then processAST opts ast'
                        else case typecheckNetwork ast' of
                            Left err -> ioError . userError $ "Error typechecking file " ++ argNetwork opts ++ ":\n" ++ showError err
                            Right ast'' -> do
                                putStrLn "File was succesfully typechecked."
                                processAST opts ast''

processAST :: CommandLineOptions -> AST.Network -> IO()
processAST opts ast = do
    let networkspec = networkSpecification $ translateNetwork ast
    when (showParseResult opts) $ putStrLn $ "Parse tree:\n" ++ show ast
    when (showNetworkSpecification opts) $ putStrLn $ "Network specification:\n" ++ utxt (printNetworkSpecification networkspec)
    let net = mkNetwork networkspec
    when (checkValid opts) $ do
        case validMaDLNetwork net of
            Just err -> putStrLn $ "The specified network is not valid:\n" ++ err
            Nothing -> putStrLn "The specified network is valid."
    when (showResultingNetwork opts) $ putStrLn $ "Network datastructure:\n" ++ show net
