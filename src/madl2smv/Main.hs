{-# LANGUAGE OverloadedStrings #-}

module Main(main) where

import System.Environment
import Utils.File
import Madl2smv.Converter
--import System.Console.GetOpt
--import Madl.Islands

main :: IO ()
main = do
  args <- getArgs
  parsed <- readColoredNetworkFromFile defaultReadOptions $ head args
  network <- case parsed of
    Left err -> error err
    Right net -> return net
  --putStrLn $ makeSMV network
  --putStrLn $ show $ getMaDL network
  --putStrLn $ show $ mkExpr $ getMaDL network
  putStrLn $ makeSMV network
