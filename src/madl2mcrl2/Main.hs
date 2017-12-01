{-# LANGUAGE OverloadedStrings #-}

module Main(main) where

import System.Environment
import Madl2mCRL2.Converter
import Utils.File
--import System.Console.GetOpt
--import Madl.Islands

main :: IO ()
main = do
  args <- getArgs
  parsed <- readColoredNetworkFromFile defaultReadOptions $ head args
  network <- case parsed of
    Left err -> error err
    Right net -> return net
  --putStr $ test network
  putStr $ makemCRL2 network
  --putStrLn $ show $ network
  --putStrLn $ show $ transferIslands network
