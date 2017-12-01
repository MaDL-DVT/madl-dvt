{-# LANGUAGE OverloadedStrings, ImpredicativeTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, NoImplicitPrelude #-}
module Main (main,v2m) where

import qualified Data.ByteString.Char8 as B
import qualified Data.Map as Map
import Data.String (unlines)

import Utils.Map
import Utils.Text

import System.Exit (exitFailure)
import System.IO (IOMode(ReadMode),openFile,writeFile,putStrLn)

import BaseLike.CustomPrelude
import BooleanSymbolic.CalcX (WithDAG, WireReference, runX, transFN)
import BooleanSymbolic.NetStructure (judgeForest, getStructure, closeSolver)
import CommonDataTypes.TraverseProps (InverseProps)
import Verilog.ModuleAnalysis ( processModules, SimpleModule, modName )
import Verilog.Parser (parseInputAsVerilog)
import Verilog.PortsAndBlackBoxes (blackBoxModuleSet, processPropSpecs)

import Madl.Network (MadlNetwork, validMaDLNetwork)
import Madl.ToAut (madl2aut)

import Verilog2MaDL (verilog2MaDL)

main :: IO()
main = do let network = v2m "mod" "xmas_annotations" "bufferedVC2.v"
          valid <- validMaDLNetwork <$> network
          aut <- case valid of
                  Nothing -> madl2aut (""::Text) <$> network 
                  Just v -> do putStrLn v
                               exitFailure
          writeFile "bufferedVC2.aut" $ unlines aut

v2m :: String -> String -> String -> IO MadlNetwork
v2m topModuleName annotations verilog
 = do let commonFiles = [annotations, verilog]
      handles <- sequence (map (flip openFile ReadMode) commonFiles)
      (moduleList, specList) <- concat2 <$> (sequence$ map parseInputAsVerilog handles)
      let blackBoxSet = blackBoxModuleSet specList
      let inspectedModules = map modName moduleList
      let modRes = processModules moduleList inspectedModules blackBoxSet :: forall s. Map B.ByteString (WithDAG s (SimpleModule s))
      let queueAnnotationsFilledIn ::  Map B.ByteString (WithDAG s (InverseProps (WireReference s)))
          queueAnnotationsFilledIn = processPropSpecs specList modRes
      network <- runX (case Map.lookup (B.pack topModuleName) queueAnnotationsFilledIn of 
                                           Nothing -> return (do B.putStrLn "Sorry, the top module was not found!"
                                                                 exitFailure)
                                           Just v ->  madl v)
      return network
    where
    madl :: WithDAG t (InverseProps (WireReference t)) -> WithDAG t (IO MadlNetwork)
    madl props =  closeSolver verilog2MaDL . judgeForest . getStructure <$> (transFN =<< props)

concat2 :: [([a], [a1])] -> ([a], [a1])
concat2 ((a,b):rst) = let (as,bs) = concat2 rst in (a++as,b++bs)
concat2 [] = ([],[])
