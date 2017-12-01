{-# OPTIONS_GHC -Wall -Werror #-}
{-# LANGUAGE OverloadedStrings, ImpredicativeTypes, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, NoImplicitPrelude #-}
module Main (main) where
{-
For examples to call this, see bottom
-}

import System.Exit (exitSuccess, exitFailure)
import System.Environment (getArgs)
import System.IO (stderr,IOMode(ReadMode),openFile)
import Verilog.Parser (parseInputAsVerilog)
import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as B -- hiding (null,map,take) -- (ByteString)
import qualified Data.Set as Set (union,difference,fromList,toList)
import Verilog.ModuleAnalysis ( processModules, showModule, SimpleModule, modName )
import Verilog.PortsAndBlackBoxes (blackBoxModuleSet, processBlackBoxes, processPropSpecs, showBlackBoxes)
import BooleanSymbolic.CalcX (WithDAG, WireReference, showWireReference, runX, transFN)
import EchelonForms.SumOfProductForEchelon (showGaussRes, gaussianEliminate, getInvariants)
import BaseLike.CustomPrelude
import BooleanSymbolic.NetStructure (showForest, judgeForest, showNetGraph, getStructure, closeSolver)
import BooleanSymbolic.SMT (showSMT,buildSMT)
import CommonDataTypes.TraverseProps (InverseProps) -- this type (imported without constructors) can be derived and is imported for documentation only

showHelp :: [B.ByteString] -> IO ()
showHelp lst
 = putLines$ [ "\nWelcome to my Verilog analysis tool (untitled, version 0.1.0.0).\n"
             , "**********************************************************************"
             , "**                                                                  **"
             , "**              You have no license to use this tool!!              **"
             , "**                                                                  **"
             , "**              Unless you are the author of this tool              **"
             , "**              you must remove it from your computer.              **"
             , "**                                                                  **"
             , "**          Sebastiaan Joosten is the author of this tool.          **"
             , "**       The research conducted for this tool started in 2012       **"
             , "**             This notice was written in January 2015.             **"
             , "**           This tool is part of a research in progress.           **"
             , "**       As such, a final date cannot be added to this notice       **"
             , "**         (Check the source's modification date for this.)         **"
             , "**                                                                  **"
             , "** Several (but not all) parts of this tool are licensed separately **"
             , "**                 please use one of those instead.                 **"
             , "**                                                                  **"
             , "**********************************************************************"
             , ""
             , "Command line options:"
             , "  -h                 show this help"
             , ""
             , "Specify what to analyse using these command line options:"
             , "  -i inputfiles      parse these files (mandatory)"
             , "                       can both be verilog code and port specifications"
             , "                       note that for verilog modules with the same name"
             , "                       the last one given overwrites the former"
             , "  -m modulenames     include information on these modules"
             , "  -bb modulenames    treat these modules as black boxes (overwrites nobb)"
             , "  -nobb modulenames  do not treat these modules as black boxes"
             , ""
             , "Specify what information you wish to see:"] ++ [ "  -"<>l | l<-lst ] ++
             [ "\nThis program currently runs on one core, but may be parallelized in future versions."
             , "\n"
             ]

-- Todo(basj): parse verilog and ports as the same format, allow any number of files as input
main :: IO ()
main = do (commonFiles,argMap) <- parseArgs <$> getArgs
          inCase (Map.null argMap && null commonFiles) "Use -h for help"
          handles <- sequence (map (flip openFile ReadMode) (commonFiles ++ Map.findWithDefault [] "i" argMap))
          (moduleList, specList) <- concat2 <$> (sequence$ map parseInputAsVerilog handles)
          let blackBoxSet = Set.union (Set.difference (blackBoxModuleSet specList) (Set.fromList (map B.pack (Map.findWithDefault [] "nobb" argMap)))) (Set.fromList (map B.pack (Map.findWithDefault [] "bb" argMap)))
          let inspectedModules = map modName moduleList
          let inspectedModulesSet = Map.fromList [(B.pack m,()) | m<-Map.findWithDefault [] "m" argMap] -- assuming this is just one module. This way, combining the WithDAG needlessly with a traverse in modMapList is kind of OK.
          let modRes = processModules moduleList inspectedModules blackBoxSet :: forall s. Map.Map B.ByteString (WithDAG s (SimpleModule s))
          
          let forIO mp = (fmap (fmap (\v k -> B.putStrLn k >> return v)) mp)
          let bbRes     = processBlackBoxes (Set.toList blackBoxSet) modRes
          let propSpec  = processPropSpecs specList modRes
          
          let gauss, invariants, showSpec
                :: WithDAG t (InverseProps (WireReference t))
                -> WithDAG t B.ByteString
              gauss props      = showGaussRes . gaussianEliminate . runIdentity <$> (transFN =<< props)
              invariants props = showGaussRes . getInvariants . runIdentity  <$> (transFN =<< props)
              showSpec = (showBlackBoxes showWireReference =<<)
          let forest, xgraph
               :: WithDAG t (InverseProps (WireReference t))
               -> WithDAG t (IO (B.ByteString -> B.ByteString))
              forest props  = closeSolver showForest . getStructure <$> (transFN =<< props)
              xgraph props  = closeSolver showNetGraph . judgeForest . getStructure <$> (transFN =<< props)
          
          let options :: [( String, B.ByteString
                          , forall x. Map.Map B.ByteString (WithDAG x (B.ByteString -> IO B.ByteString)))]
              options =
               [ ("show"       , "show the top level wire values"           , forIO (fmap (join . fmap showModule) modRes))
               , ("showBB"     , "show the in/out-wires for all blackboxes" , forIO (fmap showSpec bbRes))
               , ("showProp"   , "show annotated properties symbolically"   , forIO (fmap showSpec propSpec))
               , ("gauss"      , "gauss elimination on properties"          , forIO (fmap gauss propSpec))
               , ("invariants" , "show invariants for queues"               , forIO (fmap invariants propSpec))
               , ("forest"     , "create an ascii-art forest of components" , fmap2 forest propSpec)
               , ("xgraph"     , "create an xMAS-like graph (for graphviz)" , fmap2 xgraph propSpec)
               , ("smt"        , "output SMT file to check for deadlocks"   , fmap (fmap (showSMT . buildSMT) . (\v -> (,) <$> (transFN =<< v) <*> (transFN =<< v))) propSpec)
               ]
          let processOptions :: [(String, B.ByteString, forall x. Map.Map B.ByteString (WithDAG x (B.ByteString -> IO B.ByteString)))] -> IO ()
              processOptions [] = return ()
              processOptions ((str,_,mp):as)
                = do case Map.lookup str argMap of
                       Just s -> sequence_ [v | v <- runX (modMapList s)]
                       Nothing -> return ()
                     processOptions as
                where modMapList :: [String] -> (forall x. WithDAG x [IO ()])
                      modMapList inspectables
                       = traverse (\(k,v) -> (B.putStrLn =<<) <$> (v <*> return k))
                                  (Map.toList$ Map.intersection mp (Map.union inspectedModulesSet (Map.fromList [(B.pack i,()) | i <- inspectables])))
          let makeList [] = [] -- for the -h (help) overview
              makeList ((str1,str2,_):rs) = B.pack (str1++take (15 - length str1) (repeat ' '))<>str2:makeList rs
          let superfluous = Set.toList$ Set.difference (Map.keysSet argMap) (Set.fromList $ [k|(k,_,_)<-options] ++ ["i","m","bb","nobb"])

          case Map.member "h" argMap || Map.member "?" argMap || Map.member "-?" argMap || Map.member "-help" argMap || Map.member "help" argMap of
            True  -> showHelp (makeList options)
            False -> do inCase (not$ null superfluous) ((if (null$ tail superfluous) then "Unknown option:" else "Unknown options:")
                                                        <> mconcat ["\n  -"<>B.pack k| k<-superfluous])
                        inCase (null moduleList) "No verilog modules were parsed. Add them via the argument -i verilogFile.v"
                        processOptions options
          exitSuccess


fmap2 :: (Functor dg, Applicative io, Functor f)
      => (dg a -> dg (io (b -> c)))
      -> f (dg a)
      -> f (dg (b -> io c))
fmap2 f s1 = fmap (fmap fmap3) (fmap f s1)

-- what is this called? Why is it not implemented in Applicative?
-- the interchange law requires these two to be equivalent:
-- u <*> pure y = pure ($ y) <*> u
-- which gives two possible implementations for fmap3
fmap3 :: Applicative io
      => io (b -> c) -> b -> io c
fmap3 f' b' = f' <*> pure b'

putLines :: [B.ByteString] -> IO ()
putLines listOfLines
 = B.putStrLn (interline listOfLines)
 where interline :: [B.ByteString] -> B.ByteString
       interline [] = B.pack ""
       interline [a] = a
       interline (s:ss) = s <> (B.pack "\n") <> interline ss

concat2 :: [([a], [a1])] -> ([a], [a1])
concat2 ((a,b):rst) = let (as,bs) = concat2 rst in (a++as,b++bs)
concat2 [] = ([],[])

inCase :: Bool -> B.ByteString -> IO ()
inCase True msg
 = do B.hPutStrLn stderr msg
      exitFailure
inCase False _ = return ()

parseArgs :: [String] -> ([String],Map.Map String [String])
parseArgs [] = ([],Map.empty)
parseArgs (a:as)
 = case a of
     ('-':rst) -> ([], Map.insertWith (++) rst comingArgs prevMap)
     x -> (x:comingArgs, prevMap)
 where (comingArgs,prevMap) = parseArgs as

{- keep these comments on the bottom, or change line 5

Note for cross compilation:
you can use llvm to generate c code: http://llvm.org/releases/3.1/docs/FAQ.html#translatecxx
and generate llvm code using haskell: https://downloads.haskell.org/~ghc/7.8.3/docs/html/users_guide/code-generators.html

Full system analysis including profile information: ghc --make VerilogAnalysis -O0 -prof -auto-all
time (./Main +RTS -p -h -RTS -m "top_de115" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v) > /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.symbolic
Full system analysis without profile information: ghc --make VerilogAnalysis -O0 / ghc --make VerilogAnalysis -O2
time (./Main -m "top_de115" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v) > /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.symbolic
Small sanity check:
time (./Main -m LessThan_32u_32u sub_2 "\look_ahead_xy(PORT_NUM=5,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0)" -bb VERIFIC_DFFRS dual_port_ram sdram -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v) > /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.symbolic
Just one router (including profile):
time (./Main +RTS -p -RTS -m "\router(VC_NUM_PER_PORT=4,BUFFER_NUM_PER_VC=4,PORT_NUM=5,PYLD_WIDTH=32,FLIT_TYPE_WIDTH=2,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,SW_OUTPUT_REGISTERED=0)" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v)
Just one router (no profile):
time (./Main -m "\router(VC_NUM_PER_PORT=4,BUFFER_NUM_PER_VC=4,PORT_NUM=5,PYLD_WIDTH=32,FLIT_TYPE_WIDTH=2,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,SW_OUTPUT_REGISTERED=0)" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v)
Just one switch:
time (./Main +RTS -p -RTS -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -m "\switch_in(SWITCH_LOCATION=1,VC_NUM_PER_PORT=4,PORT_NUM=5,PYLD_WIDTH=32,BUFFER_NUM_PER_VC=4,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,FLIT_TYPE_WIDTH=2,ENABLE_MIN_DEPTH_OUT=0)")

group black boxes using minisat for the router:
     Using profiling: time (ghc -prof -auto-all Main.hs) 8.7s
     time (./Main +RTS -p -RTS -m "\router(VC_NUM_PER_PORT=4,BUFFER_NUM_PER_VC=4,PORT_NUM=5,PYLD_WIDTH=32,FLIT_TYPE_WIDTH=2,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,SW_OUTPUT_REGISTERED=0)" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -showGroup)
     (takes 44 to 49s user time)

     No profiling: time (ghc Main.hs) 5.8s
     time (./Main -m "\router(VC_NUM_PER_PORT=4,BUFFER_NUM_PER_VC=4,PORT_NUM=5,PYLD_WIDTH=32,FLIT_TYPE_WIDTH=2,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,SW_OUTPUT_REGISTERED=0)" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -showGroup)
     (takes 27 to 33s user time)

find structure in the router, with annotated crossbar:
     time (./Main -m "\router(VC_NUM_PER_PORT=4,BUFFER_NUM_PER_VC=4,PORT_NUM=5,PYLD_WIDTH=32,FLIT_TYPE_WIDTH=2,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,SW_OUTPUT_REGISTERED=0)" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v crossbar.portConfig -structure -group)
     (takes 16s user time if the .portConfig overwrites correctly!)
Gauss on the entire thing:
     time (./Main -m top_de115 -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v crossbar.portConfig -gauss)
     (still a timeout.. seems to find a lot of dead transfers!)

find structure using groups:
     time (./Main +RTS -p -RTS -m "\router(VC_NUM_PER_PORT=4,BUFFER_NUM_PER_VC=4,PORT_NUM=5,PYLD_WIDTH=32,FLIT_TYPE_WIDTH=2,X_NODE_NUM=2,Y_NODE_NUM=2,SW_X_ADDR=0,SW_Y_ADDR=0,SW_OUTPUT_REGISTERED=0)" -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -structure -group)
     (takes about 1m20 user time, the structure found appears to be independent of whether the command line option -group is used)

just the top level symbolic values of everything:
     time (./Main +RTS -p -RTS -m top_de115 -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -show)
     (takes 5.8s to 6.7s user time)

bottom level symbolic values of everything (just report output size): ghc -prof -auto-all Main.hs
     time (./Main +RTS -p -RTS -m top_de115 -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -showProp | wc -c)
     (takes 8.1s to 8.9s user time, response: 23416258, or 23M)

     slightly optimised: time (ghc Main.hs)
     time (./Main -m top_de115 -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -showProp | wc -c)
     (takes 5.0s to 5.8s user time)

     fully optimised: time (ghc Main.hs -O2) 15.2s (rerun after turning prof on to get all libs to compile again)
     time (./Main -m top_de115 -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/nocrouterMPSOC/src/top_de115_before_write.v -showProp | wc -c)
     (takes 3.1s to 3.4s user time)

Two queue example, get structure:
     time (./Main -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/smallExamples/parallelQueues/twoQueues_before_write.v -structure -m twoQueues)
Cambridge router (bad example, I don't get what's going on here):
     time (./Main -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/Imran\ Shamim\ Cambridge\ router/router5x5_128b_before_write.v -m router5x5_128b -structure)
DSM:
     time (./Main -i portConfigs VERIFIC_DFFRS.v /Users/sjc/Documents/PhD/Eclipse/branches/bas/verilog_sources/crosspoint/DSM_before_write.v -m DSM -structure)

Get information about dependencies in this code:
     /Users/sjc/Library/Haskell/ghc-7.8.2/lib/graphmod-1.2.6/bin/graphmod Main.hs -s 2 | dot -Tpdf > modules.pdf
Hide the Boolean.Class module:
     /Users/sjc/Library/Haskell/ghc-7.8.2/lib/graphmod-1.2.6/bin/graphmod Main.hs -s 3 -r Boolean.Class | dot -Tpdf > modules.pdf

OpenSoc mesh:
     time (./Main -i OpenSoCFabric-master/CMesh_before_write.v -m OpenSoC_CMesh -i ./portConfigs VERIFIC_DFFRS.v -structure)
     (times out latelty -- took 2m14 user time, 2m36 wall clock time. Parsing or so takes quite some time, so it takes a while before something like "Looking for structure" appears. No structure found)
     time (./Main -i OpenSoCFabric-master/CMesh_before_write.v -m OpenSoC_CMesh -i ./portConfigs VERIFIC_DFFRS.v -gauss)
     (sum of product too large >10000 after 56s, and >50000 after 2m22)
-}
