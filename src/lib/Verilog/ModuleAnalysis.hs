{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction #-}
{-# LANGUAGE RankNTypes, OverloadedStrings, ScopedTypeVariables, FlexibleContexts, NoImplicitPrelude #-}
-- I don't know what the -fwarn-auto-orphans switch does, but it creates an awful lot of warnings when -O or -O2 is used

{-|
Module      : Verilog.ModuleAnalysis
Copyright   : (c) Sebastiaan J C Joosten

This module should take a set of modules, and sets their interdependencies right.
It does the same for ports, using the set of interdependent modules.
-}
module Verilog.ModuleAnalysis ( processModules
                              , showModule
                              , SimpleModule(..)
                              , prettyshow

                              -- from Processor:
                              , variablesInExpr
                              , getBitsChangeBPart
                              , modName
                              ) where
-- import Verilog.Syntax
import Verilog.Processor (processModule, WireValue(..), VerilogWireType(..), modName, VerilogModule, Instantiation(INST), GetBitsType, getBit2, getBitsChangeBPart, variablesInExpr)
import qualified Data.Map as Map -- (Map,unionsWith,alter,empty,insert, lookup,fromListWith,elems,map,keys,(!),union,mapWithKey,fromList,toList)
import qualified Data.Vector as Vector (Vector,fromList,toList,(!))
import Control.Applicative
import qualified Data.Set as Set
import BooleanSymbolic.CalcX -- canonizeBoolean / runX, among others
import Data.Foldable
import BaseLike.CustomPrelude

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in Verilog.ModuleAnalysis:\n  "++s)

fatalDuplicates :: String -> a -> a -> a
fatalDuplicates s = fatal 35 $ "Duplicate map keys!\n  "++s

-- | TODO
data SimpleModule s
  = SimpleModule ByteString -- module name
                 (Map.Map ScopedWireName (WireReference s)) -- simplified wire values (no names)
                 (Map.Map ScopedWireName (WireReference s)) -- intermediate wire values (not exported)
                 (GetBitsType ScopedWireName ()) -- lookup for names
                 [WithDAG s (Instantiation (Map.Map ScopedWireName (WireReference s)))] -- a map that turns wires internal to the instantiation (unscoped) into those external to the instantiation

-- | TODO
showModule :: SimpleModule t
           -> WithDAG t ByteString
showModule (SimpleModule str exposed inside _ _)
 = (\ exposedList insideList
      -> ("Module " <> str <> "\n" <>
          mconcat ["  "<> varName<>" := "<> vl<>" ;\n" | (varName,vl) <- exposedList] <>
          "  -----------------------\n" <>
          mconcat ["  "<> varName<>" := "<> vl<>" ;\n" | (varName,vl) <- insideList])
     ) <$> castMap exposed <*> castMap inside
  where castPair (a,b) = (,) (showScopedWireName a) <$> showWireReference b
        castMap mp = sequenceA (map castPair (Map.toList mp))

-- | TODO
processModules :: forall s. [VerilogModule] -> [ByteString] -> Set.Set ByteString -> Map.Map ByteString (WithDAG s (SimpleModule s))
processModules allModules interestingModules blackBoxes
  = simplifyNextModule Map.empty interestingModules
  where
    -- keeping the processed modules in a map, to make sure that we calculate the bulk of it as few times as possible. Note that the monadic actions get executed again anyways, but this should add a bit of efficiency.
    processedModuleMap :: forall tp1 tp2. Map.Map ByteString
                                  ( WithDAG tp1 ( Map.Map (ByteString, Maybe Int) (ScopedWireName, WireValue (WireReference tp1), VerilogWireType)
                                                      , GetBitsType ScopedWireName (WithDAG tp1 (WireReference tp1)))
                                  , Vector.Vector (Instantiation (WithDAG tp2 [((ByteString, Int), WireReference tp2)]))
                                  )
    processedModuleMap = Map.fromList (map processModule' allModules)
      where processModule' vmodule
              = processModule (Set.member (modName vmodule) blackBoxes) vmodule
    -- this is a plain fold, but we need the type annotation, so the fold is written out
    simplifyNextModule :: forall s0. (forall s1. Map.Map ByteString (WithDAG s1 (SimpleModule s1)))
                       -> [ByteString] -> Map.Map ByteString (WithDAG s0 (SimpleModule s0))
    simplifyNextModule mp (nm:rst) = simplifyNextModule (snd (getNextModule nm mp)) rst
    simplifyNextModule mp []       = mp

    getNextModule :: forall s1 t. ByteString
                  -> (forall s0. Map.Map ByteString (WithDAG s0 (SimpleModule s0)))
                  -> ( WithDAG s1 (SimpleModule s1)
                     , Map.Map ByteString (WithDAG t (SimpleModule t))
                     )
    getNextModule curModule mp
     = case Map.lookup curModule mp of
         Nothing -> let curProcessed = case Map.lookup curModule processedModuleMap of
                                    Nothing -> fatal 316 ("The verilog module "++show curModule++" is not among the parsed modules!")
                                    Just v -> v
                        (instantiations, newmap) = getInstantiations mp (Vector.toList$ snd curProcessed)
                        fullModule :: forall tp. (WithDAG tp (SimpleModule tp))
                        fullModule
                         = do (mpr,inOutValues) <- selfSimplify twoMaps
                              let typeAnnotatedMap :: (forall x. [Instantiation (WithDAG x ( Map.Map ScopedWireName (WireReference x)
                                                                                                 , Map.Map ScopedWireName (WireReference x)
                                                                                                 , GetBitsType ScopedWireName ())
                                                                                )])
                                                   -> ( [WithDAG tp (Instantiation (Map.Map ScopedWireName (WireReference tp)))]
                                                      )
                                  typeAnnotatedMap inList
                                    = case inList of
                                       [] -> []
                                       _ -> let (INST a b trp:as) = inList -- this is why uni-patternmatch warnings have been turned off: pattern matching in the case part does not generalize the type (doing that in "let" does)
                                            in  (INST a b <$> (canonizeBoolean (do{(_,c,_) <- trp;return c}) id mpr)
                                                ):typeAnnotatedMap as
                              let instList = typeAnnotatedMap instantiations
                              return (SimpleModule curModule inOutValues mpr (runX getBitsWithMap) instList)
                         where
                          twoMaps = do (wires, _) <- fst curProcessed -- getBits is used elsewhere, because of the type
                                       let keepWires = filter (\(_,_,c) -> c /= Wire) (Map.elems wires)
                                       let reduceWires = filter (\(_,_,c) -> c `elem` [Output,Wire]) (Map.elems wires)
                                       vec <- (Vector.fromList <$> traverse (\(INST a b c) -> INST a b <$> c) instantiations)
                                       let fillIn = fillInInstantiations vec
                                       reduceMap <- sequenceA$ Map.fromList (map fillIn reduceWires)
                                       mpKeep <- sequenceA$ Map.fromList (map fillIn keepWires)
                                       return (reduceMap, mpKeep)
                          getBitsWithMap = do (_,getBits) <- fst curProcessed
                                              return (getBitsChangeBPart (\_ _ -> ()
                                                                         ) getBits)
                    in  ( fullModule , Map.insert curModule fullModule newmap )
         Just v -> (v, mp)
     where
         -- here the local variables get values from the instantiated modules
         fillInInstantiations :: forall tp a t3.
                                 (Vector.Vector (Instantiation ( Map.Map ScopedWireName (WireReference tp)
                                                               , Map.Map ScopedWireName (WireReference tp)
                                                               , GetBitsType ScopedWireName ())))
                              -> (a, WireValue (WireReference tp), t3)
                              -> (a, WithDAG tp (WireReference tp))
         fillInInstantiations instantiations (atom, WV val insts, _)
          = (atom, combineListC =<< ((val:) <$> traverse concreteInstantiation insts))
          where concreteInstantiation :: (Int, (ByteString, Int)) -> WithDAG tp (WireReference tp)
                concreteInstantiation (nr, (k,v))
                 = do let (INST _modnm _inm (aMp,_,gbMp)) = (Vector.!) instantiations nr
                      case Map.lookup (getBit2' gbMp k v) aMp of
                            Just r -> return r
                            -- If a wire is not set, maybe it came from a black box and we need to fix Processor
                            Nothing -> fatal 129 "Came from black box!" -- kvAtm _inm k v
         -- kvAtm :: ByteString -> ByteString -> Int -> m b
         -- kvAtm inm k i = fromOriginal (pack (unpack inm ++":"++unpack k ++ ":"++ show i))

    getInstantiations :: forall s0 t.
                         ( forall s2. Map.Map ByteString (WithDAG s2 (SimpleModule s2))) -- modules treated so far
                      -> ( forall t1. [ Instantiation (WithDAG t1 [((ByteString, Int), (WireReference t1))])] ) -- try to instantiate these modules
                      -> ( [ Instantiation (WithDAG t ( Map.Map     ScopedWireName (WireReference t) -- internal wire values, scoped
                                                      , Map.Map     ScopedWireName (WireReference t) -- mapping between internal and external wires
                                                      , GetBitsType ScopedWireName () -- port wires
                                                      ))
                                           ]
                         , Map.Map ByteString (WithDAG s0 (SimpleModule s0))
                         )
    getInstantiations mp [] = ([],mp)
    getInstantiations simpleModLookup insts
     = let wireMap :: forall t1. WithDAG t1 [((ByteString, Int), WireReference t1)]
           (INST modName' instName wireMap) = head insts
           nextModule :: forall s1. (WithDAG s1 (SimpleModule s1))
           newSML :: forall s1. Map.Map ByteString (WithDAG s1 (SimpleModule s1))
           (nextModule, newSML) = getNextModule modName' simpleModLookup
           restInst :: [ Instantiation (WithDAG t ( Map.Map ScopedWireName (WireReference t)
                                                  , Map.Map ScopedWireName (WireReference t)
                                                  , GetBitsType ScopedWireName ()
                                                  )) ]
           restSML :: Map.Map ByteString (WithDAG s0 (SimpleModule s0))
           (restInst, restSML) = getInstantiations newSML (tail insts)
           getBitsNoBPair :: GetBitsType ScopedWireName ()
           getBitsNoBPair = runX$ do SimpleModule _ _ _ getBitLocal _ <- nextModule
                                     return (getBitsChangeBPart (\_ _ -> ()) getBitLocal)
           filledInWireMap :: forall t1. WithDAG t1 (Map.Map ScopedWireName (WireReference t1))
           filledInWireMap = do wireMap' <- wireMap
                                return$ Map.fromListWith (fatalDuplicates "note-170")
                                                         [ (getBit2' getBitsNoBPair bs i, b)
                                                         | ((bs,i),b) <- wireMap' ]
           triple :: WithDAG t
                     ( Map.Map ScopedWireName (WireReference t)
                     , Map.Map ScopedWireName (WireReference t)
                     , GetBitsType ScopedWireName ())
           triple = do gbWireMap <- filledInWireMap
                       newModMap <- canonizeBoolean (do SimpleModule _ modMap _modMapInternal _ _ <- nextModule
                                                        return modMap -- (Map.unionWith (fatal 163 "Duplicate wire names") modMap _modMapInternal)
                                                    ) (scopeScopedWireName instName) gbWireMap
                       -- MA (state (\st -> trace ("Creating triple for "++show instName++" ("++show modName'++")\n"++prettyshow st++"\nWireMap:"++show gbWireMap++"\nModMap:"++show newModMap) ((),st)))
                       return (newModMap, gbWireMap, getBitsNoBPair)
       in ( (INST modName' instName triple) : restInst
          , restSML
          )

-- | TODO
prettyshow :: (Show a, Foldable t) => t a -> [Char]
prettyshow s
 = concat ["\n"++show i++": "++show v | (i,v) <- zip [(0::Int)..] (toList s)]

getBit2' :: GetBitsType ScopedWireName b -> ByteString -> Int -> ScopedWireName
getBit2' gb bs mb = fst (getBit2 gb bs (Just mb))

-- dist/build/verilogAndPorts/verilogAndPorts VERIFIC_DFFRS.v OpenSoCFabric-master/OpenSoC_CMesh_before_write.v -m add_1u_1u -show +RTS -xc -RTS
-- dist/build/verilogAndPorts/verilogAndPorts VERIFIC_DFFRS.v OpenSoCFabric-master/OpenSoC_CMesh_before_write.v -m VERIFIC_FADD -show
-- dist/build/verilogAndPorts/verilogAndPorts VERIFIC_DFFRS.v OpenSoCFabric-master/OpenSoC_CMesh_before_write.v -m add_4u_4u -show +RTS -xc -RTS
