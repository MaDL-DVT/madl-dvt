{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverloadedStrings, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, RankNTypes, NoImplicitPrelude, ImpredicativeTypes #-}
-- I don't know what the -fwarn-auto-orphans switch does, but it creates an awful lot of warnings when -O or -O2 is used

{-|
Module      : Verilog.PortsAndBlackBoxes
Copyright   : (c) Sebastiaan J C Joosten

This module should take a set of modules, and sets their interdependencies right.
It does the same for ports, using the set of interdependent modules.
-}
module Verilog.PortsAndBlackBoxes ( processBlackBoxes
                         , showBlackBoxes
                         , processPropSpecs
                         , blackBoxModuleSet
                         ) where
import CommonDataTypes.TraverseProps
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.ByteString as B  (ByteString, length)
import Data.ByteString.Char8 as C (replicate)
import qualified Data.Vector as Vector (toList)
-- import Boolean.Class (Instantiatable(..), BooleanXZ())
import Control.Applicative
import Data.Foldable
import Data.Traversable
import BooleanSymbolic.CalcX
import Verilog.ModuleAnalysis (SimpleModule(..), getBitsChangeBPart, variablesInExpr)
import BaseLike.CustomPrelude as Prelude
import Unsafe.Coerce
-- import Debug.Trace

-- | TODO
blackBoxModuleSet :: [VerilogPort] -> Set.Set B.ByteString
blackBoxModuleSet ports
 = Set.fromList [nm | VerilogPort _ stmts <- ports, PortModuleReference _ nm <- stmts]

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in Verilog/PortsAndBlackBoxes.hs:\n  "++s)


-- | TODO
showBlackBoxes :: Applicative m => (b -> m ByteString) -> (InverseProps b) -> m ByteString
showBlackBoxes f (InverseProps props) = mconcat <$> (traverse (((<>) "\n" <$>) . showBlackBox f) props)
showBlackBox :: Applicative m => (b -> m ByteString) -> (InverseProp b) -> m ByteString
showBlackBox f (InverseProp nm' _ strs lst')
 = ((nm' <> mconcat (map (mappend " in ") (reverse strs)) <> "\n") <>)
   <$> (mconcat <$> (sequenceA [ (<> ";\n") <$>
                                 case bs of
                                   [] -> pure (initStr <> "{}")
                                   (a:lst) -> liftA2 (<>) ((initStr <>) <$> f a)
                                                          (mconcat <$> sequenceA [ (("\n" <> C.replicate (B.length initStr) ' ') <>) <$> f b | b<-lst])
                               | (nm,_,bs) <- lst', let initStr = "  "<> nm <> " := " ]))

-- | TODO
processPropSpecs :: forall s. [VerilogPort]
                -> (forall tp. Map.Map ByteString (WithDAG tp (SimpleModule tp)))
                -> Map.Map ByteString
                           (WithDAG s (InverseProps (WireReference s)))
processPropSpecs ports mp
  = propertiesInMods (Map.unionsWith (liftA2 appendProps) (map processProp ports)) mp
  where
   parsePortProps mp' vls
    = map (parsePortProp mp') vls
   parsePortProp mp' (Right v)
    = Map.findWithDefault (fatal 57 ("Annotate is missing a value for "++show v)) v mp'
   parsePortProp _ (Left v) = v
   processProp :: forall tp. VerilogPort
               -> Map.Map ByteString (WithDAG tp (InverseProps (WireReference tp)))
   processProp (VerilogPort (PD desc) stmts)
    = Map.fromListWith (liftA2 appendProps)
      [ ( modnm
        , do portExprs <- sequenceA [ (\v -> (exprName, parsePortProps modArgs portArgs, v)) <$> sequenceA (map snd (variablesInExpr getBits expr))
                                    | PortExpression (PP exprName) portArgs expr <- stmts ]
             return$ InverseProps [InverseProp desc modArgs [] portExprs]
        )
      | PortModuleReference modArgs modnm <- stmts
      , getBits <- runX$ case Map.lookup modnm mp of
                              Nothing -> return []
                              Just modr -> do (SimpleModule _ _ _ getBits' _) <- modr
                                              return [getBitsChangeBPart (\a _ -> toBoolean a) getBits']
      ]

-- | TODO
processBlackBoxes :: forall s.
                   [ByteString] -- these are the black boxes
                -> (forall tp. Map.Map ByteString (WithDAG tp (SimpleModule tp)))
                -> Map.Map ByteString
                           (WithDAG s (InverseProps (WireReference s)))
processBlackBoxes blackBoxes simplifiedModules
 = propertiesInMods bbModules simplifiedModules
 where
   bbModules :: Map.Map ByteString
                        (WithDAG tp (InverseProps (WireReference tp)))
   bbModules
     = Map.fromList
       [ ( blackBoxName
         , case Map.lookup blackBoxName simplifiedModules of
             Nothing -> return (InverseProps [])
             Just v -> do (SimpleModule _ values _ getbits _) <- v
                          inoutVals <- sequenceA [ (\exprs -> (bitName, [], exprs)) <$> sequenceA listOfValidBits
                                                 | (bitName, (bitVec, _orderedLittleOrBigEndian)) <- Map.toList getbits
                                                 , let listOfValidBits = [toBoolean atom | (atom,()) <- Vector.toList bitVec -- just the values from the atom value pairs
                                                                            -- filter out wires that are marked as input
                                                                            , case Map.lookup atom values of
                                                                                Nothing -> False
                                                                                Just _ -> True
                                                                                ]
                                                 , not (Prelude.null listOfValidBits)
                                                 ]
                          return$ InverseProps
                                  [ InverseProp blackBoxName
                                                Map.empty
                                                [] -- list of instance-names
                                                inoutVals
                                  ]
         )
       | blackBoxName <- blackBoxes ]

myCoerce :: forall x y a b s t f.
            (((a x (s (t x))) -> (b y (s (t y)))) -> f (a x (s (t x))) -> f (b y (s (t y))))
         -> (forall y2. (forall y1. a y1 (s (t y1))) -> b y2 (s (t y2)))
         -> f (a x (s (t x))) -> f (b y (s (t y)))
myCoerce mapFn thing res
 = mapFn (unsafeCoerce thing) res

propertiesInMods :: forall s.
                    (forall tp. Map.Map ByteString
                                        (WithDAG tp (InverseProps (WireReference tp))))
                 -> (forall tp. Map.Map ByteString
                                        (WithDAG tp (SimpleModule tp)))
                 -> Map.Map ByteString
                            (WithDAG s (InverseProps (WireReference s)))
propertiesInMods bbModules simplifiedModules
 = myCoerce Map.map simplify filledModules
 where
   simplify :: forall s1. (forall tp. (WithDAG tp (InverseProps (WireReference tp))))
            -> WithDAG s1 (InverseProps (WireReference s1))
   simplify ips = snd <$> (selfSimplify ((,) Map.empty <$> ips))
   filledModules :: (forall tp.
                     Map.Map ByteString
                       (WithDAG tp (InverseProps (WireReference tp))))
   filledModules = Map.union bbModules (Map.map fillModule simplifiedModules)
   scopeProp nm (InverseProp a v lst b) = InverseProp a v (nm:lst) b
   eachProp f (InverseProps x) = InverseProps (map f x)
   fillModule :: forall tp.
                 WithDAG tp (SimpleModule tp)
              -> WithDAG tp (InverseProps (WireReference tp))
   fillModule smod
    = do (SimpleModule _ _ _ _ insts) <- smod
         propsInMod <- sequenceA [ do (INST modNm instNm instVals) <- inst
                                      let filledModule = (case Map.lookup modNm filledModules of
                                                            Nothing -> fatal 190 "Could not find module in map"
                                                            Just v ->  eachProp (scopeProp instNm) <$> v)
                                      canonizeBoolean filledModule (scopeScopedWireName instNm) instVals
                                 | inst <- insts] :: WithDAG tp [InverseProps (WireReference tp)]
         return$ InverseProps (concat [props | InverseProps props <- propsInMod])
