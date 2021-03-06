{-# OPTIONS_GHC -Wall -Werror -fno-max-relevant-binds -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -Wmissing-local-signatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveTraversable, DeriveFoldable, DeriveFunctor, OverloadedStrings, ScopedTypeVariables, LambdaCase, NoImplicitPrelude #-}
-- | Add the X and Z and verilog-gate semantics
-- We do not export the constructor for BPair, so that we can change it and experiment with it
-- For instance: this version introduced explicit sharing using DAGs
-- a lot of functions are not used anywhere, and therefore not exported, but we might need them later (we needed them in the past at some point..)
-- so we ignore all these warnings for now..
module EchelonForms.SumOfProductForEchelon (showGaussRes,gaussianEliminate,getInvariants,SumOfProducts(..))
 where

import BooleanSymbolic.Class as BXZ (AtomToBoolean(..), ScopedWireName(..), Boolean(..))
import qualified Data.Set as Set
import qualified Data.Map as Map
import BaseLike.CustomPrelude as Prelude
import Data.Hashable
import Echelon.Echelon
import CommonDataTypes.TraverseProps (InverseProp(..),InverseProps(..),findQueues)
import EchelonForms.RingLogic
import Data.ByteString (intercalate)
import Data.Ratio (denominator, (%))
fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in Boolean/SumOfProductForEchelon.hs:\n  "++s)

runDuoNatBool :: forall c. DuoXZ (NaturalBoolean c) -> c
runDuoNatBool = runNaturalBoolean . runDuoXZ

-- note: ScopedWireName is optional, but putting it here helps against having to specify types in Main
gaussianEliminate :: InverseProps (DuoXZ (NaturalBoolean (SumOfProducts ScopedWireName))) -> GaussRes
gaussianEliminate lst
 = let setupForEchelon :: (ByteString, DuoXZ (NaturalBoolean (SumOfProducts ScopedWireName)))
                       -> (Map.Map (HashSet ScopedWireName) Int, Map.Map (Int, ByteString) Rational)
       setupForEchelon (bs,b) = ( runSOP . runDuoNatBool $ b
                                , Map.singleton (hash bs,bs) 1)
   in map makeInteger . echelonFilter . map setupForEchelon . concat . map oneBitBlackBox $ props
  where (InverseProps props) = lst
        oneBitBlackBox :: (InverseProp b) -> [(ByteString,b)]
        oneBitBlackBox (InverseProp nm' _ strs lst')
          = [ (initStr, b)
            | (nm,_,[b]) <- lst', let initStr = nm' <> mconcat (map (mappend ">") strs) <> "." <> nm
            ]

instance SingleHelper (SumOfProducts ScopedWireName) where
  singleHelper = SOP$ Map.fromList [(HashSet minBound (Set.singleton (ScopedWN minBound [] "Z")),1)]
  substituteHelper v' (SOP a'') = SOP$ substituteMap (ScopedWN minBound [] "Z") v'' a''
    where (NaturalBoolean (SOP v'')) = runIdentity$ BXZ.fromBool v'

getInvariants :: InverseProps (DuoXZ (NaturalBoolean (SumOfProducts ScopedWireName)))
              -> GaussRes
getInvariants iprops
 = map fst . echelonKeep . reverse . map (flip (,) (Map.empty :: Map.Map Int Rational) . makeInteger) . echelonFilter $ extendedInfo -- (trace (show extendedInfo) extendedInfo)
 where
  extraInfoMap :: Map.Map ScopedWireName
                          (Map.Map [ByteString]
                                   (Map.Map Int
                                            ( SumOfProducts ScopedWireName
                                            , SumOfProducts ScopedWireName)
                                   ,SumOfProducts ScopedWireName
                                   ,SumOfProducts ScopedWireName))
  extraInfoMap = Map.unions (concat extraInfo)
  extendedInfo = extendInfo Set.empty initialPart
  (initialPart, extraInfo)
   = Prelude.unzip
     [ ( (runSOP (ins </> outs), genName strs [])
       , [ Map.fromList
             [ (v, Map.singleton strs (Map.singleton i (runDuoNatBool inputBit,outputBit),ins,outs))
             | (((v,outputBit),inputBit),i) <- zip (zip outp inputData) [0..]
             ]
         | outp
             <- [ [case Map.keys (runSOP (runDuoNatBool b)) of
                    [HashSet _ v]
                      -> case Set.toList v of
                            [v'] -> (v', runDuoNatBool b)
                            _ -> fatal 116 "outputData in queue should be the name of an output-wire, not an expression"
                    _ -> fatal 114 ("outputData in queue should be the name of an output-wire, not an expression. It was:\n"++show b)
                  | b <- outputData] ]
         ] )
     | (strs,ins',outs') <- findQueues iprops
     , (ins ,inputData  ) <- map (first runDuoNatBool . snd) ins'
     , (outs,outputData ) <- map (first runDuoNatBool . snd) outs'
     ]
  extendInfo _ [] = []
  extendInfo handledBits (someInv@(mp,_):moreInvsSoFar)
   = someInv:extendInfo newHandledBits (moreInvsSoFar++newlyGenerated)
   where (newHandledBits,newlyGenerated) = generateFor handledBits (Map.keys mp)
  generateFor handledBits [] = (handledBits,[])
  generateFor handledBits ((HashSet _ k):ks)
   = ( foldr Set.insert newHandledBits addHB
     , generateItms ++ newlyGenerated
     )
   where setAsMap = Map.fromAscList (map (\v -> (v,())) (Set.toAscList k))
         relevantBits = Map.elems (Map.intersection extraInfoMap setAsMap)
         relevantMaps = Map.unionsWith myMerge relevantBits
         (addHB, generateItms)
          = unzip
            [ ( (scp,bitNrs)
              , ( runSOP (foldr (.*) ins (map fst bitVals) </> foldr (.*) outs (map snd bitVals))
                , genName scp (Set.toList bitNrs) )
              )
            | (scp,(inout,ins,outs)) <- Map.toList relevantMaps
            , let bitNrs = Map.keysSet inout
            , let bitVals = Map.elems inout
            , not (Set.member (scp,bitNrs) newHandledBits)
            ]
         myMerge :: (Map.Map Int a, t, t1)
                 -> (Map.Map Int a, t2, t3) -> (Map.Map Int a, t2, t3)
         myMerge (m1,_,_) (m2,ins,outs)
          = (Map.union m1 m2,ins,outs)
         (newHandledBits,newlyGenerated) = generateFor handledBits ks

genName :: [ByteString] -> [Int] -> Map.Map (Int, ByteString) Rational
genName strs []  = Map.singleton (hash strs,intercalate "/" strs) 1
genName strs lst = Map.singleton (hash strs,intercalate "/" strs <> "[" <> intercalate "," (map (pack . show) lst) <> "]") 1

instance Show (SumOfProducts ScopedWireName) where
  show x = "{"<>concat ["\n "++show k++": "++show v | (k,v)<-Map.toList (runSOP x)] <>"\n}"
instance Show (HashSet ScopedWireName) where
  show (HashSet _ s) = show (fmap show (toList s))

type GaussRes = [Map.Map (Int,ByteString) Integer]

makeInteger :: Map.Map (Int,ByteString) Rational -> Map.Map (Int,ByteString) Integer
makeInteger mp
 = let lcm' = foldr1 lcm (map denominator (Map.elems mp)) % 1
   in  map (ceiling . (*) lcm') mp

showInteger :: Integer -> ByteString
showInteger = pack . show
showGaussRes :: GaussRes -> ByteString
showGaussRes lst = mconcat [ (case negs of
                               [] -> "0"
                               _ -> intercalate " + " negs) <> " = " <>
                             (case poss of
                               [] -> "0"
                               _ -> intercalate " + " poss) <> "\n"
                           | mp <- map (Map.mapKeys snd) lst
                           , let gcd' = foldr1 gcd (Map.elems mp)
                           , let negs = [ (case nr' of
                                             1 -> ""
                                             _ -> showInteger nr' <> " * ") <> bs
                                        | (bs,nr) <- Map.toAscList mp
                                        , nr<0
                                        , let nr' = quot (0 - nr) gcd'
                                        ]
                           , let poss = [ (case nr' of
                                             1 -> ""
                                             _ -> showInteger nr' <> " * ") <> bs
                                        | (bs,nr) <- Map.toAscList mp
                                        , nr>0
                                        , let nr' = quot nr gcd'
                                        ]
                           ] <> "Number of invariants found: "<> (pack (show (Prelude.length lst)))

newtype SumOfProducts a = SOP {runSOP :: Map.Map (HashSet a) Int}

instance (Ord x, Hashable x)
 => AtomToBoolean x (Identity (DuoXZ (NaturalBoolean (SumOfProducts x)))) where
 toBoolean o = Identity . Duo . NaturalBoolean . SOP $ Map.singleton (mkHashSet (Set.singleton o)) (1::Int)

instance (Hashable x,Ord x) => Monoid (SumOfProducts x) where
  mappend (SOP a) (SOP b) = SOP (a .+. b)
  mempty = SOP spZero
instance (Hashable x,Ord x) => Abelian (SumOfProducts x) where
  (SOP a) </> (SOP b) = SOP (a .-. b)
  aTimes n (SOP m) = SOP$ n .*. m
instance (Hashable x,Ord x) => Ring (SumOfProducts x) where
  rOne = SOP spOne
  (.*) (SOP a) (SOP b)
   = SOP$ fromListMap [(a' <> b', ai*bi) | (a',ai) <- Map.toList a, (b',bi) <- Map.toList b]
substituteMap :: (Hashable x,Ord x) => x
              -> Map.Map (HashSet x) Int
              -> Map.Map (HashSet x) Int
              -> Map.Map (HashSet x) Int
substituteMap needle replaceBy haystack
 = fromListMap (concat [case Set.member needle (runHashSet k) of
                           True -> fillIn (mkHashSet$ Set.delete needle (runHashSet k)) v
                           False -> [(k,v)]
                       | (k,v) <- Map.toList haystack])
 where fillIn a v = [ (a <> a', v*ai) | (a',ai) <- Map.toList replaceBy ]
fromListMap :: forall x. Ord x => [(HashSet x, Int)] -> Map.Map (HashSet x) Int
fromListMap
 = foldlStrict ins Map.empty
   where foldlStrict :: (a -> b -> a) -> a -> [b] -> a
         foldlStrict f = go
           where
             go z []     = z
             go z (x:xs) = let z' = f z x in z' `seq` go z' xs
         ins :: Map.Map (HashSet x) Int -> (HashSet x, Int) -> Map.Map (HashSet x) Int
         ins mp (k,v) = Map.alter (\old -> case old of
                                      Nothing -> Just v
                                      Just w -> nonzero (+) k v w) k mp

nonzero :: (t1 -> t2 -> Int) -> t -> t1 -> t2 -> Maybe Int
nonzero f _ a b = if s == 0 then Nothing else Just s
              where s = f a b
(.-.), (.+.) :: forall t. (Ord t) => Map.Map t Int -> Map.Map t Int -> Map.Map t Int
a .+. b
 = if (Map.size a > 16*16384) || (Map.size b > 16*16384) then fatal 86 "sum of product too large!"
   else (Map.mergeWithKey (nonzero (+)     ) id id               a b)
a .-. b
 = if (Map.size a > 16*16384) || (Map.size b > 16*16384) then fatal 86 "sum of product too large!"
   else (Map.mergeWithKey (nonzero (flip subtract)) id (Map.map negate) a b)
(.*.) :: Int -> Map.Map k Int -> Map.Map k Int
(.*.) 0 _ = Map.empty
(.*.) n a = (Map.map (* n) a)
spOne, spZero :: Monoid m => Map.Map m Int
spZero = Map.empty
spOne  = Map.singleton mempty 1


data HashSet a = HashSet {hsHash :: Int, runHashSet :: Set.Set a} deriving (Ord,Eq)
mkHashSet :: (Hashable x, Ord x) => Set.Set x -> HashSet x
mkHashSet st = HashSet{hsHash=(sum (map hash (Set.toList st))), runHashSet=st}

instance (Hashable x,Ord x) => Monoid (HashSet x) where
  mappend hs1 hs2
    = mkHashSet (Set.union (runHashSet hs1) (runHashSet hs2))
  mempty = HashSet 0 Set.empty
