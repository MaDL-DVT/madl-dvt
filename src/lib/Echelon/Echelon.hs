{-# OPTIONS_GHC -Wall -Werror -fno-max-relevant-binds -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -Wmissing-local-signatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveTraversable, DeriveFoldable, DeriveFunctor, OverloadedStrings, ScopedTypeVariables, LambdaCase, NoImplicitPrelude #-}

{-|
Module      : Echelon.Echelon
Copyright   : (c) Sebastiaan J C Joosten
-}
module Echelon.Echelon (echelonFilter, echelonKeep) where -- ik moet aangeven wat ik wil exporteren om te voorkomen dat "fatal" en "debug" geexporteerd worden (niet dat dat nu veel uit maakt, maar het kan name-collisions in andere programma's veroorzaken)
import qualified Data.Map as Map
import System.Random
import Data.List (nub)
import BaseLike.CustomPrelude as Prelude
-- import Debug.Trace

debug :: Bool
debug = False -- deze definitie kun je verstoppen in een aparte library, zodat je makkelijk het debuggen van alles aan of uit kan zetten

randomSeed :: Int
randomSeed = 0

-- door de beschrijving van deze functie in elk bestand opnieuw te zetten (repeat yourself), kun je sneller terugvinden in welk bestand de fout gegenereerd wordt. Ik kies als waarde voor n altijd het regelnummer, zodat ik een goede kans heb dat die waarde uniek is, maar verander dat getal daarna niet meer, zodat er bij dezelfde fout steeds hetzelfde nummer hoort (tijdens verschillende versies).
fatal :: Int -> String -> a
fatal n s = error ("Fatal error number "++show n++" in Boolean/Echelon.hs:\n" ++ s)

-- | Get the right side of matrix rows where the left side is empty
echelonFilter :: (Ord k1, Ord k, Integral a1, Fractional a, Eq a, Real a) =>
                       [(Map.Map k1 a1, Map.Map k a)] -> [Map.Map k a]
echelonFilter lst
 = filterNonzeros (echelonKeep lst)
  where filterNonzeros :: [(Map.Map k a, a1)] -> [a1]
        filterNonzeros ((a,v):rst) = (if Map.null a then (:) v else id) (filterNonzeros rst)
        filterNonzeros [] = []

-- | Get the entire resulting matrix
-- Als debug==False, staat hieronder "echelonKeep lst = res"
echelonKeep :: (Ord k, Ord k1, Integral a1, Fractional a, Eq a, Real a) =>
                     [(Map.Map k1 a1, Map.Map k a)] -> [(Map.Map k1 a1, Map.Map k a)]
echelonKeep lst
 = (if debug then testZeros lst "the input for echelonKeep"
                . testZeros res "the output of echelonKeep"
                . testSatisfy lst lstSat "There is probably an error in the testSatisfy or findSatisfy function" -- als de fout in de testprocedure zelf zit zoek je je rot.
                . testSatisfy res resSat "There is probably an error in the testSatisfy or findSatisfy function"
                . testSatisfy res lstSat "A solution to the input system, turned out not to be a solution to the output system"
                . testSatisfy lst resSat "A solution to the output system, turned out not to be a solution to the input system"
                else id) res
 where res = echelonKeep' lst
       lstSat = findSatisfy randomSeed lst
       resSat = findSatisfy randomSeed res

testSatisfy :: (Ord b, Ord a2, Eq a3, Fractional a3, Integral a1, Real v) =>
                     [(Map.Map a2 a1, Map.Map b a3)] -> Map.Map (Either a2 b) v -> String -> x -> x
testSatisfy lst solution errString
 = if and [sum ( [fromRational (toRational$ Map.findWithDefault notFound1 (Left  k) solution) * fromIntegral v | (k,v) <- Map.toList m1] ++
                 [fromRational (toRational$ Map.findWithDefault notFound2 (Right k) solution) * v | (k,v) <- Map.toList m2]
               ) == 0 | (m1,m2)<-lst ]
   then id else fatal 43 ("testSatisfy found an error in the solution.\n"++errString++"\n\nSolution vector was:"++show (map toRational$ Map.elems solution))
 where notFound1,notFound2 :: forall a. a
       notFound1 = fatal 44 ("Incomplete solution provided to testSatisfy.\n"++errString)
       notFound2 = fatal 45 ("Incomplete solution provided to testSatisfy.\n"++errString)

findSatisfy :: (Num t1, Fractional t1, Ord a, Ord b, Eq t1, Integral a1)
            => Int -> [(Map.Map a a1, Map.Map b t1)] -> Map.Map (Either a b) t1
findSatisfy seed lst
 = valueAssignments (mkStdGen seed)
                    allKeys
                    Map.empty
 where fullMatrix = [ Map.fromListWith (fatal 55 "Strange duplicates are arising.. check your instance of Ord, it might be wrong")
                    $ [(Left k,fromIntegral v) | (k,v)<-Map.toList m1] ++ [(Right k,v) | (k,v) <- Map.toList m2] | (m1,m2) <- lst ]
       allKeys = Map.keys (Map.unions fullMatrix)

       valueAssignments _ [] res = res
       valueAssignments randGen (k:restKeys) res
        = case nub forcedValues of
            []  -> valueAssignments newRandGen restKeys (Map.insert k (fromInteger randNr) res)
            [a] -> valueAssignments randGen    restKeys (Map.insert k a                    res)
            _   -> -- throw away the previously built part of the solution, because it has lead to a contradiction. Note: this is bad for testing, but unfortunately, it can happen
                   valueAssignments randGen    restKeys (Map.insert k 0 (Map.map (const 0) res))
        where ~(randNr, newRandGen) = random (randGen::StdGen)
              forcedValues = [ - sum [ case Map.lookup k'' res of
                                          Nothing -> if k''==k then 0 else fatal 67 "Could not find an element in a map. Check your Ord instance, it could be wrong."
                                          Just m -> m * v''
                                     | (k'',v'') <- Map.toList row ] / v'
                             | row <- fullMatrix -- check whether this row forces the value of k. It does so when k is the last value in the row.
                             , [(k',v')] <- [Map.toList (Map.difference row res)]
                             , k'==k ]

echelonKeep' :: (Ord k1, Ord k, Integral a1, Fractional a, Eq a) =>
                       [(Map.Map k1 a1, Map.Map k a)] -> [(Map.Map k1 a1, Map.Map k a)]
echelonKeep' ((a,v):rst)
 = (a,v):echelonKeep' (if (Map.null a) then rst else map sweep rst)
  where (ll,ht) = Map.findMin a
        sweep (vals,nms)
         = case seq nms$Map.lookup ll vals of
              Nothing -> (vals,nms)
              Just f' -> (if abs f' == abs ht then id else normalize)
                         (let commonFactor = gcd f' ht
                              combine :: Num a => a -> a -> a
                              combine x y = x*(-fromIntegral (quot ht commonFactor))+y*(fromIntegral (quot f' commonFactor))
                          in (mergeB combine vals a, mergeB combine nms v))
echelonKeep' [] = []

testZeros :: (Integral a1, Fractional a, Eq a) => [(Map.Map k1 a1, Map.Map k a)] -> String -> x -> x
testZeros lst s = if (and [ and (map (0 /=) (Map.elems m1)) &&
                            and (map (0 /=) (Map.elems m2))
                          | (m1,m2) <- lst ]) then id
                  else fatal 37 ("Zero values found in "++s)

mergeB :: (Ord k, Num b, Num c, Num a, Eq c) =>
       (a -> b -> c) -> Map.Map k a -> Map.Map k b -> Map.Map k c
mergeB f = Map.mergeWithKey (nonzero f) (Map.map (flip f 0)) (Map.map (f 0))
normalize :: (Integral a, Fractional b) =>
          (Map.Map k a, Map.Map k1 b) -> (Map.Map k a, Map.Map k1 b)
normalize o@(p1,p2)
  = case Map.foldr gcd 0 p1 of
      0 -> o
      1 -> o
      factor -> (Map.map (\f -> quot f factor) p1,Map.map (\f -> f / (fromIntegral factor)) p2)
nonzero :: (Num a, Eq a) => (t1 -> t2 -> a) -> t -> t1 -> t2 -> Maybe a
nonzero f _ a b = if s == 0 then Nothing else Just s
             where s = f a b
