{-# LANGUAGE OverloadedStrings, ScopedTypeVariables#-}
module Madl.MetaIslands where

import Madl.Network
import Madl.MsgTypes
import Madl.Islands
import Utils.Text
import Data.Maybe
import Control.Monad (replicateM)
import qualified Data.List as L
--import qualified Data.Sequence as Seq
import qualified Data.Set as S
import qualified Data.IntMap as IM
import qualified Data.Bimap as BM

data CompType = Src | Snk | Q | Frk | CJ | FJ | Swtch | Mrg deriving (Show,Eq,Ord)

data FunComp = Arg ComponentID | Fun Int [FunComp] deriving (Show,Eq,Ord)

data MetaIslands = MetaIslands [String] Int [[Int]] (BM.Bimap Int MFunctionDisj, BM.Bimap Int MFunctionBool) [MetaIsle] deriving (Show,Eq)

data MetaIsle = MetaIsle Int [ChannelID] [MetaComp] [MetaComp] deriving (Show,Eq,Ord)

data MetaComp = MetaComp ComponentID FunComp CompType IOColor Capacity deriving (Show,Eq,Ord)

data Capacity = Capacity Int deriving (Show,Eq,Ord)

data IOColor = IOColor (S.Set Color) deriving (Show,Eq,Ord)

noquot :: String -> String
noquot str = filter (\x -> x /= '\"') str

--gets type and field names from a network
typeFieldGetter :: ColoredNetwork -> [String]
typeFieldGetter net = filter (\x -> x /= "") $ map (\x -> noquot $ show x) $ L.nub (networkTypes net ++ networkStructFields net) 

funPredMap :: ColoredNetwork -> (BM.Bimap Int MFunctionDisj, BM.Bimap Int MFunctionBool)
funPredMap net = let funs = L.nub . map (\(_,x) -> let (Function _ f _) = x in f) $ getAllFunctionsWithID net
                     preds = L.nub . L.concat . map (\(_,x) -> case x of
                                                                 Switch _ ps -> ps
                                                                 FControlJoin _ p -> [p]
                                                                 _ -> error "incorrect primitive")
                             $ (getAllSwitchesWithID net) ++ (getAllFJoinsWithID net)
                     fkv = zip [i | i <- [0..length funs]] funs
                     pkv = zip [i | i <- [0..length preds]] preds
                 in (BM.fromList fkv, BM.fromList pkv)

testHead :: String -> [a] -> a
testHead s [] = error ("empty list: " ++ s)
testHead _ (x:_) = x

funcProp :: ColoredNetwork -> (Island a) -> (BM.Bimap Int MFunctionDisj, BM.Bimap Int MFunctionBool) -> [(ChannelID, FunComp)]
funcProp net isl (fm,pm) = let ins = getIslIns isl net
                               islChans = islToChanIDs isl
                               s = map (\x -> (x,Arg (getInitiator net x))) ins
                           in funcProp' s islChans s
  where funcProp' :: [(ChannelID,FunComp)] -> [ChannelID] -> [(ChannelID,FunComp)] -> [(ChannelID,FunComp)]
        funcProp' [] _ res = res
        funcProp' ((x,x'):xs) ic res = let comp = getTarget net x
                                           compIns = L.intersect (getInChannels net comp) ic
                                           compOuts = getOutChannels net comp
                                           checkIns = S.isSubsetOf (S.fromList compIns) (S.fromList $ map (\(z,_) -> z) res)
                                           checkOuts = L.intersect compOuts ic /= []
                                       in if (not checkIns || not checkOuts)
                                          then funcProp' xs ic res
                                          else case getComponent net comp of
                                                 (Function _ f _) -> let res' = filter (\(z,_) -> z /= (head compIns)) res
                                                                         compOut = head compOuts
                                                                         res'' = ((compOut,Fun (fm BM.!> f) [x']):res')
                                                                     in funcProp' res'' ic res''
                                                 (Fork _) -> let res' = filter (\(z,_) -> z /= (head compIns)) res
                                                                 compOuts' = map (\z -> (z,x')) compOuts
                                                                 res'' = compOuts' ++ res'
                                                             in funcProp' res'' ic res''
                                                 (ControlJoin _) -> let res' = filter (\(z,_) -> z /= (head compIns)) res
                                                                        compOut = head compOuts
                                                                        res'' = ((compOut,x'):res')
                                                                    in funcProp' res'' ic res''
                                                 (FControlJoin _ p) -> let res' = filter (\(z,_) -> z /= (head compIns)) res
                                                                           compOut = head compOuts
                                                                           fprop = map (\z -> snd z)
                                                                                   $ filter (\(z,_) -> L.elem z compIns) res
                                                                           res'' = ((compOut,Fun (pm BM.!> p) fprop):res')
                                                                       in funcProp' res'' ic res''
                                                 (Switch _ ps) -> let res' = filter (\(z,_) -> z /= (head compIns)) res
                                                                      fprop = map (\z ->
                                                                                     (z, Fun (pm BM.!> (ps !!
                                                                                                        (fromJust
                                                                                                         (L.elemIndex z compOuts))))
                                                                                         [x'])) compOuts
                                                                      res'' = fprop ++ res'
                                                                  in funcProp' res'' ic res''
                                                 (Merge _) -> let res' = filter (\(z,_) -> z /= (head (L.intersect compIns ic))) res
                                                                  compOut = head $ compOuts
                                                                  res'' = ((compOut,x'):res')
                                                              in funcProp' res'' ic res''
                                                 _ -> error "wrong component"

--gets all the island's merges
isleMerges :: ColoredNetwork -> (Island a) -> [ComponentID]
isleMerges net isl = let chans = islToChanIDs isl
                         comp = map (\x -> getInitiator net x) chans ++ map (\x -> getTarget net x) chans
                         comp' = L.nub $ filter (\x -> case getComponent net x of (Merge _) -> True; _ -> False) comp
                     in comp'

mergePairCheck :: ColoredNetwork -> Int -> Int -> Bool
mergePairCheck net i1 i2 = let isls = islSetToList $ transferIslands net
                               isl1 = isls !! i1
                               isl2 = isls !! i2
                               m1 = isleMerges net isl1
                               m2 = isleMerges net isl2
                           in L.intersect m1 m2 == []

mergeConfs :: ColoredNetwork -> [[Int]]
mergeConfs net = let isls = islSetToList $ transferIslands net
                     confs = replicateM (L.length isls) [0,1]
                     confs' = filter (\x -> isValidConf net x) confs
                 in confs'

isValidConf :: ColoredNetwork -> [Int] -> Bool
isValidConf net conf = let conf' = filter (\x -> x /= -1) $ updConf conf 0 
                           pairs = filter (\x -> (x !! 0) /= (x !! 1)) $ L.nub $ map (\x -> L.sort x) $ replicateM 2 conf'
                       in foldr (\x y -> x && y) True $ map (\x -> mergePairCheck net (x !! 0) (x !! 1)) pairs
  where updConf :: [Int] -> Int -> [Int]
        updConf [] _ = []
        updConf (x:xs) ind
          | x == 0 = (-1:updConf xs (ind + 1))
          | otherwise = (ind:updConf xs (ind + 1))
  

makeMetaIsle :: ColoredNetwork -> (Island a) -> Int -> (BM.Bimap Int MFunctionDisj, BM.Bimap Int MFunctionBool) -> MetaIsle
makeMetaIsle net isl i _ {-(fm,pm)-} = let ins = getIns isl net
                                           outs = getOuts isl net
                                           fprop = [] --funcProp net isl (fm,pm)
                                           mkin = \(n::ColoredNetwork) (c::ComponentID) -> case getComponent n c of
                                                                                             (Source _ (ColorSet col)) -> MetaComp c (Arg c) Src (IOColor col) (Capacity 0)
                                                                                             (Queue _ cap) -> let (ColorSet col) = snd $ getChannel n ((getInChannels n c) !! 0) in MetaComp c (Arg c) Q (IOColor col) (Capacity cap)
                                                                                             _ -> error "wrong component"
                                           mkout = \(n::ColoredNetwork) (c::ComponentID) _ {-(fp::[(ChannelID, FunComp)])-} -> case getComponent n c of
                                                                                                                                 (Sink _) -> let (ColorSet col) = snd $ getChannel n ((getInChannels n c) !! 0)
                                                                                                                                           --p = [] snd . head $ filter (\(x,_) -> x == ((getInChannels n c) !! 0)) fp
                                                                                                                                             in MetaComp c (Fun 0 []) Snk (IOColor col) (Capacity 0)
                                                                                                                                 (Queue _ cap) -> let (ColorSet col) = snd $ getChannel n ((getInChannels n c) !! 0)
                                                                                                                                                --p = [] snd . head $ filter (\(x,_) -> x == ((getInChannels n c) !! 0)) fp
                                                                                                                                                  in MetaComp c (Fun 0 []) Q (IOColor col) (Capacity cap)
                                                                                                                                 _ -> error "wrong component"
                                       in MetaIsle i (islToChanIDs isl) (map (\x -> mkin net x) ins) (map (\x -> mkout net x fprop) outs)                                   

makeMetaIslands :: ColoredNetwork -> MetaIslands
makeMetaIslands net = let isls = islSetToList $ transferIslands net
                          t = typeFieldGetter net
                          fpm = funPredMap net
                          mrgs = getAllMerges net
                      in MetaIslands t (L.length mrgs) (mergeConfs net) fpm (map (\x -> makeMetaIsle net x (fromJust $ L.elemIndex x isls) fpm) isls)


getSources :: MetaIslands -> [MetaComp]
getSources (MetaIslands _ _ _ _ m) = let comps = L.nub . L.concat $ map (\(MetaIsle _ _ c1 _) -> c1) m
                                         res = filter (\x -> case x of (MetaComp _ _ Src _ _) -> True; _ -> False) comps
                                     in res
                                      
getSinks :: MetaIslands -> [MetaComp]
getSinks (MetaIslands _ _ _ _ m) = let comps = L.nub . L.concat $ map (\(MetaIsle _ _ _ c1) -> c1) m
                                       res = filter (\x -> case x of (MetaComp _ _ Snk _ _) -> True; _ -> False) comps
                                   in res

getQueues :: MetaIslands -> [MetaComp]
getQueues (MetaIslands _ _ _ _ m) = let comps = L.nub . L.concat $ map (\(MetaIsle _ _ _ c1) -> c1) m
                                        res = filter (\x -> case x of (MetaComp _ _ Q _ _) -> True; _ -> False) comps
                                    in res

uniqueIDMetaComps :: [MetaComp] -> [MetaComp]
uniqueIDMetaComps xs = uniqueIDMetaComps' xs []
  where uniqueIDMetaComps' :: [MetaComp] -> [MetaComp] -> [MetaComp]
        uniqueIDMetaComps' [] ms = ms
        uniqueIDMetaComps' (m:ms) ms' = let (MetaComp i _ _ _ _) = m
                                        in if (existsID ms' i)
                                           then uniqueIDMetaComps' ms ms'
                                           else uniqueIDMetaComps' ms (m:ms')
          
existsID :: [MetaComp] -> ComponentID -> Bool
existsID [] _ = False
existsID ((MetaComp i _ _ _ _):xs) j
  | i == j = True
  | otherwise = existsID xs j
          
metaCompToID :: MetaComp -> ComponentID
metaCompToID (MetaComp i _ _ _ _) = i

metaCompsToIDs :: [MetaComp] -> [ComponentID]
metaCompsToIDs ms = map (\(MetaComp i _ _ _ _) -> i) ms

compType :: MetaComp -> S.Set Color
compType (MetaComp _ _ _ (IOColor t) _) = t

compCapacity :: MetaComp -> Int
compCapacity (MetaComp _ _ _ _ (Capacity i)) = i

getCompType :: MetaComp -> CompType
getCompType (MetaComp _ _ t _ _) = t

srcInd :: ColoredNetwork -> MetaComp -> Int
srcInd net comp = let (MetaComp _ _ t _ _) = comp
                      misls = makeMetaIslands net
                      srcs = L.nub $ getSources misls
                  in case t of
                       Src -> srcInd' srcs comp 0
                       _ -> error "Source component is expected"
  where srcInd' :: [MetaComp] -> MetaComp -> Int -> Int
        srcInd' [] _ j = j
        srcInd' ((MetaComp g _ _ _ _):xs) (MetaComp h a b c d) j
          | g == h = j
          | otherwise = srcInd' xs (MetaComp h a b c d) (j+1)

snkInd :: ColoredNetwork -> MetaComp -> Int
snkInd net comp = let (MetaComp _ _ t _ _) = comp
                      misls = makeMetaIslands net
                      snks = L.nub $ getSinks misls
                  in case t of
                       Snk -> snkInd' snks comp 0
                       _ -> error "Sink component is expected"
  where snkInd' :: [MetaComp] -> MetaComp -> Int -> Int
        snkInd' [] _ j = j
        snkInd' ((MetaComp g _ _ _ _):xs) (MetaComp h a b c d) j
          | g == h = j
          | otherwise = snkInd' xs (MetaComp h a b c d) (j+1)

qInd :: ColoredNetwork -> MetaComp -> Int
qInd net comp = let (MetaComp _ _ t _ _) = comp
                    misls = makeMetaIslands net
                    qs = L.nub $ getQueues misls
                in case t of
                     Q -> qInd' qs comp 0
                     _ -> error "Queue component is expected"
  where qInd' :: [MetaComp] -> MetaComp -> Int -> Int
        qInd' [] _ j = j
        qInd' ((MetaComp g _ _ _ _):xs) (MetaComp h a b c d) j
          | g == h = j
          | otherwise = qInd' xs (MetaComp h a b c d) (j+1)

inpInd :: ColoredNetwork -> MetaComp -> [Int]
inpInd net comp = let (MetaIslands _ _ _ _ misls) = makeMetaIslands net
                  in inpInd' misls comp
  where inpInd' :: [MetaIsle] -> MetaComp -> [Int]
        inpInd' [] _ = [] --error "inpInd: component not found"
        inpInd' (m:ms) c = let (MetaIsle i _ _ _) = m
                           in if (hasInpComp m c)
                              then (i:inpInd' ms c)
                              else inpInd' ms c

hasInpComp :: MetaIsle -> MetaComp -> Bool
hasInpComp (MetaIsle _ _ cs _) c = hasInpComp' cs c
  where hasInpComp' :: [MetaComp] -> MetaComp -> Bool
        hasInpComp' [] _ = False
        hasInpComp' ((MetaComp i _ _ _ _):xs) (MetaComp j e f g h)
          | i == j = True
          | otherwise = hasInpComp' xs (MetaComp j e f g h)

getComp :: [MetaComp] -> ComponentID -> MetaComp
getComp [] c = error ("MetaComp:" ++ show c ++ " not found")
getComp (m:ms) c = --error $ show (m:ms) ++ " *** " ++ show c 
  let (MetaComp d _ _ _ _) = m
  in if (c == d)
     then m
     else getComp ms c

funIOMap :: ColoredNetwork -> IM.IntMap (S.Set Color,S.Set Color)
funIOMap net = let funs = L.nub . map (\(_,x) -> let (Function c f o) = x
                                                     a = fromJust $ findComponentID net c
                                                     finp = head $ getInChannels net a
                                                     (ColorSet i) = getColorSet net finp
                                                 in (f,i,o)) $ getAllFunctionsWithID net
                   (fm,_) = funPredMap net
                   funs' = map (\(x,y,z) -> let (ColorSet z') = z in (fm BM.!> x,(y,z'))) funs
               in IM.fromList funs'

predIOMap :: ColoredNetwork -> IM.IntMap (S.Set Color)
predIOMap net = let preds = L.nub . L.concat . map (\(_,x) -> case x of
                                                                Switch (c::Text) ps -> map (\z -> (c,z)) ps
                                                                FControlJoin (c::Text) p -> [(c,p)]
                                                                _ -> error "incorrect primitive") $ getAllFunctionsWithID net
                    (_,pm) = funPredMap net
                    preds' = map (\((x::Text),y) -> let a = fromJust $ findComponentID net x
                                                        finp = head $ getInChannels net a
                                                        (ColorSet i) = getColorSet net finp
                                                    in (y,i)) preds
                    preds'' = map (\(x,y) -> (pm BM.!> x,y)) preds'
                in IM.fromList preds''
