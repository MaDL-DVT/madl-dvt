{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleInstances, CPP #-}

module Madl2mCRL2.Converter
where

import Madl.MsgTypes
import Madl.Network
import Madl.MsgTypes()
import Madl.Islands
import Utils.Text
import Data.Maybe
import qualified Data.List as L
import qualified Data.HashMap as Hash
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Control.Monad (replicateM)

makemCRL2 :: ColoredNetwork -> String
makemCRL2 net = makeTypeDecl net
                ++ "\n\n"
                ++ makeDefDecl
                ++ "\n\n"
                ++ makeFuns net
                ++ "\n\n"
                ++ makeActs net
                ++ "\n\n"
                ++ instantiateProcs net
                ++ "\n\n"
                -- ++ "init " ++ hide net ++ ";"
                ++ getHideCommAllow net
                ++ "\n\n"
                -- ++ getComm net

data HideCommAllow = HideCommAllow { usedComps :: [ComponentID],
                                     unusedComps :: [ComponentID],
                                     result :: String
                                   }

--function that takes two lists of compIDs and computes communicating actions, using comm pairs

--function that takes a list of compIDs and computes external actions

--function that makes a hide by using a list of communicating actions

--function that makes an allow using a communicating and external actions

{-
allow :: ColoredNetwork -> String
allow net = let syncacts = syncActs net
                syncacts' = map (\x -> foldr (\a b -> case b of
                                                        "" -> a ++ b
                                                        _ -> a ++ "|" ++ b) "" x) syncacts
                syncacts'' = foldr (\x y -> case y of
                                              "" -> x ++ y
                                              _ -> x ++ "," ++ y) "" syncacts'
            in "allow({" ++ syncacts'' ++ "}," ++ communication net ++ ")"
-}

getHideCommAllow :: ColoredNetwork -> String
getHideCommAllow net = let cs = getComponentIDs net
                           r = case getComponent net (head cs) of
                                 (Source _ _) -> "(free)"
                                 (Queue _ _) -> "([])"
                                 _ -> ""
                           c = (compName net (head cs) True) ++ r
                       in "init " ++ getHideCommAllow' (HideCommAllow ([head cs]) (tail cs) c) ++ ";"
  where getHideCommAllow' :: HideCommAllow -> String
        getHideCommAllow' hda = case (unusedComps hda) of
                                  [] -> result hda
                                  _ -> let comm = getCommRes net (usedComps hda) [(head $ unusedComps hda)]
                                           alw = getAllowActs net (usedComps hda) [(head $ unusedComps hda)]
                                           alw' = map (\x -> foldr (\a b -> case b of
                                                                       "" -> a ++ b
                                                                       _ -> a ++ "|" ++ b) "" x) alw
                                           alw'' = foldr (\x y -> case y of
                                                             "" -> x ++ y
                                                             _ -> x ++ "," ++ y) "" alw'
                                           hid = foldr (\x y -> case y of
                                                             "" -> x ++ y
                                                             _ -> x ++ "," ++ y) "" (getCommActs net (usedComps hda) [(head $ unusedComps hda)])
                                           cmp = case (getComponent net (head $ unusedComps hda)) of
                                                   (Source _ _) -> "(free)"
                                                   (Queue _ _) -> "([])"
                                                   _ -> ""
                                           cmp' = (compName net (head $ unusedComps hda) True) ++ cmp
                                           res = case comm of
                                                   "" -> "allow({" ++ alw'' ++ "},(" ++ "(" ++ (result hda) ++ ") || " ++ cmp' ++ "))"
                                                   _ -> "hide({" ++ hid ++ "},allow({" ++ alw'' ++ "},comm({" ++ comm ++ "},(" ++ (result hda) ++ ") || " ++ cmp' ++ ")))"
                                       in getHideCommAllow' (HideCommAllow ((usedComps hda) ++ [(head $ unusedComps hda)]) (tail $ unusedComps hda) res)
                                         

getCommRes :: ColoredNetwork -> [ComponentID] -> [ComponentID] -> String
getCommRes net c1 c2 = let pairs = communicatingPairs net
                           pairs' = filter (\(a,_,_,b) ->
                                              (elem a c1 && elem b c2) || (elem a c2 && elem b c1)) pairs
                           pairActs = foldr (\x y -> case y of
                                                    "" -> x ++ y
                                                    _ -> x ++ "," ++ y) ""
                                      (concat (map (\(a,b,c,d) -> commActs
                                                                  ((compName net a False) ++ "_o" ++ (show b))
                                                                  ((compName net d False) ++ "_i" ++ (show c))) pairs'))
                       in pairActs

getCommActs :: ColoredNetwork -> [ComponentID] -> [ComponentID] -> [String]
getCommActs net c1 c2 = let pairs = communicatingPairs net
                            pairs' = filter (\(a,_,_,b) ->
                                               (elem a c1 && elem b c2) || (elem a c2 && elem b c1)) pairs
                            pairActs = (concat (map (\(a,b,c,d) -> [((compName net a False) ++ "_o" ++ (show b)) ++ "_" ++
                                                                   ((compName net d False) ++ "_i" ++ (show c)) ++ "_io"]) pairs'))
                        in pairActs

getAllowActs :: ColoredNetwork -> [ComponentID] -> [ComponentID] -> [[String]]
getAllowActs net c1 c2 = let c = L.nub (c1 ++ c2)
                             cacts = getCommActs net c1 c2
                             srcs = getAllSourceIDs net
                             srcs' = L.intersect srcs c
                             iSrcActs = map (\x -> [{-compName net x False ++ "_idle",-}compName net x False ++ "_inject"])  srcs'
                             snks = getAllSinkIDs net
                             snks' = L.intersect snks c
                             iSnkActs = map (\x -> [{-compName net x False ++ "_reject",-}compName net x False ++ "_consume"]) snks'
                             pairs = communicatingPairs net
                             pairs' = filter (\(a,_,_,b) ->
                                                not ((elem a c1 && elem b c2) || (elem a c2 && elem b c1) || (elem a c1 && elem b c1))) pairs
                             ncomo = filter (\(x,_) -> L.elem x c) (map (\(a,b,_,_) -> (a,b)) pairs')
                             ncomi = filter (\(x,_) -> L.elem x c) (map (\(_,_,a,b) -> (b,a)) pairs')
                             ids = L.nub ((map (\(x,_) -> x) ncomi) ++ (map (\(x,_) -> x) ncomo))
                             nc = map (\x -> let i = map (\(g,h) -> ((compName net g False) ++ "_i" ++ (show h) ++ "_in")) (filter (\(a,_) -> x == a) ncomi)
                                                 o = map (\(g,h) -> ((compName net g False) ++ "_o" ++ (show h) ++ "_out")) (filter (\(a,_) -> x == a) ncomo)
                                             in {-cartprod ([i] ++ [o])-} (i ++ o)) ids
                         in cartprod (filter (\x -> x /= []) (iSrcActs ++ iSnkActs ++ (map (\x -> [x]) cacts) ++ (map (\y -> [y]) (concat nc))))
--cartprod needs [[string]]
{-
syncActs :: ColoredNetwork -> [[String]]
syncActs net = cartprod (intSrcActs net ++ intSnkActs net ++ cActs net)

intSrcActs :: ColoredNetwork -> [[String]]
intSrcActs net = let srcs = getAllSourceIDs net
                 in map (\x -> [compName net x False ++ "_idle",compName net x False ++ "_inject"]) srcs

intSnkActs :: ColoredNetwork -> [[String]]
intSnkActs net = let snks = getAllSinkIDs net
                 in map (\x -> [compName net x False ++ "_reject",compName net x False ++ "_consume"]) snks

cActs :: ColoredNetwork -> [[String]]
cActs net = let pairs = communicatingPairs net
                pairActs = map (\(a,b,c,d) -> ioActs'
                                              ((compName net a False) ++ "_o" ++ (show b))
                                              ((compName net d False) ++ "_i" ++ (show c))) pairs
-}
                           
compName :: ColoredNetwork -> ComponentID -> Bool -> String
compName net c b = let comps = getComponentIDs net
                       i = show $ fromJust $ L.elemIndex c comps
                   in case (getComponent net c) of
                        (Source _ _) -> if b then ("Src" ++ i) else ("src" ++ i)
                        (Sink _) -> if b then ("Snk" ++ i) else ("snk" ++ i)
                        (Function _ _ _) -> if b then ("Func" ++ i) else ("func" ++ i)
                        (Queue _ _) -> if b then ("Q" ++ i) else ("q" ++ i) 
                        (Switch _ _) -> if b then ("Sw" ++ i) else ("sw" ++ i)
                        (Merge _) -> if b then ("Mrg" ++ i) else ("mrg" ++ i)
                        (Fork _) -> if b then ("Frk" ++ i) else ("frk" ++ i)
                        (ControlJoin _) -> if b then ("Cj" ++ i) else ("cj" ++ i)
                        (FControlJoin _ _) -> if b then ("Fcj" ++ i) else ("fcj" ++ i)
                        (MultiMatch _ _) -> if b then ("Mm" ++ i) else ("mm" ++ i)
                        (LoadBalancer _) -> if b then ("Lb" ++ i) else ("lb" ++ i)
                        _ -> error "compName: the component is not supported yet"


getAllColors :: ColoredNetwork -> [Color]
getAllColors net = let compIDs = getComponentIDs net
                   in L.nub $ L.concat (map (\x -> let ins = getInChannels net x
                                                       outs = getOutChannels net x
                                                       inCols = L.concat (map (\a -> let ColorSet z = (getColorSet net a) in Set.toList z) ins)
                                                       outCols = L.concat (map (\a -> let ColorSet z = (getColorSet net a) in Set.toList z) outs)
                                                   in inCols ++ outCols) compIDs)

colorMap :: ColoredNetwork -> M.Map Color Int
colorMap net = let colors = getAllColors net
                   colors' = L.zip colors [0..L.length colors]
               in M.fromList colors'

makeTypeDecl :: ColoredNetwork -> String
makeTypeDecl net = "sort C = struct " ++
                   foldr (\a b -> case b of
                                    "" -> a ++ b
                                    _ -> a ++ " | " ++ b)
                   ""
                   (map (\x -> "c" ++ show x) [0..L.length (getAllColors net) - 1]) ++ ";\n" ++
                   "sort S = struct free | next(C);"

getCond :: ColoredNetwork -> ComponentID -> Bool -> Int -> String
getCond net comp isinp i = let inChans = getInChannels net comp
                               outChans = getOutChannels net comp
                           in if ((L.length inChans <= i && isinp) || (L.length outChans <= i && not isinp))
                              then "getCond: wrong input channel index " ++ show i ++ " in " ++ show (L.length inChans) ++ " out " ++ show (L.length outChans)
                              else if isinp
                                   then let ColorSet colors = getColorSet net (inChans !! i)
                                            cm = colorMap net
                                            res = foldr (\a b -> case b of
                                                                   "" -> a ++ b
                                                                   _ -> a ++ " || " ++ b)
                                                  ""
                                                  (map (\x -> "x == c" ++ (show $ cm M.! x)) (Set.toList colors))
                                        in case res of
                                             "" -> "true"
                                             _ -> res
                                   else let ColorSet colors = getColorSet net (outChans !! i)
                                            cm = colorMap net
                                            res = foldr (\a b -> case b of
                                                                   "" -> a ++ b
                                                                   _ -> a ++ " || " ++ b)
                                                  ""
                                                  (map (\x -> "x == c" ++ (show $ cm M.! x)) (Set.toList colors))
                                        in case res of
                                             "" -> "true"
                                             _ -> res

{-
map def_frk0: C;
eqn def_frk0 = r;
-}

makeDefDecl :: String
makeDefDecl = "map def: C;\neqn def = c0;"

makeActs :: ColoredNetwork -> String
makeActs net = let compIDs = getComponentIDs net
                   pairs = communicatingPairs net
                   pairActs = map (\(a,b,c,d) -> ioActs
                                                 ((compName net a False) ++ "_o" ++ (show b))
                                                 ((compName net d False) ++ "_i" ++ (show c))) pairs
               in "act\n"
                  ++ foldr (\x y -> case y of
                                      "" -> "\t\t" ++ x ++ ";" ++ y;
                                      _ -> "\t\t" ++ x ++ ";\n" ++ y) "" (concat ((map (\x -> makeActs' x) compIDs) ++
                                                                                 pairActs)
                                                                                  )
  where makeActs' :: ComponentID -> [String]
        makeActs' c = let c' = getComponent net c
                          n = compName net c False
                      in case c' of
                           (Source _ _) -> [--n ++ "_idle",
                                            n ++ "_inject:Bool # C"] ++
                                           outActs (n ++ "_o0")
                           (Sink _) -> [--n ++ "_reject",
                                        n ++ "_consume:Bool # C"] ++
                                       inActs (n ++ "_i0")
                           (Function _ _ _) -> inActs (n ++ "_i0") ++
                                               outActs (n ++ "_o0")
                           (Queue _ _) -> inActs (n ++ "_i0") ++
                                          outActs (n ++ "_o0")
                           (Switch _ _) -> let outs = getOutChannels net c
                                           in inActs (n ++ "_i0") ++
                                              (concat $ map (\x -> outActs
                                                              (n
                                                                ++ "_o" ++ (show $ fromJust $ L.elemIndex x outs))) outs)
                           (Merge _) -> let ins = getInChannels net c
                                        in (concat $ map (\x -> inActs
                                                           (n
                                                            ++ "_i" ++ (show $ fromJust $ L.elemIndex x ins))) ins) ++
                                           outActs (n ++ "_o0")
                           (Fork _) -> let outs = getOutChannels net c
                                       in inActs (n ++ "_i0") ++
                                          (concat $ map (\x -> outActs
                                                              (n
                                                                ++ "_o" ++ (show $ fromJust $ L.elemIndex x outs))) outs)
                           (ControlJoin _) -> let ins = getInChannels net c
                                              in (concat $ map (\x -> outActs
                                                                 (n
                                                                  ++ "_i" ++ (show $ fromJust $ L.elemIndex x ins))) ins) ++
                                                 outActs (n ++ "o0")
                           (FControlJoin _ _) -> let ins = getInChannels net c
                                                 in (concat $ map (\x -> outActs
                                                                    (n
                                                                     ++ "_i" ++ (show $ fromJust $ L.elemIndex x ins))) ins) ++
                                                    outActs (n ++ "o0")
                           (MultiMatch _ _) -> let ins = getInChannels net c
                                                   outs = getOutChannels net c
                                               in (concat $ map (\x -> inActs
                                                                  (n
                                                                   ++ "_i" ++ (show $ fromJust $ L.elemIndex x ins))) ins) ++
                                                  (concat $ map (\x -> outActs
                                                                  (n
                                                                   ++ "_o" ++ (show $ fromJust $ L.elemIndex x outs))) outs)
                           (LoadBalancer _) -> let outs = getOutChannels net  c
                                               in inActs (n ++ "_i0") ++
                                                  (concat $ map (\x -> outActs
                                                                  (n
                                                                   ++ "_o" ++ (show $ fromJust $ L.elemIndex x outs))) outs)
                           _ -> error "makeActs: the component is not supported yet"

                                
inActs :: String -> [String]
inActs pref = [pref ++ "_in: Bool # Bool # C"]

outActs :: String -> [String]
outActs pref = [pref ++ "_out: Bool # Bool # C"]

ioActs :: String -> String -> [String]
ioActs pref1 pref2 = [pref1 ++ "_" ++ pref2 ++ "_io: Bool # Bool # C"]

ioActs' :: String -> String -> [String]
ioActs' pref1 pref2 = [pref1 ++ "_" ++ pref2 ++ "_io"]

srcTemplate :: ColoredNetwork -> ComponentID -> String
srcTemplate net c = "proc " ++ (compName net c True) ++ "(s:S) = \n" ++
                    "\t((s == free)\n" ++
                    "\t\t-> ((" ++ (compName net c False) ++ "_inject(false,def)|" ++ (compName net c False) ++ "_o0_out(false,false,def) + " ++ (compName net c False) ++ "_inject(false,def)|" ++ (compName net c False) ++ "_o0_out(false,true,def))." ++ (compName net c True) ++ "(free)\n" ++
                    "\t\t   + sum x:C.((" ++ (getCond net c False 0) ++ ") -> (" ++ (compName net c False) ++ "_inject(true,x)|" ++ (compName net c False) ++ "_o0_out(true,true,x)." ++ (compName net c True) ++ "(free) + " ++ (compName net c False) ++ "_inject(true,x)|" ++ (compName net c False) ++ "_o0_out(true,false,x)." ++ (compName net c True) ++ "(next(x))))))\n" ++
                    "\t+ sum x:C.((s == next(x))\n" ++
                    "\t\t-> (" ++ (compName net c False) ++ "_inject(true,x)|" ++ (compName net c False) ++ "_o0_out(true,false,x)." ++ (compName net c True) ++ "(next(x))\n" ++
                    "\t\t   + " ++ (compName net c False) ++ "_inject(true,x)|" ++ (compName net c False) ++ "_o0_out(true,true,x)." ++ (compName net c True) ++ "(free)));"


queueTemplate :: ColoredNetwork -> ComponentID -> String
queueTemplate net c = case getComponent net c of
                        (Queue _ n) ->
                          "proc " ++ (compName net c True) ++ "(s:List(C)) = \n" ++
                          "\t((s == [])" ++ "\n" ++
                          "\t\t-> sum x:C.(\n" ++
                          "\t\t\t" ++ (compName net c False) ++ "_i0_in(false,true,x)|" ++ (compName net c False) ++ "_o0_out(false,true,x)." ++ (compName net c True) ++ "([])\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(false,true,x)|" ++ (compName net c False) ++ "_o0_out(false,false,x)." ++ (compName net c True) ++ "([])\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(true,true,x)|" ++ (compName net c False) ++ "_o0_out(false,true,x)." ++ (compName net c True) ++ "(x |> s)\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(true,true,x)|" ++ (compName net c False) ++ "_o0_out(false,false,x)." ++ (compName net c True) ++ "(x |> s)))\n" ++
                          "\t+ ((s != [] && #s < " ++ show n ++ ")\n" ++ "\n" ++
                          "\t\t-> sum x:C.(\n" ++
                          "\t\t\t" ++ (compName net c False) ++ "_i0_in(true,true,x)|" ++ (compName net c False) ++ "_o0_out(true,true,rhead(s))." ++ (compName net c True) ++ "(x |> rtail(s))\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(false,true,x)|" ++ (compName net c False) ++ "_o0_out(true,true,rhead(s))." ++ (compName net c True) ++ "(rtail(s))\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(true,true,x)|" ++ (compName net c False) ++ "_o0_out(true,false,rhead(s))." ++ (compName net c True) ++ "(x |> s)))\n" ++
                          "\t+ ((#s == " ++ show n ++ ")\n" ++
                          "\t\t-> sum x:C.(\n" ++
                          "\t\t\t" ++ (compName net c False) ++ "_i0_in(true,false,x)|" ++ (compName net c False) ++ "_o0_out(true,false,rhead(s))." ++ (compName net c True) ++ "(s)\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(false,false,x)|" ++ (compName net c False) ++ "_o0_out(true,false,rhead(s))." ++ (compName net c True) ++ "(s)\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(true,false,x)|" ++ (compName net c False) ++ "_o0_out(true,true,rhead(s))." ++ (compName net c True) ++ "(rtail(s))\n" ++
                          "\t\t\t+ " ++ (compName net c False) ++ "_i0_in(false,false,x)|" ++ (compName net c False) ++ "_o0_out(true,true,rhead(s))." ++ (compName net c True) ++ "(rtail(s))));"
                        _ -> error "queueTemplate: wrong component"


snkTemplate :: ColoredNetwork -> ComponentID -> String
snkTemplate net c = "proc " ++ (compName net c True) ++ " =\n" ++
                    "\tsum x:C.(" ++ (compName net c False) ++ "_consume(false,def)|" ++ (compName net c False) ++ "_i0_in(false,false,x) + " ++ (compName net c False) ++ "_consume(false,def)|" ++ (compName net c False) ++ "_i0_in(true,false,x))." ++ (compName net c True) ++ "\n" ++
                    "\t\t+ sum x:C.((" ++ getCond net c True 0 ++ ") -> " ++ (compName net c False) ++ "_consume(true,x)|" ++ (compName net c False) ++ "_i0_in(false,true,x)." ++ (compName net c True) ++ ")\n" ++
                    "\t\t+ sum x:C.((" ++ getCond net c True 0 ++ ") -> " ++  (compName net c False) ++ "_consume(true,x)|" ++ (compName net c False) ++ "_i0_in(true,true,x)." ++ (compName net c True) ++ ");"

frkTemplate :: ColoredNetwork -> ComponentID -> String
frkTemplate net c = "proc " ++ (compName net c True) ++ " =\n" ++
                    "\tsum x:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x)|" ++ (compName net c False) ++ "_o0_out(false,false,x)|" ++ (compName net c False) ++ "_o1_out(false,false,x))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x)|" ++ (compName net c False) ++ "_o0_out(false,true,x)|" ++ (compName net c False) ++ "_o1_out(false,false,def))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x)|" ++ (compName net c False) ++ "_o0_out(false,false,x)|" ++ (compName net c False) ++ "_o1_out(false,true,def))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(false,true,x)|" ++ (compName net c False) ++ "_o0_out(false,true,x)|" ++ (compName net c False) ++ "_o1_out(false,true,x))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(true,false,x)|" ++ (compName net c False) ++ "_o0_out(true,false,x)|" ++ (compName net c False) ++ "_o1_out(true,false,x))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(true,true,x)|" ++ (compName net c False) ++ "_o0_out(true,true,x)|" ++ (compName net c False) ++ "_o1_out(true,true,x)." ++ (compName net c True) ++ ");"


funTemplate :: ColoredNetwork -> ComponentID -> String
funTemplate net c = "proc " ++ (compName net c True) ++ " =\n" ++
                    "\tsum x:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x)|" ++ (compName net c False) ++ "_o0_out(false,false,f_" ++ (compName net c False) ++ "(x)))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(false,true,x)|" ++ (compName net c False) ++ "_o0_out(false,true,f_" ++ (compName net c False) ++ "(x)))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(true,false,x)|" ++ (compName net c False) ++ "_o0_out(true,false,f_" ++ (compName net c False) ++ "(x)))." ++ (compName net c True) ++ "\n" ++
                    "\t+ sum x:C.(" ++ (compName net c False) ++ "_i0_in(true,true,x)|" ++ (compName net c False) ++ "_o0_out(true,true,f_" ++ (compName net c False) ++ "(x))." ++ (compName net c True) ++ ");"


swtchTemplate :: ColoredNetwork -> ComponentID -> String
swtchTemplate net c = let cs = switchIO net c
                          res = foldr (\g h -> case h of
                                                 "" -> g ++ h ++ ";"
                                                 _ -> g ++ "\n\t+ " ++ h) "" $
                                map (\x -> case switchPredTransfers x of
                                             True -> let is = snd' x
                                                         os = trd' x                                              
                                                         ri = swtchTemplateI is []
                                                         ro = swtchTemplateO os []
                                                         p = zip [0..(length (fst' x))] (map (\z -> case z of
                                                                                                      True -> "true"
                                                                                                      _ -> "false") $ fst' x)
                                                         p' = map (\z -> "(p_" ++
                                                                         compName net c False ++
                                                                         "_" ++
                                                                         show (fst z) ++
                                                                         "(x) == " ++
                                                                         snd z ++
                                                                         ")") p
                                                         preds = foldr
                                                                 (\a b -> case b of
                                                                            "" -> a ++ b
                                                                            _ -> a ++ " && " ++ b)
                                                                 ""
                                                                 p'
                                                         r = foldr (\a b -> case b of
                                                                              "" -> a ++ b
                                                                              _ -> a ++ "|" ++ b) "" (ri ++ ro)
                                                     in "sum x:C.(((" ++ preds ++ ")) -> (" ++ r ++ "." ++ compName net c True ++ "))" 
                                             _ -> let is = snd' x
                                                      os = trd' x
                                                      ri = swtchTemplateI is []
                                                      ro = swtchTemplateO os []
                                                      p = zip [0..(length (fst' x))] (map (\z -> case z of
                                                                                                   True -> "true"
                                                                                                   _ -> "false") $ fst' x)
                                                      p' = map (\z -> "(p_" ++
                                                                      compName net c False ++
                                                                      "_" ++
                                                                      show (fst z) ++
                                                                      "(x) == " ++
                                                                      snd z ++
                                                                      ")") p
                                                      preds = foldr
                                                              (\a b -> case b of
                                                                         "" -> a ++ b
                                                                         _ -> a ++ " && " ++ b)
                                                              ""
                                                              p'
                                                      r = foldr (\a b -> case b of
                                                                           "" -> a ++ b
                                                                           _ -> a ++ "|" ++ b) "" (ri ++ ro)
                                                  in "sum x:C.(((" ++ preds ++ ")) -> (" ++ r ++ "." ++ compName net c True ++ "))") cs
                      in "proc " ++ (compName net c True) ++ " = \n\t" ++ res
  where swtchTemplateI :: [(Bool,Bool)] -> [String] -> [String]
        swtchTemplateI [] res = res
        swtchTemplateI ((False,False):xs) res = swtchTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(false,false,x)"])
        swtchTemplateI ((False,True):xs) res = swtchTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(false,true,x)"])
        swtchTemplateI ((True,False):xs) res = swtchTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(true,false,x)"])
        swtchTemplateI ((True,True):xs) res = swtchTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(true,true,x)"])
        swtchTemplateO :: [(Bool,Bool)] -> [String] -> [String]
        swtchTemplateO [] res = res
        swtchTemplateO ((False,False):xs) res = swtchTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(false,false,x)"])
        swtchTemplateO ((False,True):xs) res = swtchTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(false,true,x)"])
        swtchTemplateO ((True,False):xs) res = swtchTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(true,false,x)"])
        swtchTemplateO ((True,True):xs) res = swtchTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(true,true,x)"])


mmTemplate :: ColoredNetwork -> ComponentID -> String
mmTemplate net c = let cs = mmIO net c
                       res = foldr (\g h -> case h of
                                              "" -> g ++ h ++ ";"
                                              _ -> g ++ "\n\t+ " ++ h) "" $
                             map (\x -> case (fst . fst'') x of
                                          True -> let i0s = snd'' x
                                                      i1s = trd'' x
                                                      os = frt'' x                                              
                                                      ri0 = mmTemplateI i0s 0 []
                                                      ri1 = mmTemplateI i1s (L.length ri0) []
                                                      ro = mmTemplateO os 0 []
                                                      sm = foldr (\k l -> case l of
                                                                            "" -> k ++ l
                                                                            _ -> k ++ "." ++ l) ""
                                                           (map (\z -> "sum x" ++ show z ++ ":C")
                                                            [0..(length i0s + length i1s - 1)])
                                                      r = foldr (\a b -> case b of
                                                                           "" -> a ++ b
                                                                           _ -> a ++ "|" ++ b) "" (ri0 ++ ri1 ++ ro)
                                                  in sm ++ ".((p_" ++ compName net c False ++ "(x" ++ show ((fst . snd . fst'') x) ++ ",x" ++ show ((snd . snd . fst'') x) ++ ")) -> (" ++ r ++ "." ++ compName net c True ++ "))" 
                                          _ -> let i0s = snd'' x
                                                   i1s = trd'' x
                                                   os = frt'' x                                              
                                                   ri0 = mmTemplateI i0s 0 []
                                                   ri1 = mmTemplateI i1s (L.length ri0) []
                                                   ro = mmTemplateO os 0 []
                                                   sm = foldr (\k l -> case l of
                                                                            "" -> k ++ l
                                                                            _ -> k ++ "." ++ l) ""
                                                        (map (\z -> "sum x" ++ show z ++ ":C")
                                                         [0..(length i0s + length i1s - 1)])
                                                   r = foldr (\a b -> case b of
                                                                        "" -> a ++ b
                                                                        _ -> a ++ "|" ++ b) "" (ri0 ++ ri1 ++ ro)
                                               in sm ++ ".((!p_" ++ compName net c False ++ "(x" ++ show ((fst . snd . fst'') x) ++ ",x" ++ show ((snd . snd . fst'') x) ++ ")) -> (" ++ r ++ "." ++ compName net c True ++ "))") cs
                   in "proc " ++ (compName net c True) ++ " = \n\t" ++ res
  where mmTemplateI :: [(Bool,Bool)] -> Int -> [String] -> [String]
        mmTemplateI [] _ res = res
        mmTemplateI ((False,False):xs) i res = mmTemplateI xs (i+1) (res ++ [(compName net c False) ++ "_i" ++ show i ++ "_in(false,false,x" ++ show i ++ ")"])
        mmTemplateI ((False,True):xs) i res = mmTemplateI xs (i+1) (res ++ [(compName net c False) ++ "_i" ++ show i ++ "_in(false,true,x" ++ show i ++ ")"])
        mmTemplateI ((True,False):xs) i res = mmTemplateI xs (i+1) (res ++ [(compName net c False) ++ "_i" ++ show i ++ "_in(true,false,x" ++ show i ++")"])
        mmTemplateI ((True,True):xs) i res = mmTemplateI xs (i+1) (res ++ [(compName net c False) ++ "_i" ++ show i ++ "_in(true,true,x" ++ show i ++ ")"])
        mmTemplateO :: [(Bool,Bool)] -> Int -> [String] -> [String]
        mmTemplateO [] _ res = res
        mmTemplateO ((False,False):xs) i res = mmTemplateO xs (i+1) (res ++ [(compName net c False) ++ "_o" ++ show i ++ "_out(false,false,x" ++ show i ++ ")"])
        mmTemplateO ((False,True):xs) i res = mmTemplateO xs (i+1) (res ++ [(compName net c False) ++ "_o" ++ show i ++ "_out(false,true,x" ++ show i ++ ")"])
        mmTemplateO ((True,False):xs) i res = mmTemplateO xs (i+1) (res ++ [(compName net c False) ++ "_o" ++ show i ++ "_out(true,false,x" ++ show i ++ ")"])
        mmTemplateO ((True,True):xs) i res = mmTemplateO xs (i+1) (res ++ [(compName net c False) ++ "_o" ++ show i ++ "_out(true,true,x" ++ show i ++ ")"])


mergeTemplate :: ColoredNetwork -> ComponentID -> String
mergeTemplate net c = "proc " ++ (compName net c True) ++ " =\n" ++
                      "\tsum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x0)|" ++ (compName net c False) ++ "_i1_in(false,false,x1)|" ++ (compName net c False) ++ "_o0_out(false,false,c0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,false,x0)|" ++ (compName net c False) ++ "_i1_in(false,false,x1)|" ++ (compName net c False) ++ "_o0_out(true,false,c0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x0)|" ++ (compName net c False) ++ "_i1_in(true,false,x1)|" ++ (compName net c False) ++ "_o0_out(true,false,c0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,false,x0)|" ++ (compName net c False) ++ "_i1_in(true,false,x1)|" ++ (compName net c False) ++ "_o0_out(true,false,c0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,true,x0)|" ++ (compName net c False) ++ "_i1_in(false,false,x1)|" ++ (compName net c False) ++ "_o0_out(false,true,c0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x0)|" ++ (compName net c False) ++ "_i1_in(false,true,x1)|" ++ (compName net c False) ++ "_o0_out(false,true,c0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,true,x0)|" ++ (compName net c False) ++ "_i1_in(true,false,x1)|" ++ (compName net c False) ++ "_o0_out(true,true,x0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,true,x0)|" ++ (compName net c False) ++ "_i1_in(false,false,x1)|" ++ (compName net c False) ++ "_o0_out(true,true,x0))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,false,x0)|" ++ (compName net c False) ++ "_i1_in(true,true,x1)|" ++ (compName net c False) ++ "_o0_out(true,true,x1))." ++ (compName net c True) ++ "\n" ++
                      "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x0)|" ++ (compName net c False) ++ "_i1_in(true,true,x1)|" ++ (compName net c False) ++ "_o0_out(true,true,x1))." ++ (compName net c True) ++ ";"
                      

deadSnkTemplate :: ColoredNetwork -> ComponentID -> String
deadSnkTemplate net c = "proc " ++ (compName net c True) ++ " =\n" ++
                        "\tsum x:C.(" ++ (compName net c False) ++ "_reject|" ++ (compName net c False) ++ "_i0_in(false,false,x))." ++ (compName net c True) ++ "\n" ++
                        "\t+ sum x:C.(" ++ (compName net c False) ++ "_reject|" ++ (compName net c False) ++ "_i0_in(true,false,x))." ++ (compName net c True) ++ ";"

{-
proc CtrlJoin = 
    in_i0_00|in_i1_00|out_o_00.CtrlJoin
    + in_i0_01|in_i1_01|out_o_01.CtrlJoin
    + in_i0_10|in_i1_10|out_o_10.CtrlJoin
    + sum c1:C.sum c2:C.in_i0_11(с1)|in_i1_11(c2)|out_o_11(c1).CtrlJoin;    
-}

cJTemplate :: ColoredNetwork -> ComponentID -> String
cJTemplate net c = "proc " ++ (compName net c True) ++ " =\n" ++
                   "\tsum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,false,x0)|" ++ (compName net c False) ++ "_i1_in(false,false,x1)|" ++ (compName net c False) ++ "_o0_out(false,false,x0))." ++ (compName net c True) ++ "\n" ++
                   "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(false,true,x0)|" ++ (compName net c False) ++ "_i1_in(false,true,x1)|" ++ (compName net c False) ++ "_o0_out(false,true,x0))." ++ (compName net c True) ++ "\n" ++
                   "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,false,x0)|" ++ (compName net c False) ++ "_i1_in(true,false,x1)|" ++ (compName net c False) ++ "_o0_out(true,false,x0))." ++ (compName net c True) ++ "\n" ++
                   "\t+ sum x0:C.sum x1:C.(" ++ (compName net c False) ++ "_i0_in(true,true,x0)|" ++ (compName net c False) ++ "_i1_in(true,true,x1)|" ++ (compName net c False) ++ "_o0_out(true,true,x0))." ++ (compName net c True) ++ ";"
  
  
lbTemplate :: ColoredNetwork -> ComponentID -> String
lbTemplate net c = let cs = lbIO net c
                       res = foldr (\g h -> case h of
                                              "" -> g ++ h ++ ";"
                                              _ -> g ++ "\n\t+ " ++ h) "" $
                             map (\x -> let is = fst x
                                            os = snd x                                              
                                            ri = lbTemplateI is []
                                            ro = lbTemplateO os []
                                            r = foldr (\a b -> case b of
                                                                 "" -> a ++ b
                                                                 _ -> a ++ "|" ++ b) "" (ri ++ ro)
                                        in "sum x:C.(" ++ r ++ "." ++ compName net c True ++ ")") cs
                   in "proc " ++ (compName net c True) ++ " = \n\t" ++ res
  where lbTemplateI :: [(Bool,Bool)] -> [String] -> [String]
        lbTemplateI [] res = res
        lbTemplateI ((False,False):xs) res = lbTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(false,false,x)"])
        lbTemplateI ((False,True):xs) res = lbTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(false,true,x)"])
        lbTemplateI ((True,False):xs) res = lbTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(true,false,x)"])
        lbTemplateI ((True,True):xs) res = lbTemplateI xs (res ++ [(compName net c False) ++ "_i" ++ show (L.length res) ++ "_in(true,true,x)"])
        lbTemplateO :: [(Bool,Bool)] -> [String] -> [String]
        lbTemplateO [] res = res
        lbTemplateO ((False,False):xs) res = lbTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(false,false,x)"])
        lbTemplateO ((False,True):xs) res = lbTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(false,true,x)"])
        lbTemplateO ((True,False):xs) res = lbTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(true,false,x)"])
        lbTemplateO ((True,True):xs) res = lbTemplateO xs (res ++ [(compName net c False) ++ "_o" ++ show (L.length res) ++ "_out(true,true,x)"])

makeFuns :: ColoredNetwork -> String
makeFuns net = let comps = getComponentIDs net
               in concat $ map (\x -> makeFun x) comps
  where makeFun :: ComponentID -> String
        makeFun c = case getComponent net c of
                      (Function _ f _) -> let (ColorSet inCols') = getColorSet net (head $ getInChannels net c)
                                              inCols = Set.toList inCols'
                                              (outCols :: [Color]) = map (\a -> eval (makeVArguments [a]) f) inCols
                                              inOutCols = zip inCols outCols
                                              cm = colorMap net
                                              res = ["map \n\tf_" ++ compName net c False ++ ": C -> C;\n","eqn\n"]
                                                    ++ (map (\(x,y) -> "\tf_" ++
                                                                       compName net c False ++
                                                                       "(c" ++ (show $ cm M.! x) ++ ") = c" ++
                                                                       (show $ cm M.! y) ++ ";\n") inOutCols)
                                          in concat res
                      (Switch _ ps) -> concat $ map (\p -> let (ColorSet inCols') = getColorSet net ((getInChannels net c) !! 0)
                                                               inCols = Set.toList inCols'
                                                               (outBools :: [Bool]) = map (\a -> eval (makeVArguments [a]) p) inCols
                                                               inOutCols = zip inCols outBools
                                                               cm = colorMap net
                                                               res = ["map \n\tp_" ++ compName net c False ++ "_" ++ show (fromJust $ L.elemIndex p ps) ++ ": C -> Bool;\n","eqn\n"]
                                                                     ++ (map (\(x,y) -> "\tp_" ++
                                                                                        compName net c False ++
                                                                                        "_" ++
                                                                                        show (fromJust $ L.elemIndex p ps) ++
                                                                                        "(c" ++ (show $ cm M.! x) ++ ") = " ++
                                                                                        (mcrl2Bool y) ++ ";\n") inOutCols)
                                                           in concat res ++ "\n") ps
                      (MultiMatch _ p) -> let ins = getInChannels net c
                                              inCols = concat $ map (\x -> let (ColorSet y) = getColorSet net x in Set.toList y) ins
                                              inPairs = L.nub [(a,b)|a <- inCols,b <- inCols]
                                              (outCols :: [Bool]) = map (\(x,y) -> eval (makeVArguments ([x] ++ [y])) p) inPairs
                                              inOut = zip inPairs outCols
                                              cm = colorMap net
                                              res = ["map \n\tp_" ++ compName net c False ++ ": C # C -> Bool;\n","eqn\n"]
                                                    ++ (map (\((x,y),z) -> "\tp_" ++
                                                                       compName net c False ++
                                                                       "(c" ++
                                                                       (show $ cm M.! x) ++
                                                                       ",c" ++
                                                                       (show $ cm M.! y) ++
                                                                       ") = " ++
                                                                       (mcrl2Bool z) ++ ";\n") inOut)
                                          in concat res
                      _ -> ""

mcrl2Bool :: Bool -> String
mcrl2Bool True = "true"
mcrl2Bool False = "false"

ioGen :: Int -> Int -> (([Bool],[(Bool,Bool)],[(Bool,Bool)]) -> Bool) -> [([Bool],[(Bool,Bool)],[(Bool,Bool)])]
ioGen ni no p = [(a,as,bs)|a <- replicateM no [True,False],as <- replicateM ni [(g,h) | g <- [True,False], h <- [True,False]], bs <- replicateM no [(x,y) | x <- [True,False], y <- [True,False]], p (a,as,bs) && (L.length (filter (\z -> case z of True -> True; _ -> False) a) <= 1)]

switchCond :: ([Bool],[(Bool,Bool)],[(Bool,Bool)]) -> Bool
switchCond cs = let i = (head . snd') cs
                    o = trd' cs
                    o' = zip (fst' cs) o
                    cond1 = snd i == ((foldr (\a b -> a || b) False $ map (\x -> fst x && snd x) o))
                    cond2 = foldr (\a b -> a && b) True $ map (\x -> (fst . snd) x == (fst i && fst x)) o'
                in cond1 && cond2

switchIO :: ColoredNetwork -> ComponentID -> [([Bool],[(Bool,Bool)],[(Bool,Bool)])]
switchIO net c = ioGen (L.length $ getInChannels net c) (L.length $ getOutChannels net c) switchCond

switchTransfers :: ([(Bool,Bool)],[(Bool,Bool)]) -> Bool
switchTransfers cs = (head . fst) cs == (True,True) 

switchPredTransfers :: ([Bool],[(Bool,Bool)],[(Bool,Bool)]) -> Bool
switchPredTransfers cs = L.length (filter (\x -> x) (fst' cs)) > 0

mmIOGen :: Int -> Int -> Int -> (((Bool,(Int,Int)),[(Bool,Bool)],[(Bool,Bool)],[(Bool,Bool)]) -> Bool) -> [((Bool,(Int,Int)),[(Bool,Bool)],[(Bool,Bool)],[(Bool,Bool)])]
mmIOGen ni0 ni1 no p = [((a,(a',a'')),as,bs,cs)|a <- [True,False],a'<-[0..(ni0-1)],a''<-[(ni0)..(ni0+ni1-1)],as <- replicateM ni0 [(g,h) | g <- [True,False], h <- [True,False]], bs <- replicateM ni1 [(x,y) | x <- [True,False], y <- [True,False]], cs <- replicateM no [(m,n) | m <- [True,False], n <- [True,False]], p ((a,(a',a'')),as,bs,cs)] 

mmCond :: ((Bool,(Int,Int)),[(Bool,Bool)],[(Bool,Bool)],[(Bool,Bool)]) -> Bool
mmCond cs = let p = (fst . fst'') cs
                j = (fst . snd . fst'') cs
                k = (snd . snd . fst'') cs
                i1 = snd'' cs
                i2 = trd'' cs
                i2' = zip i2 [length i1..(length i1 + length i2 - 1)]
                o = frt'' cs
                i1o = zip i1 o
                i1o' = zip i1o [0..length i1o]
                cond1 = foldr (\a b -> a && b) True (map (\(x,y) -> snd x == (fst y && snd y)) i1o)
                cond2 = (foldr (\a b -> a && b) True (map (\x -> (snd . fst) x == ((countTransfers o > 0) && (snd x == k))) i2')) 
                cond3 = (foldr (\a b -> a && b) True (map (\((x,y),n) -> fst y == (fst x && p && countIrdys i2 > 0 && n == j)) i1o')) 
                cond4 = if (countTransfers o > 0)
                        then (countTransfers i2 > 0) && (countTransfers i1 > 0)
                         else True
            in cond1 && cond2 && cond3 && cond4

mmIO :: ColoredNetwork -> ComponentID -> [((Bool,(Int,Int)),[(Bool,Bool)],[(Bool,Bool)],[(Bool,Bool)])]
mmIO net c = let nri0 = L.length $ getOutChannels net c
                 nri1 = (L.length $ getInChannels net c) - nri0
                 nro = nri0
             in mmIOGen nri0 nri1 nro mmCond

mmInpPair :: ((Bool,(Int,Int)),[(Bool,Bool)],[(Bool,Bool)],[(Bool,Bool)]) -> Maybe (Int,Int)
mmInpPair cs = let i1 = trd'' cs
                   o = frt'' cs
                   r1 = L.elemIndex True (map (\x -> snd x) i1)
                   r2 = L.elemIndex True (map (\x -> fst x) o)
               in if (r1 == Nothing || r2 == Nothing)
                  then Nothing
                  else Just (fromJust r1,fromJust r2)

lbIOGen :: Int -> Int -> (([(Bool,Bool)],[(Bool,Bool)]) -> Bool) -> [([(Bool,Bool)],[(Bool,Bool)])]
lbIOGen ni no p = [(as,bs)|as <- replicateM ni [(g,h) | g <- [True,False], h <- [True,False]], bs <- replicateM no [(x,y) | x <- [True,False], y <- [True,False]], p (as,bs)]


lbCond :: ([(Bool,Bool)],[(Bool,Bool)]) -> Bool
lbCond cs = let i = (head . fst) cs
                o = snd cs
                cond1 = snd i == ((foldr (\a b -> a || b) False $ map (\x -> snd x) o))
                cond2 = countIrdys o <= 1
                cond3 = if (countTransfers [i] > 0) then (countTransfers o > 0) else True 
            in cond1 && cond2 && cond3

lbIO :: ColoredNetwork -> ComponentID -> [([(Bool,Bool)],[(Bool,Bool)])]
lbIO net c = lbIOGen (L.length $ getInChannels net c) (L.length $ getOutChannels net c) lbCond

             
countTransfers :: [(Bool,Bool)] -> Int
countTransfers bs = let r = map (\x -> case x of
                                         (True,True) -> 1
                                         _ -> 0) bs
                        (r'::Int) = foldr (\a b -> a + b) 0 r
                    in r'

countIrdys :: [(Bool,Bool)] -> Int
countIrdys bs = let r = map (\x -> case x of
                                   (True,_) -> 1
                                   _ -> 0) bs
                    (r'::Int) = foldr (\a b -> a + b) 0 r
                in r'

countTrdys :: [(Bool,Bool)] -> Int
countTrdys bs = let r = map (\x -> case x of
                                   (_,True) -> 1
                                   _ -> 0) bs
                    (r'::Int) = foldr (\a b -> a + b) 0 r
                in r'

outPortIndex :: (Int,[(Bool,Bool)],[(Bool,Bool)]) -> Int
outPortIndex cs = case fst' cs of
                    -1 -> error "outPortIndex: wrong component"
                    i -> i
  
instantiateProcs :: ColoredNetwork -> String
instantiateProcs net = let comps = getComponentIDs net
                       in foldr (\a b -> case b of
                                           "" -> a ++ b
                                           _ -> a ++ "\n\n" ++ b) "" 
                          (map (\x -> case getComponent net x of
                                        (Source _ _) -> srcTemplate net x
                                        (Queue _ _) -> queueTemplate net x
                                        (Sink _) -> snkTemplate net x
                                        (Fork _) -> frkTemplate net x
                                        (Switch _ _) -> swtchTemplate net x
                                        (Function _ _ _) -> funTemplate net x
                                        (DeadSink _) -> deadSnkTemplate net x
                                        (MultiMatch _ _) -> mmTemplate net x
                                        (Merge _) -> mergeTemplate net x
                                        (LoadBalancer _) -> lbTemplate net x
                                        (ControlJoin _) -> cJTemplate net x
                                        _ -> "") comps)
  
  
getAllSinkIDs :: ColoredNetwork -> [ComponentID]
getAllSinkIDs net = map (\(x,_) -> x) $ getAllSinksWithID net

intSrcActs :: ColoredNetwork -> [[String]]
intSrcActs net = let srcs = getAllSourceIDs net
                 in map (\x -> [compName net x False ++ "_idle",compName net x False ++ "_inject"]) srcs

intSnkActs :: ColoredNetwork -> [[String]]
intSnkActs net = let snks = getAllSinkIDs net
                 in map (\x -> [compName net x False ++ "_reject",compName net x False ++ "_consume"]) snks

cActs :: ColoredNetwork -> [[String]]
cActs net = let pairs = communicatingPairs net
                pairActs = map (\(a,b,c,d) -> ioActs'
                                              ((compName net a False) ++ "_o" ++ (show b))
                                              ((compName net d False) ++ "_i" ++ (show c))) pairs
            in pairActs

syncActs :: ColoredNetwork -> [[String]]
syncActs net = cartprod (intSrcActs net ++ intSnkActs net ++ cActs net)

cartprod :: [[String]] -> [[String]]
cartprod [] = [[]]
cartprod (xs:xss) = [x:ys | x<- xs, ys <-yss]
  where yss = cartprod xss

commActs :: String -> String -> [String]
commActs pref1 pref2 = [pref1 ++ "_out|" ++ pref2 ++ "_in -> " ++ pref1 ++ "_" ++ pref2 ++ "_io"
                       ]

communicatingPairs :: ColoredNetwork -> [(ComponentID,Int,Int,ComponentID)]
communicatingPairs net = let comps = getComponentIDs net
                         in concat $ map (\x -> let outs = getOutChannels net x
                                                in map (\y -> (x,
                                                               fromJust $ L.elemIndex y outs,
                                                               getInpID net x (getTarget net y),
                                                               (getTarget net y))) outs) comps

composition :: ColoredNetwork -> String
composition net = let comps = getComponentIDs net
                  in foldr (\x y -> case y of
                                      "" -> x ++ y
                                      _ -> x ++ " || " ++ y) "" (map (\x -> let c = (compName net x True)
                                                                            in case (getComponent net x) of
                                                                                 (Source _ _) -> c ++ "(free)"
                                                                                 (Queue _ _) -> c ++ "([])"
                                                                                 _ -> c
                                                                            ) comps)

allow :: ColoredNetwork -> String
allow net = let syncacts = syncActs net
                syncacts' = map (\x -> foldr (\a b -> case b of
                                                        "" -> a ++ b
                                                        _ -> a ++ "|" ++ b) "" x) syncacts
                syncacts'' = foldr (\x y -> case y of
                                              "" -> x ++ y
                                              _ -> x ++ "," ++ y) "" syncacts'
            in "allow({" ++ syncacts'' ++ "}," ++ communication net ++ ")"

hide :: ColoredNetwork -> String
hide net = let cacts = cActs net
               cacts' = foldr (\x y -> case y of
                                         "" -> x ++ y
                                         _ -> x ++ "," ++ y) "" (concat cacts)
           in "hide({" ++ cacts' ++ "}," ++ allow net ++ ")"

communication :: ColoredNetwork -> String
communication net = let pairs = communicatingPairs net
                        pairActs = foldr (\x y -> case y of
                                                    "" -> x ++ y
                                                    _ -> x ++ "," ++ y) ""
                                   (concat (map (\(a,b,c,d) -> commActs
                                                               ((compName net a False) ++ "_o" ++ (show b))
                                                               ((compName net d False) ++ "_i" ++ (show c))) pairs))
                    in "comm({" ++ pairActs ++ "}," ++ composition net ++ ")" 

getInpID :: ColoredNetwork -> ComponentID -> ComponentID -> Int
getInpID net c1 c2 = let ins = getInChannels net c2
                     in getInpID' ins 0
  where getInpID' :: [ChannelID] -> Int -> Int
        getInpID' [] _ = error "getInpID: initiator not found"
        getInpID' (x:xs) i
          | c1 == getInitiator net x = i
          | otherwise = getInpID' xs (i+1)
        

fst' :: (a,b,c) -> a
fst' (x,_,_) = x

snd' :: (a,b,c) -> b
snd' (_,x,_) = x

trd' :: (a,b,c) -> c
trd' (_,_,x) = x

fst'' :: (a,b,c,d) -> a
fst'' (x,_,_,_) = x

snd'' :: (a,b,c,d) -> b
snd'' (_,x,_,_) = x

trd'' :: (a,b,c,d) -> c
trd'' (_,_,x,_) = x

frt'' :: (a,b,c,d) -> d
frt'' (_,_,_,x) = x

fst''' :: (a,b,c,d,e) -> a
fst''' (x,_,_,_,_) = x

snd''' :: (a,b,c,d,e) -> b
snd''' (_,x,_,_,_) = x

trd''' :: (a,b,c,d,e) -> c
trd''' (_,_,x,_,_) = x

----------------Old code, might be useful for functions, predicates and color to mcrl2 conversions----------------

--data SinkAction = Reject | Consume Color deriving (Show,Ord,Eq)

--type SinkActWithID = (ComponentID,SinkAction)

--data SourceAction = Idle | Inject Color deriving (Show,Ord,Eq)

--type SourceActWithID = (ComponentID,SourceAction)

--type MergeAction = ChannelID

--type MergeActWithID = (ComponentID,MergeAction)

--type Action = ([SourceActWithID], [SinkActWithID], [MergeActWithID])

data SourceState = Free | Next deriving (Show,Ord,Eq)

data CompAction = Idle | Reject | Inject | Consume | MergeNone | MergeIn ChannelID deriving (Eq, Ord, Show)

data ConvState = ConvState
  {
    maps :: [String],
    eqns :: [String],
    ind  :: Int
  } deriving Show

type Isle = Island (WithColors (XChannel Text))

{-
sinkActions :: ColoredNetwork -> [SinkActWithID]
sinkActions network = let z = (getAllSinksWithID network) in [(x,y) | x <- (map fst z), y <- (Reject: map (\t -> Consume t) (getPossiblePackets network))]

sourceActions :: ColoredNetwork -> [SourceActWithID]
sourceActions network = let z = (getAllSourcesWithID network) in [(x,y) | x <- (map fst z), y <- (Idle: map (\t -> Inject t) (getPossiblePackets network))]

getSourceActions :: ColoredNetwork -> ComponentID -> [SourceActWithID]
getSourceActions net i = let chans = getOutChannels net i
                             comp = getComponent net i
                         in if ((length chans) == 1)
                            then case comp of
                                   Source _ (ColorSet c) -> [(i,x)| x <- (Idle: map (\t -> Inject t) (Set.toList c))]
                                   _ -> error "getSourceActions: Wrong component"
                            else error "getSourceActions: Wrong component"

getSinkActions :: ColoredNetwork -> ComponentID -> [SinkActWithID]
getSinkActions net i = let c = getInChannels net i
                           comp = getComponent net i
                       in if ((length c) == 1)
                          then case comp of
                                 Sink _ -> let (_,ColorSet d) = getChannel net (head c) in [(i,x)| x <- (Reject: map (\t -> Consume t) (Set.toList d))]
                                 _ -> error "getSinkActions: Wrong component"
                          else error "getSinkActions: Wrong component"

getMergeActions :: ColoredNetwork -> ComponentID -> [MergeActWithID]
getMergeActions net i = let ins = getInChannels net i
                            comp = getComponent net i
                        in if ((length ins) > 0)
                           then case comp of
                                  Merge _ -> [(i,x)| x <- ins]
                                  _ -> error "getMergeActions: Wrong component"
                           else error "getMergeActions: Wrong component"
-}

getPossiblePackets :: ColoredNetwork -> [Color]
getPossiblePackets network = Set.toList (Set.unions (map (\(_,b,_) -> let (ColorSet d) = (snd b) in d) (map (\x -> getChannelContext network x) $ getChannelIDs network)))

convArgs :: VArguments -> [String]
convArgs _ = []


-- TODO: refactor this and the next function
makeTXTDecl :: ColoredNetwork -> String
makeTXTDecl n = "sort TXT = struct " ++ (makeTXTDecl' $ filter (\x -> x /= "") $ (L.nub (networkTypes n ++ networkStructFields n)) ++ ["empty"]) ++ ";\n"
  where makeTXTDecl' :: [Text] -> String
        makeTXTDecl' xs = let xs' = map (\x -> noslashes (show x)) xs
                          in foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ " | " ++ y) "" xs'

makeFTXTDecl :: ColoredNetwork -> String
makeFTXTDecl n = let res = (makeFTXTDecl' $ filter (\x -> x /= "") $ networkStructFields n)
                 in case res of
                      "" -> "sort FTXT = struct none;\n"
                      _ -> "sort FTXT = struct " ++ res ++ ";\n"
  where makeFTXTDecl' :: [Text] -> String
        makeFTXTDecl' xs = let xs' = map (\x -> noslashes (show x)) xs
                           in foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ " | " ++ y) "" xs'
                    
functionHeader :: ColoredNetwork -> String
functionHeader n = makeTXTDecl n ++ makeFTXTDecl n ++ "sort Color = struct color (text: TXT, valOrStruct: ValueOrVstruct);\nsort ValueOrVstruct = struct value(val: Int) ? isVal | vstruct(v: List(FTextValOrCol)) ? isVstruct;\nsort FTextValOrCol = struct ftextOrValOrCol(ftext: FTXT, valOrCol: ValOrColor);\nsort ValOrColor = struct value(v: Int) ? isVal | col(c: Color) ? isCol;\nvar x : List(Color);"

  
--TODO: refactor!
{-
makemCRL2 :: ColoredNetwork -> String
makemCRL2 net = let (ConvState m e _) = allFunConv net
                    args = foldr
                           (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) ""
                           ["x" ++ show i | i <- [0..((getMaxIslInputs net)-1)]]
                    sourceids = map (\(x,_) -> x) $ getAllSourcesWithID net
                    sourceacts = concat $ map (\x -> makeCompActions net x) sourceids
                    mergeids = map (\(x,_) -> x) $ getAllMergesWithID net
                    mergeacts = concat $ map (\x -> makeCompActions net x) mergeids
                    sinkids = map (\(x,_) -> x) $ getAllSinksWithID net
                    sinkacts = concat $ map (\x -> makeCompActions net x) sinkids
                    sh = sourceHash net
                    qh = queueHash net
                    isls = islSetToList $ transferIslands net
                    iconf = legalConfs net $ makeIslConf $ L.length isls
                    sconf = makeSourceConfs net
                    acts = makeActions net 
                    condacts = map    
                               (\(a,b,c) -> makeCond net a b c ++ "\n\t\t-> " ++ convAct net b c ++ ".P(" ++ makeNewState net a b c ++ ")\n")
                               (filter (\(a,b,c) -> isAllowed net a b c) [(ic,sc,ac)|ic <- iconf,sc <- sconf,ac <- acts])
                in makeTXTDecl net ++
                   --makeFTXTDecl net ++
                   "sort Color = struct color (text: TXT, valOrStruct: ValueOrVstruct);\nsort ValueOrVstruct = struct value(v: Int) ? isVal | vstruct(vs: List(FTextValOrCol)) ? isVstruct;\nsort FTextValOrCol = struct ftextOrValOrCol(ftext: TXT, valOrCol: ValOrColor);\nsort ValOrColor = struct value(v: Int) ? isVal | col(c: Color) ? isCol;\nsort S = struct free | next(c:List(Color));" ++
                   "\nmap\n" ++
                   (foldr (\x y -> case y of "" -> "\t" ++ x ++ y; _ -> "\t" ++ x ++ "\n" ++ y) "" m) ++
                   "\nvar\n" ++
                   "\tt: TXT;\n" ++
                   "\tl: List(FTextValOrCol);\n" ++
                   "\tx: List(Color);\n" ++
                   "\t" ++ args ++ " : List(Color);" ++
                   "\neqn\n" ++
                   (foldr (\x y -> case y of "" -> "\t" ++ x ++ y; _ -> "\t" ++ x ++ "\n" ++ y) "" e) ++
                   "\n" ++
                   "\nact\n" ++
                   actionsDecl net (sourceacts ++ mergeacts ++ sinkacts) ++ "\n" ++
                   "proc P(" ++
                   foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" (Hash.elems sh) ++ ":S," ++
                   foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" (Hash.elems qh) ++ ":List(Color)) =\n" ++
                   "\t" ++ foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "\t+ " ++ y) "" condacts ++ ";\n\n" ++
                   "init P(" ++
                   foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" (map (\_ -> "free") (Hash.elems sh)) ++ "," ++
                   foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" (map (\_ -> "[]") (Hash.elems qh)) ++ ");\n"
-}

--TODO: refactor!
makeCond :: ColoredNetwork -> [Bool] -> [(ComponentID,SourceState)] -> [(ComponentID, CompAction)] -> String
makeCond net conf sconf act = let sh = sourceHash net
                                  ah = argHash net act sconf
                                  sumvars = Hash.elems ah
                                  sumids = Hash.keys ah
                                  sumconds = makeTerm' "&&" $ map (\x -> packetsToCond x (getActPackets net x) ah) sumids
                                  sumconds' = case sumconds of
                                                "" -> ""
                                                _ -> " && " ++ sumconds
                                  sumvars' = case sumvars of
                                               [] -> ""
                                               _ -> "sum " ++
                                                    foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" sumvars ++
                                                    ":List(Color)."
                              in sumvars' ++ "(" ++
                                 (makeCond' net conf act (islSetToList $ transferIslands net) "") ++ " && " ++
                                 foldr (\g h -> case h of "" -> g ++ h; _ -> g ++ " && " ++ h) ""
                                 (map (\(a,b) -> case b of
                                                   Free -> "(" ++ (sh Hash.! a) ++ " == free)"
                                                   Next -> "(" ++ (sh Hash.! a) ++ " == next(" ++ ah Hash.! a ++ "))") sconf) ++
                                 sumconds' ++ ")"
  where makeCond' :: ColoredNetwork -> [Bool] -> [(ComponentID, CompAction)] -> [Isle] -> String -> String
        makeCond' _[] _ _ res = res
        makeCond' _ _ _ [] res = res
        makeCond' n (c:cs) a (i:is) res = let qh = queueHash n
                                              ins = getIns i n
                                              icomps = map (\x -> (getComponent n x,x)) ins
                                              icomps' = filter (\(x,_) -> case x of (Queue _ _) -> True; _ -> False) icomps
                                              cond1 = map (\(_,x) -> "#" ++ qh Hash.! x ++ " > 0") icomps'
                                              cond1' = addParenthesis $ makeTerm' "&&" cond1
                                              outs = getOuts i n
                                              ocomps = map (\x -> (getComponent n x,x)) outs
                                              ocomps' = filter (\(x,_) -> case x of (Queue _ _) -> True; _ -> False) ocomps
                                              cond2 = map (\((Queue _ cap),x) -> "#" ++ qh Hash.! x ++ " < " ++ show cap) ocomps'
                                              res' = if (res == []) then res else (res ++ " && ")
                                              cond2' = addParenthesis $ makeTerm' "&&" cond2
                                              cond3 = funCond n i a sconf
                                              cond = if c
                                                     then makeTerm' "&&" [cond1',cond2',cond3]
                                                     else if (cond3 == "")
                                                          then negTerm (makeTerm' "&&" [cond1',cond2'])
                                                          else makeTerm' "||" [(negTerm (makeTerm' "&&" [cond1',cond2'])), makeTerm' "&&" [cond1',cond2',negTerm cond3]]
                                          in makeCond' n cs a is (res' ++ cond)

makeTerm :: String -> String -> String -> String
makeTerm op = \x y -> if ((x /= "") && (y /= "")) then (x ++ " " ++ op ++ " " ++ y) else (x ++ y)

makeTerm' :: String -> [String] -> String
makeTerm' op xs = let xs' = filter (\x -> x /= "") xs
                  in if (L.length xs' > 1)
                     then "(" ++ (foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ " " ++ op ++ " " ++ y) "" xs') ++ ")"
                     else (foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ " " ++ op ++ " " ++ y) "" xs')

negTerm :: String -> String
negTerm "" = ""
negTerm x = "!" ++ x

funCond :: ColoredNetwork -> Isle -> [(ComponentID, CompAction)] -> [(ComponentID, SourceState)] -> String
funCond net isl act sconf = let ins = getIns isl net
                                outs = getOuts isl net
                                outs' = filter (\x -> case getComponent net x of
                                                        (Sink _) -> if ((getCompAct x act) == Consume)
                                                                    then True
                                                                    else False
                                                        (Queue _ _) -> True                 
                                                        _ -> False) outs
                                ah = argHash net act sconf
                                qh = queueHash net
                                inpArgs = map (\x -> case getComponent net x of
                                                       (Source _ _) -> if ((getCompAct x act) == Inject)
                                                                       then (ah Hash.! x)
                                                                       else "[]"
                                                       (Queue _ _) -> "[rhead(" ++ qh Hash.! x ++ ")]"
                                                       _ -> error "funCond: unexpected component"
                                              ) ins
                                inpArgs' = foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" $ inpArgs
                            in if (not $ elem "[]" inpArgs)
                               then funCond' net isl inpArgs' outs' act ah ""
                               else ""
  where funCond' :: ColoredNetwork -> Isle -> String -> [ComponentID] -> [(ComponentID, CompAction)] -> Hash.Map ComponentID String -> String -> String
        funCond' _ _ _ [] _ _ res = res
        funCond' n i args (x:xs) a ah res = let res' = if (res /= "")
                                                       then (res ++ " && ")
                                                       else res
                                                ch = chanHash net
                                                outchan = if ((getInChannels n x) /= [])
                                                          then head $ getInChannels n x
                                                          else error "test 5"
                                            in case getComponent net x of
                                                 (Queue _ _) -> funCond' n i args xs a ah (res' ++ ("(IR_" ++ show (fromJust $ getIslID n i) ++ "_" ++ ch Hash.! outchan ++ "(" ++ args ++ ") != [])"))
                                                 (Sink _) -> funCond' n i args xs a ah (res' ++ ("(IR_" ++ show (fromJust $ getIslID n i) ++ "_" ++ ch Hash.! outchan ++ "(" ++ args ++ ") == " ++ ah Hash.! x  ++ ")"))
                                                 _ -> error "funCond: unexpected component"

getArg :: ColoredNetwork -> ComponentID -> (Hash.Map ComponentID String) -> (Hash.Map ComponentID String) -> [(ComponentID, CompAction)] -> String
getArg net comp qs ah act = case getComponent net comp of
                              (Source _ _) -> case getCompAct comp act of
                                                Inject -> ah Hash.! comp
                                                Idle -> "[]"
                                                _ -> error "getArg: unexpected component"
                              (Queue _ _) -> qs Hash.! comp
                              _ -> error "getArg: unexpected component"

addParenthesis :: String -> String
addParenthesis "" = ""
addParenthesis s = "(" ++ s ++ ")"

isLegalConf :: ColoredNetwork -> [Bool] -> Bool
isLegalConf net iconf = isLegalConf' net (map (\(x,_) -> x) $ getAllMergesWithID net) iconf
  where isLegalConf' :: ColoredNetwork -> [ComponentID] -> [Bool] -> Bool
        isLegalConf' _ [] _ = True
        isLegalConf' n (x:xs) ic = let mergeIns = getInChannels n x
                                       isls = islSetToList $ transferIslands n
                                       isls' = filter (\y -> let i = fromJust (L.elemIndex y isls) in (((L.intersect (islToChanIDs y) mergeIns) /= []) && (ic!!i))) isls
                                   in if ((L.length isls' > 1))
                                      then False
                                      else isLegalConf' net xs ic
                                           
legalConfs :: ColoredNetwork -> [[Bool]] -> [[Bool]]
legalConfs net iconfs = filter (\x -> isLegalConf net x) iconfs

makeCompActions :: ColoredNetwork -> ComponentID -> [(ComponentID, CompAction)]
makeCompActions net i = case getComponent net i of
                          (Source _ _) -> [(i,x)| x <- [Idle, Inject]]
                          (Sink _) -> [(i,x)| x <- [Reject, Consume]]
                          (Merge _) -> let outs = getInChannels net i
                                       in [(i,MergeNone)] ++ [(i,MergeIn x) | x <- outs]
                          _ -> error "makeCompActions: wrong component"

makeActions :: ColoredNetwork -> [[(ComponentID, CompAction)]]
makeActions net = let l1 = L.length (getAllSources net)
                      l2 = L.length (getAllMerges net)
                      l3 = L.length (getAllSinks net) 
                      sourceids = map (\(x,_) -> x) $ getAllSourcesWithID net
                      sourceacts = concat $ map (\x -> makeCompActions net x) sourceids
                      sourceacts' = filter (\x -> uniqueIDs x) (replicateM l1 sourceacts)
                      mergeids = map (\(x,_) -> x) $ getAllMergesWithID net
                      mergeacts = concat $ map (\x -> makeCompActions net x) mergeids
                      mergeacts' = filter (\x -> uniqueIDs x) (replicateM l2 mergeacts)
                      sinkids = map (\(x,_) -> x) $ getAllSinksWithID net
                      sinkacts = concat $ map (\x -> makeCompActions net x) sinkids
                      sinkacts' = filter (\x -> uniqueIDs x) (replicateM l3 sinkacts)
                  in L.nub $ map (\(a,b,c) -> L.sort (a ++ b ++ c)) [(a,b,c)|a <- sourceacts', b <- mergeacts', c <- sinkacts'] --L.nub $ map (\x -> L.sort x) $ filter (\x -> uniqueIDs x) $ replicateM n (sourceacts ++ mergeacts ++ sinkacts)

getCompAct :: ComponentID -> [(ComponentID, CompAction)] -> CompAction
getCompAct i a = if ((filter (\(x,_) -> i == x) a) /= [])
                 then snd . L.head $ filter (\(x,_) -> i == x) a
                 else error $ show (i,a)

getActPackets :: ColoredNetwork -> ComponentID -> [Color]
getActPackets net i = case getComponent net i of
                        (Source _ (ColorSet c)) -> Set.toList c
                        (Sink _) -> if ((inputTypes net i) /= [])
                                    then let (ColorSet c) = head $ inputTypes net i in Set.toList c
                                    else error "test 7"
                        _ -> []

checkIslIO :: ColoredNetwork -> (Island a) -> [(ComponentID, CompAction)] -> Bool
checkIslIO net isl act = let iocomponents = (getIns isl net) ++ (getOuts isl net)
                         in foldr (\x y -> x && y)
                            True (map (\x -> case getComponent net x of
                                               Source _ _ -> (getCompAct x act) == Inject
                                               Sink _ -> (getCompAct x act) == Consume
                                               _ -> True) iocomponents)
                                                                  

trdyIslands :: ColoredNetwork -> [(ComponentID, CompAction)] -> [Bool] -> [Bool]
trdyIslands net act iconf = let isls = islSetToList $ transferIslands net
                            in (map (\(x,y) -> if y then (checkIslIO net x act) else y) (zip isls iconf))

makeNewState :: ColoredNetwork -> [Bool] -> [(ComponentID, SourceState)] -> [(ComponentID, CompAction)] -> String
makeNewState net iconf sconf act = let iconf' = trdyIslands net act iconf
                                       sh = sourceHash net
                                       ah = argHash net act sconf
                                       isls = islSetToList $ transferIslands net
                                       isls' = map (\(x,_) -> x) $ filter (\(_,x) -> x) (zip isls iconf')
                                       isls'' = map (\(x,_) -> x) $ filter (\(_,x) -> not x) (zip isls iconf')
                                       injected = L.nub $ filter (\x -> case getComponent net x of (Source _ _) -> True; _ -> False) $ concat $ map (\x -> getIns x net) isls'
                                       failedtoinj = (L.nub $ filter (\x -> case getComponent net x of (Source _ _) -> True; _ -> False) $ concat $ map (\x -> getIns x net) isls'') L.\\ injected 
                                       failedtoinj' = filter (\x -> case getCompAct x act of Inject -> True; _ -> False) failedtoinj
                                       nx = map (\x -> sh Hash.! x ++ " = next(" ++ ah Hash.! x ++ ")") failedtoinj'
                                       (res,rh) = makeNewState' net isls' sconf act (queueHash net)
                                       qh = queueHash net
                                       res' = map (\(x,y) -> qh Hash.! x ++ " = " ++ y) $ Hash.assocs rh
                                   in foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" $ L.nub nx ++ L.nub res ++ L.nub res' --map (\x -> makeIslTransfer net x sconf act) isls'

makeNewState' :: ColoredNetwork -> [Isle] -> [(ComponentID, SourceState)] -> [(ComponentID, CompAction)] -> Hash.Map ComponentID String -> ([String], Hash.Map ComponentID String)
makeNewState' _ [] _ _ qh = ([],qh)
makeNewState' net (x:xs) sconf act qh = let icomp = getIns x net
                                            ocomp = getOuts x net
                                            islid = noslashes $ show $ fromJust $ getIslID net x
                                            (res1,qh') = makeIslTransfer' net icomp qh
                                            qh'' = makeIslTransfer'' net ocomp act sconf islid icomp qh'
                                        in (res1 ++ fst (makeNewState' net xs sconf act qh''), snd (makeNewState' net xs sconf act qh''))


makeIslTransfer :: ColoredNetwork -> Isle -> [(ComponentID, SourceState)] -> [(ComponentID, CompAction)] -> [String]
makeIslTransfer net isl sconf act = let ah = argHash net act sconf
                                        qh = queueHash net
                                        sh = sourceHash net
                                        ch = chanHash net
                                        icomp = getIns isl net
                                        ocomp = getOuts isl net
                                        islid = fromJust $ getIslID net isl
                                        args = foldr (\a b -> case b of "" -> a ++ b; _ -> a ++ "," ++ b) ""
                                               (filter
                                               (\y -> y /= "")
                                               (map (\x -> case getComponent net x of
                                                             Source _ _ -> ah Hash.! x
                                                             Queue _ _ -> "[rhead(" ++ qh Hash.! x ++ ")]"
                                                             _ -> "") icomp))
                                        res = filter
                                              (\y -> y /= "")
                                              (map (\x -> case getComponent net x of
                                                            Source _ _ -> sh Hash.! x ++ " = free"
                                                            Queue _ _ -> qh Hash.! x ++ " = rtail(" ++ qh Hash.! x ++ ")"
                                                            _ -> "") icomp)
                                        res' = filter
                                               (\y -> y /= "")
                                               (map (\x -> case getComponent net x of
                                                             Queue _ _ -> case (getInChannels net x) of
                                                                            [] -> error "test1"
                                                                            _ -> if ((getInChannels net x) /= [])
                                                                                 then qh Hash.! x ++ " = IR_" ++ show islid ++ "_" ++ ch Hash.! (head (getInChannels net x)) ++ "(" ++ args ++")"
                                                                                 else error "test 9"
                                                             _ -> "") ocomp)
                                    in res ++ res'
              
makeIslTransfer' :: ColoredNetwork -> [ComponentID] -> Hash.Map ComponentID String -> ([String],Hash.Map ComponentID String)
makeIslTransfer' _ [] qh = ([],qh)
makeIslTransfer' net (x:xs) qh = let sh = sourceHash net
                                 in case getComponent net x of
                                      Source _ _ -> ([(sh Hash.! x ++ " = free")] ++ fst (makeIslTransfer' net xs qh), snd (makeIslTransfer' net xs qh))
                                      Queue _ _  -> (fst (makeIslTransfer' net xs (Hash.insert x ("rtail(" ++ qh Hash.! x ++ ")") qh)),
                                                     snd (makeIslTransfer' net xs (Hash.insert x ("rtail(" ++ qh Hash.! x ++ ")") qh)))
                                      _ -> (fst (makeIslTransfer' net xs qh), snd (makeIslTransfer' net xs qh))

makeIslTransfer'' :: ColoredNetwork -> [ComponentID] -> [(ComponentID, CompAction)] -> [(ComponentID, SourceState)] -> String -> [ComponentID] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
makeIslTransfer'' _ [] _ _ _ _ qh = qh
makeIslTransfer'' net (x:xs) act sconf islid icomp qh = let ah = argHash net act sconf
                                                            ch = chanHash net
                                                            qh' = queueHash net
                                                            args = foldr (\a b -> case b of "" -> a ++ b; _ -> a ++ "," ++ b) ""
                                                                   (filter
                                                                    (\y -> y /= "")
                                                                    (map (\z -> case getComponent net z of
                                                                                  Source _ _ -> ah Hash.! z
                                                                                  Queue _ _ -> "[rhead(" ++ qh' Hash.! z ++ ")]"
                                                                                  _ -> "") icomp))
                                                        in case getComponent net x of
                                                             Queue _ _ -> case getInChannels net x of
                                                                            [] -> error "test2"
                                                                            _ -> if ((getInChannels net x) /= [])
                                                                                 then let res = "IR_" ++ islid ++ "_" ++
                                                                                                ch Hash.! (head (getInChannels net x)) ++ "(" ++ args ++") ++ " ++ qh Hash.! x
                                                                                      in makeIslTransfer'' net xs act sconf islid icomp (Hash.insert x res qh)
                                                                                 else error "tes10"
                                                             _ -> makeIslTransfer'' net xs act sconf islid icomp qh
                                                                             
                                                           
isAllowed :: ColoredNetwork -> [Bool] -> [(ComponentID, SourceState)] -> [(ComponentID, CompAction)] -> Bool
isAllowed net iconf sconf act = let sconf' = filter (\(_,x) -> x == Next) sconf
                                    res = foldr (\x y -> x && y)
                                          True
                                          (map (\(x,_) -> if ((getCompAct x act) == Idle) then False else True) sconf')
                                    isls = map
                                           (\(x,_) -> x)
                                           (filter
                                           (\(_,x) -> x)
                                           (zip (islSetToList $ transferIslands net) iconf))
                                    islChans = concat $ map (\x -> islToChanIDs x) isls
                                    mergeActs = filter (\(x,_) -> case getComponent net x of
                                                                    (Merge _) -> True
                                                                    _ -> False) act
                                    res' = foldr (\x y -> x && y)
                                           True
                                           (map (\(x,y) -> case y of
                                                             MergeNone -> ((L.intersect islChans (getInChannels net x)) == [])
                                                             MergeIn a -> ((L.intersect islChans [a]) /= [])
                                                             _ -> False
                                                ) mergeActs)
                                in res && res'
                                          
--CompAction = Idle | Reject | Inject | Consume | MergeNone | MergeIn ChannelID
act2mcrl2decl :: CompAction -> String
act2mcrl2decl Idle = "idle"
act2mcrl2decl Reject = "reject"
act2mcrl2decl Inject = "inject:List(Color)"
act2mcrl2decl Consume = "consume:List(Color)"
act2mcrl2decl MergeNone = "mnone"
act2mcrl2decl (MergeIn _) = "mergein:Nat"

actionsDecl :: ColoredNetwork -> [(ComponentID,CompAction)] -> String
actionsDecl net act = let sh = sourceHash net
                          sih = sinkHash net
                          mh = mergeHash net
                          h = Hash.union mh $ Hash.union sh sih 
                      in unlines $ L.nub $ map (\(x,y) -> "\t" ++ h Hash.! x ++ "_" ++ act2mcrl2decl y ++ ";") act  

convAct :: ColoredNetwork -> [(ComponentID,SourceState)] -> [(ComponentID,CompAction)] -> String
convAct net sconf act = let ah = argHash net act sconf
                            sh = sourceHash net
                            sih = sinkHash net
                            mh = mergeHash net
                            h = Hash.union mh $ Hash.union sh sih 
                        in foldr (\a b -> case b of "" -> a ++ b; _ -> a ++ "|" ++ b) ""
                           (map (\(x,y) -> case y of
                                             Idle -> h Hash.! x ++ "_idle"
                                             Reject -> h Hash.! x ++ "_reject"
                                             Inject -> h Hash.! x ++ "_inject(" ++ ah Hash.! x ++ ")"
                                             Consume -> h Hash.! x ++ "_consume(" ++ ah Hash.! x ++ ")"
                                             MergeNone -> h Hash.! x ++ "_mnone"
                                             MergeIn chan -> let mouts = getInChannels net x
                                                                 i = fromJust $ L.elemIndex chan mouts
                                                             in h Hash.! x ++ "_mergein(" ++ noslashes (show i) ++ ")") act)



packetsToCond :: ComponentID -> [Color] -> Hash.Map ComponentID String -> String
packetsToCond i cs ah = makeTerm' "||" $ map (\x -> "(" ++ ah Hash.! i ++ " == [" ++ col2mcrl2 x ++ "])") cs

class ColorConv a where
  col2mcrl2 :: a -> String

instance ColorConv Color where
  col2mcrl2 (Color "" orvs) = "color(empty," ++ col2mcrl2 orvs ++ ")"
  col2mcrl2 (Color t orvs) = "color(" ++ noslashes (show t) ++ "," ++ col2mcrl2 orvs ++ ")"

instance ColorConv (OrValue VStruct) where
  col2mcrl2 (Left x) = "vstruct(" ++ col2mcrl2 x ++ ")"
  col2mcrl2 (Right x) = "value(" ++ col2mcrl2 x ++ ")"

instance ColorConv (OrValue Color) where
  col2mcrl2 (Left x) = "col(" ++ col2mcrl2 x ++ ")"
  col2mcrl2 (Right x) = "value(" ++ col2mcrl2 x ++ ")"

instance ColorConv VStruct where
  col2mcrl2 (VStruct hm) = "[" ++ foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y ) "" (map (\x -> col2mcrl2 x) (Hash.toList hm)) ++ "]"

instance ColorConv (Text, OrValue Color) where
  col2mcrl2 (t, orvc) = "ftextOrValOrCol(" ++ noslashes (show t) ++ "," ++ col2mcrl2 orvc ++ ")"

instance ColorConv Value where
  col2mcrl2 (Value i) = show i


class FunConv a where
  fun2mcrl2 :: String -> String -> a -> ConvState -> ConvState

instance FunConv MFunctionBool where
  fun2mcrl2 fname args (XMatch f1 f2) s = let ConvState nm ne i1 = fun2mcrl2 fname args f1 s 
                                              ConvState nm' ne' i2 = fun2mcrl2 fname args f2 (ConvState nm ne i1)
                                          in ConvState ([fname ++ "_" ++ show (i2+1) ++ " : List(Color) -> Bool;"] ++ nm') ([fname ++ "_" ++ show (i2+1) ++ "(" ++ args ++ ") = text(" ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ ")) == text(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ "));"] ++ ne') (i2+1)
  fun2mcrl2 fname args XTrue s = let ConvState m e i = s
                                     nm = [fname ++ "_" ++ show (i+1) ++ " : List(Color) -> Bool;"]
                                     ne = [fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = true;"]
                                 in ConvState (m ++ nm) (e ++ ne) (i+1)
  fun2mcrl2 fname args XFalse s = let ConvState m e i = s
                                      nm = [fname ++ "_" ++ show (i+1) ++ " : List(Color) -> Bool;"]
                                      ne = [fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = false;"]
                                  in ConvState (m ++ nm) (e ++ ne) (i+1)
  fun2mcrl2 fname args (XUnOpBool op f) s = let ConvState nm ne i = fun2mcrl2 fname args f s
                                                op' = opconv op
                                                nm' = [fname ++ "_" ++ show (i+1) ++ " : List(Color) -> Bool;"]
                                                ne' = [fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = " ++ op' ++ "(" ++ fname ++ "_" ++ show i ++ "(" ++ args ++ "));"]
                                            in ConvState (nm ++ nm') (ne ++ ne') (i+1)
  fun2mcrl2 fname args (XBinOpBool op f1 f2) s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args f1 s
                                                     ConvState nm2 ne2 i2 = fun2mcrl2 fname args f2 (ConvState nm1 ne1 i1)
                                                     op' = opconv op
                                                     nm' = [fname ++ "_" ++ show (i2+1) ++ " : List(Color) -> Bool;"]
                                                     ne' = [fname ++ "_" ++ show (i2+1) ++ "(" ++ args ++ ") = " ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ ") " ++ op' ++ " " ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ ");"]
                                                 in ConvState (nm2 ++ nm') (ne2 ++ ne') (i2+1)
  fun2mcrl2 fname args (XAppliedToB f gs) s = let (nargs,ns) = fun2mcrl2args fname args "" gs s
                                                  ns' = fun2mcrl2 fname ("[" ++ nargs ++ "]") f ns
                                              in ns'
  fun2mcrl2 fname args (XSelectB f h) s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args f s
                                              ConvState nm2 ne2 i2 = fun2mcrl2B fname (i1 + 1) args (Hash.toList h) (ConvState nm1 ne1 (i1 + 1))
                                              re = [fname ++ "_" ++ show (i2 + 1) ++ "(" ++ args ++  ") = " ++ fname ++ "_" ++ show (i1 + 1) ++ "(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ "));"]
                                              rm = [fname ++ "_" ++ show (i1 + 1) ++ " : Color -> Color;"] ++
                                                [fname ++ "_" ++ show (i2 + 1) ++ " : List(Color) -> Bool;"]
                                          in ConvState (rm ++ nm2) (re ++ ne2) (i2 + 1)
  fun2mcrl2 fname args (XIfThenElseB b f1 f2) s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args b s
                                                      ConvState nm2 ne2 i2 = fun2mcrl2 fname args f1 (ConvState nm1 ne1 i1)
                                                      ConvState nm3 ne3 i3 = fun2mcrl2 fname args f2 (ConvState nm2 ne2 i2)
                                                      re = [fname ++ "_" ++ show (i3+1) ++ "(" ++ args ++ ") = if(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ ")" ++ "," ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ ")," ++ fname ++ "_" ++ show i3 ++ "(" ++ args ++ "));"]
                                                      rm = [fname ++ "_" ++ show (i3+1) ++ " : List(Color) -> Color;"]
                                                  in ConvState (rm ++ nm3) (re ++ ne3) (i3+1)
  fun2mcrl2 _ _ _ s = s

instance FunConv MFunctionVal where
  fun2mcrl2 fname args (XConst j) s = let ConvState nm ne i = s
                                          nm' = [fname ++ "_" ++ show (i+1) ++ " : List(Color) -> ValOrColor;"]
                                          ne' = [fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = value(" ++ show j ++ ");"]
                                      in ConvState (nm ++ nm') (ne ++ ne') (i+1)
  fun2mcrl2 _ _ (XUnOp _ _) s = s
  fun2mcrl2 fname args (XBinOp op f1 f2) s = let op' = opconv op
                                                 ConvState nm1 ne1 i1 = fun2mcrl2 fname args f1 s
                                                 ConvState nm2 ne2 i2 = fun2mcrl2 fname args f2 (ConvState nm1 ne1 i1)
                                                 nm' = [fname ++ "_" ++ show (i2+1) ++ " : List(Color) -> ValOrColor;"]
                                                 ne' = [fname ++ "_" ++ show (i2+1) ++ "(" ++ args ++ ") = value(v(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ ")) " ++ noslashes (show op') ++ " v(" ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ "));"]
                                             in ConvState (nm2 ++ nm') (ne2 ++ ne') (i2+1)
  fun2mcrl2 fname args (XChooseVal _ f) s = let ConvState nm ne i = fun2mcrl2 fname args f s
                                                nm' = [fname ++ "_" ++ show (i+1) ++ " : List(Color) -> ValOrColor;"]
                                                ne' = [fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = value(val(valOrStruct(" ++ fname ++ "_" ++ show i ++ "(" ++ args ++ "))));"]
                                            in ConvState (nm ++ nm') (ne ++ ne') (i+1)
  fun2mcrl2 fname args (XGetFieldVal t f) s = let ConvState nm ne i = fun2mcrl2 fname args f s
                                                  nm' = [fname ++ "_" ++ show (i+1) ++ " : TXT # List(FTextValOrCol) -> ValOrColor;"] ++
                                                        [fname ++ "_" ++ show (i+2) ++ " : List(Color) -> ValOrColor;"]
                                                  ne' = ["ftext(head(l)) != z -> " ++ fname ++ "_" ++ show (i+1) ++ "(z,l) = " ++ fname ++ "_" ++ show (i+1) ++ "(z,tail(l));"] ++
                                                        ["ftext(head(l)) == z -> " ++ fname ++ "_" ++ show (i+1) ++ "(z,l) = valOrCol(head(l));"] ++
                                                        [fname ++ "_" ++ show (i+2) ++ "(" ++ args ++ ") = vs(" ++ fname ++ "_" ++ show (i+1) ++ "(" ++ noslashes (show t) ++ "," ++ fname ++ "_" ++ show i ++ "(" ++ args ++ ")));"]
                                              in ConvState (nm ++ nm') (ne ++ ne') (i+2)
  fun2mcrl2 fname args (XIfThenElseV b f f') s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args b s
                                                     ConvState nm2 ne2 i2 = fun2mcrl2 fname args f (ConvState nm1 ne1 i1)
                                                     ConvState nm3 ne3 i3 = fun2mcrl2 fname args f' (ConvState nm2 ne2 i2)
                                                     re = [fname ++ "_" ++ show (i3+1) ++ "(" ++ args ++ ") = if(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ ")" ++ "," ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ ")," ++ fname ++ "_" ++ show i3 ++ "(" ++ args ++ "));"]
                                                     rm = [fname ++ "_" ++ show (i3+1) ++ " : List(Color) -> Color;"]
                                                 in ConvState (rm ++ nm3) (re ++ ne3) (i3+1)                                    

instance FunConv MFunctionStruct where
  fun2mcrl2 fname args (XConcat mp) (ConvState m e i) = case (Hash.null mp) of
                                                          True -> ConvState ([fname ++ "_" ++ show (i+1) ++ " : List(Color) -> ValueOrVstruct;"] ++ m) ([fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = vstruct([]);"] ++ e) (i+1)
                                                          _ -> let (res,ConvState nm ne j) = vstr2mcrl2 fname args (Hash.toList mp) (ConvState m e i)
                                                                   nm' = [fname ++ "_" ++ show (j+1) ++ " : List(Color) -> ValueOrVstruct;"]
                                                                   ne' = [fname ++ "_" ++ show (j+1) ++ "(" ++ args ++ ") = vstruct([" ++ res ++ "]);"]
                                                               in ConvState (nm ++ nm') (ne ++ ne') (j+1)
  fun2mcrl2 fname args (XChooseStruct _ f) s = let ConvState nm ne i = fun2mcrl2 fname args f s
                                                   nm' = [fname ++ "_" ++ show (i+1) ++ " : List(Color) -> ValueOrVstruct;"]
                                                   ne' = [fname ++ "_" ++ show (i+1) ++ "(" ++ args ++ ") = valOrStruct(" ++ fname ++ "_" ++ show i ++ "(" ++ args ++ "));"]
                                               in ConvState (nm ++ nm') (ne ++ ne') (i+1)
  fun2mcrl2 fname args (XIfThenElseC b f f') s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args b s
                                                     ConvState nm2 ne2 i2 = fun2mcrl2 fname args f (ConvState nm1 ne1 i1)
                                                     ConvState nm3 ne3 i3 = fun2mcrl2 fname args f' (ConvState nm2 ne2 i2)
                                                     re = [fname ++ "_" ++ show (i3+1) ++ "(" ++ args ++ ") = if(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ ")" ++ "," ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ ")," ++ fname ++ "_" ++ show i3 ++ "(" ++ args ++ "));"]
                                                     rm = [fname ++ "_" ++ show (i3+1) ++ " : List(Color) -> ValueOrVstruct;"]
                                                 in ConvState (rm ++ nm3) (re ++ ne3) (i3+1)

instance FunConv MFunctionDisj where
  fun2mcrl2 fname args (XVar i) (ConvState m e j) = ConvState ([fname ++ "_" ++ show (j+1) ++ " : List(Color) -> Color;"] ++ m) ([fname ++ "_" ++ show (j+1) ++ "(" ++ args ++ ") = " ++ args ++ "." ++ show i ++ ";"] ++ e) (j+1)
  fun2mcrl2 fname args (XChoice t (Left m)) s = let ConvState nm ne i1 = fun2mcrl2 fname args m s
                                                    t' = case (noslashes (show t)) of "" -> "empty"; t'' -> t''
                                                in ConvState ([fname ++ "_" ++ show (i1+1) ++ " : List(Color) -> Color;"] ++ nm) ([fname ++ "_" ++ show (i1+1) ++ "(" ++ args ++ ") = color(" ++ t' ++ ", " ++ fname ++ "_" ++ show (i1) ++ "(" ++ args ++ "));"] ++ ne) (i1+1)
  fun2mcrl2 fname args (XChoice t (Right m)) s = let ConvState nm ne i1 = fun2mcrl2 fname args m s
                                                     t' = case (noslashes (show t)) of "" -> "empty"; t'' -> t''
                                                 in ConvState ([fname ++ "_" ++ show (i1+1) ++ " : List(Color) -> Color;"] ++ nm) ([fname ++ "_" ++ show (i1+1) ++ "(" ++ args ++ ") = color(" ++ t' ++ ", " ++ fname ++ "_" ++ show (i1) ++ "(" ++ args ++ "));"] ++ ne) (i1+1)
  fun2mcrl2 fname args (XSelect f h) s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args f s
                                             ConvState nm2 ne2 i2 = fun2mcrl2' fname (i1 + 1) args (Hash.toList h) (ConvState nm1 ne1 (i1 + 1))
                                             re = [fname ++ "_" ++ show (i2 + 2) ++ "(" ++ args ++  ") = " ++ fname ++ "_" ++ show (i1 + 1) ++ "(" ++ fname ++ "_" ++ show (i2 + 1) ++ "(" ++ args ++ ")," ++ args ++ ");"] ++
                                                  [fname ++ "_" ++ show (i2 + 1) ++ "(" ++ args ++ ") = text(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ "));"]
                                             rm = [fname ++ "_" ++ show (i1 + 1) ++ " : TXT # List(Color) -> Color;"] ++
                                                  [fname ++ "_" ++ show (i2 + 1) ++ " : List(Color) -> TXT;"] ++
                                                  [fname ++ "_" ++ show (i2 + 2) ++ " : List(Color) -> Color;"]
                                         in ConvState (rm ++ nm2) (re ++ ne2) (i2 + 2)
  fun2mcrl2 fname args (XIfThenElseD b f f') s = let ConvState nm1 ne1 i1 = fun2mcrl2 fname args b s
                                                     ConvState nm2 ne2 i2 = fun2mcrl2 fname args f (ConvState nm1 ne1 i1)
                                                     ConvState nm3 ne3 i3 = fun2mcrl2 fname args f' (ConvState nm2 ne2 i2)
                                                     re = [fname ++ "_" ++ show (i3+1) ++ "(" ++ args ++ ") = if(" ++ fname ++ "_" ++ show i1 ++ "(" ++ args ++ ")" ++ "," ++ fname ++ "_" ++ show i2 ++ "(" ++ args ++ ")," ++ fname ++ "_" ++ show i3 ++ "(" ++ args ++ "));"]
                                                     rm = [fname ++ "_" ++ show (i3+1) ++ " : List(Color) -> Color;"]
                                                 in ConvState (rm ++ nm3) (re ++ ne3) (i3+1)
  fun2mcrl2 fname args (XAppliedTo f gs) s = let (nargs,ns) = fun2mcrl2args fname args "" gs s
                                                 ns' = fun2mcrl2 fname ("[" ++ nargs ++ "]") f ns
                                             in ns'
  fun2mcrl2 fname args (XGetFieldDisj t str) s = let ConvState nm ne i = fun2mcrl2 fname args str s
                                                     nm' = [fname ++ "_" ++ show (i+1) ++ " : TXT # List(FTextValOrCol) -> ValOrColor;"] ++
                                                           [fname ++ "_" ++ show (i+2) ++ " : List(Color) -> Color;"]
                                                     ne' = ["ftext(head(l)) != t -> " ++ fname ++ "_" ++ show (i+1) ++ "(t,l) = " ++ fname ++ "_" ++ show (i+1) ++ "(t,tail(l));"] ++
                                                           ["ftext(head(l)) == t -> " ++ fname ++ "_" ++ show (i+1) ++ "(t,l) = valOrCol(head(l));"] ++
                                                           [fname ++ "_" ++ show (i+2) ++ "(" ++ args ++ ") = c(" ++ fname ++ "_" ++ show (i+1) ++ "(" ++ noslashes (show t) ++ ",vs(" ++ fname ++ "_" ++ show i ++ "(" ++ args ++ "))));"]
                                                 in ConvState (nm ++ nm') (ne ++ ne') (i+2)
  fun2mcrl2 _ _ _ s = s

fun2mcrl2args :: String -> String -> String -> [MFunctionDisj] -> ConvState -> (String,ConvState)
fun2mcrl2args _ _ res [] s = (res,s)
fun2mcrl2args fname args res (x:xs) s = let ConvState nm ne i = fun2mcrl2 fname args x s
                                        in case res of
                                             "" -> fun2mcrl2args fname args (fname ++ "_" ++ show i ++ "(" ++ args ++ ")") xs (ConvState nm ne i)
                                             _ -> fun2mcrl2args fname args (res ++ "," ++ fname ++ "_" ++ show i ++ "(" ++ args ++ ")") xs (ConvState nm ne i)

--TODO: refactor the following two functions
fun2mcrl2' :: String -> Int -> String -> [(Text,MFunctionDisj)] -> ConvState -> ConvState
fun2mcrl2' _ _ _ [] s = s
fun2mcrl2' fname i args ((t,f):xs) s = let ConvState nm ne j = fun2mcrl2 fname args f s
                                           re = ["t == " ++ (noslashes (show t)) ++ " -> " ++ fname ++ "_" ++ show i ++ "(t," ++ args ++ ") = " ++ fname ++ "_" ++ show j ++ "(" ++ args ++ ");"]
                                           --re = [fname ++ "_" ++ show i ++ "(" ++ (noslashes (show t)) ++ ") = " ++ fname ++ "_" ++ show j ++ "(" ++ args ++ ");"]
                                       in fun2mcrl2' fname i args xs (ConvState nm (re ++ ne) j)

fun2mcrl2B :: String -> Int -> String -> [(Text,MFunctionBool)] -> ConvState -> ConvState
fun2mcrl2B _ _ _ [] s = s
fun2mcrl2B fname i args ((t,f):xs) s = let ConvState nm ne j = fun2mcrl2 fname args f s
                                           re = [fname ++ "_" ++ show i ++ "(" ++ (noslashes (show t)) ++ ") = " ++ fname ++ "_" ++ show j ++ "(" ++ args ++ ");"]
                                       in fun2mcrl2B fname i args xs (ConvState nm (re ++ ne) j)

vstr2mcrl2 :: String -> String -> [(Text,Either MFunctionDisj MFunctionVal)] -> ConvState -> (String,ConvState)
vstr2mcrl2 _ _ [] s = ("",s)
vstr2mcrl2 fname args ((t,(Left f)):[]) (ConvState m e i) = let ConvState nm ne j = fun2mcrl2 fname args f (ConvState m e i)
                                                            in ("ftextOrValOrCol(" ++ noslashes (show t) ++ ",col(" ++ fname ++ "_" ++ show j ++ "("++ args ++ ")" ++ "))",ConvState (m ++ nm) (e ++ ne) j)
vstr2mcrl2 fname args ((t,(Right f)):[]) (ConvState m e i) = let ConvState nm ne j = fun2mcrl2 fname args f (ConvState m e i)
                                                             in ("ftextOrValOrCol(" ++ noslashes (show t) ++ ",col(" ++ fname ++ "_" ++ show j ++ "("++ args ++ ")" ++ "))",ConvState (m ++ nm) (e ++ ne) j)
vstr2mcrl2 fname args ((t,(Left f)):xs) (ConvState m e i) = let ConvState nm ne j = fun2mcrl2 fname args f (ConvState m e i)
                                                                (res,s) = vstr2mcrl2 fname args xs (ConvState nm ne j)
                                                            in ("ftextOrValOrCol(" ++ noslashes (show t) ++ ",col(" ++ fname ++ "_" ++ show j ++ "("++ args ++ ")" ++ "))," ++ res,s)
vstr2mcrl2 fname args ((t,(Right f)):xs) (ConvState m e i) = let ConvState nm ne j = fun2mcrl2 fname args f (ConvState m e i)
                                                                 (res,s) = vstr2mcrl2 fname args xs (ConvState nm ne j)
                                                             in ("ftextOrValOrCol(" ++ noslashes (show t) ++ ",col(" ++ fname ++ "_" ++ show j ++ "("++ args ++ ")" ++ "))," ++ res,s)

class OpConv a where
  opconv :: a -> String

instance OpConv ComparisonOperator where
  opconv Eq = "=="
  opconv Gt = ">"

instance OpConv UnaryOperatorBool where
  opconv Not = "!"

instance OpConv BinaryOperatorBool where
  opconv Or = "||"
  opconv And = "&&"

instance OpConv BinaryOperator where
  opconv Plus = "+"
  opconv Minus = "-"
  opconv Mult = "*"
  opconv Mod = "mod"


initConvState :: ConvState
initConvState = ConvState ["R_fork_1 : List(Color) -> List(Color);",
                           "R_fork_1 : List(Color) -> List(Color);",
                           "R_ctrljoin : List(Color) # List(Color) -> List(Color);",
                           "R_merge : List(Color) -> List(Color);"]
                          ["R_fork_1(x) = x;",
                           "R_fork_2(x) = x;",
                           "R_cltrjoin(x,y) = x;",
                           "R_merge(x) = x;"]
                           0

convInitState :: ConvState
convInitState = ConvState [] [] 0

makeSpec :: ColoredNetwork -> MFunctionDisj -> String
makeSpec net fun = let (ConvState m e _) = fun2mcrl2 "R" "x" fun (ConvState [] [] 0)
                   in functionHeader net ++ "\nmap\n" ++ makeSpec' m ++ "eqn\n" ++ makeSpec' e
  where makeSpec' :: [String] -> String
        makeSpec' [] = ""
        makeSpec' (x:xs) = "\t" ++ show x ++ "\n" ++ makeSpec' xs                                

funConv :: ColoredNetwork -> ComponentID -> ConvState
funConv net cid = case (getComponent net cid) of
                    (Function _ fun _) -> let fm = funHash net
                                              funval = fm Hash.! cid
                                              (ConvState m e i) = fun2mcrl2 funval "x" fun convInitState
                                              nm = [funval ++ " : List(Color) -> List(Color);"]
                                              ne = ["#x > 0 -> " ++ funval ++ "(x) = [" ++ funval ++ "_" ++ show i ++ "(x)];",
                                                    "#x == 0 -> " ++ funval ++ "(x) = [];"]
                                          in ConvState (nm ++ m) (ne ++ e) i
                    (Switch _ funs) -> let fm = funHash net
                                           ch = chanHash net
                                           funval = fm Hash.! cid
                                       in funConvSwitch (getOutChannels net cid) funval "x" ch funs convInitState
                    (FControlJoin _ fun) -> let fm = funHash net
                                                funval = fm Hash.! cid
                                                (ConvState m e i) = fun2mcrl2 ("FR_" ++ funval) "x" fun convInitState
                                                nm = [funval ++ " : List(Color) -> List(Color);"]
                                                ne = [funval ++ "_" ++ show i ++ " == true -> " ++ funval ++ "_" ++ "(x) = x;",
                                                      funval ++ "_" ++ show i ++ " == false -> " ++ funval ++ "_" ++ "(x) = [];"]
                                            in ConvState (nm ++ m) (ne ++ e) i
                    _ -> convInitState

--refactor
funConvSwitch :: [ChannelID] -> String -> String -> Hash.Map ChannelID String -> [MFunctionBool] -> ConvState -> ConvState
funConvSwitch _ _ _ _ [] s = s
funConvSwitch j n arg ch (x:xs) (ConvState m e _) = let k = ch Hash.! (head j)
                                                        (ConvState nm ne i) = fun2mcrl2 (n ++ "_" ++ k) arg x (ConvState m e 0)
                                                        nm1 = [n ++ "_" ++ k  ++ " : List(Color) -> List(Color);"]
                                                        ne1 = [n ++ "_" ++ k ++ "_" ++ show i ++ "(" ++ arg ++ ") == true -> " ++ n ++ "_" ++ k ++ "(x) = x;",
                                                               n ++ "_" ++ k ++ "_" ++ show i ++ "(" ++ arg ++ ") == false -> " ++ n ++ "_" ++ k ++ "(x) = [];"]
                                                    in funConvSwitch (tail j) n arg ch xs (ConvState (nm1 ++ nm) (ne1 ++ ne) 0)

islRules :: ColoredNetwork -> Isle -> ConvState
islRules net isl = let pf = funcPropagation net isl
                       ins = getIslIns isl net
                       outs = getIslOuts isl net
                       ch = chanHash net
                   in islRules' (L.length ins) (fromJust $ getIslID net isl) ch outs pf convInitState
  where islRules' :: Int -> Int -> Hash.Map ChannelID String -> [ChannelID] -> [(ChannelID,String)] -> ConvState -> ConvState --(z:zh) - outs, f - funcPropagation
        islRules' _ _ _ [] _ s = s
        islRules' a islid h (z:zs) f (ConvState m e _) = let args = foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" ["x" ++ show i | i <- [0..(a-1)]]
                                                             types = (foldr (\x (y::String) -> case y of "" -> x ++ y; _ -> x ++ " # " ++ y) "" (replicate a "List(Color)")) ++ " -> List(Color)"
                                                             nm = ["IR_" ++ show islid ++ "_" ++ h Hash.! z ++ " : " ++ types ++ ";"]
                                                             res = if ((filter (\(k,_) -> k == z) f) == [])
                                                                   then error ("test3 --" ++ show f ++ "--" ++ show (z:zs))
                                                                   else snd (head (filter (\(k,_) -> k == z) f))
                                                             ne = ["IR_" ++ show islid ++ "_" ++ h Hash.! z ++ "(" ++ args ++ ") = " ++ res ++ ";"]
                                                         in islRules' a islid h zs f (ConvState (m ++ nm) (e ++ ne) 0)

getAllFunctions :: ColoredNetwork -> [XComponent Text]
getAllFunctions network = filter (\x -> case x of Function _ _ _ -> True; _ -> False) $ getComponents network

getReturnType :: (XComponent Text) -> Maybe ColorSet
getReturnType (Function _ _ r) = Just r
getReturnType _ = Nothing

noslashes :: String -> String
noslashes str = filter (\x -> x /= '\"') str

--test functions
test :: ColoredNetwork -> String
test net = let mf = getFunctionFunc $ head $ getAllFunctions net
           in case mf of
                Nothing -> "No functions in the network"
                Just fun -> show fun ++ "\n" ++ makeSpec net testFun7 --functionHeader net ++ "\n" ++ show (fun2mcrl2 testFun5 (ConvState [] (Hash.empty) [] 0))

testSourceColors :: ColoredNetwork -> ColorSet
testSourceColors net = let sources = getAllSources net
                           (Source _ c) = head sources
                       in c

{-
testFunCond :: ColoredNetwork -> String
testFunCond net = let isls = islSetToList $ transferIslands net
                      acts = makeActions net
                  in unlines $ map (\(a,b) -> show a ++ "***" ++ show b ++ "***" ++ funCond net a b) [(x,y)| x <- isls, y <- acts]
-}

testIsAllowed :: ColoredNetwork -> [([Bool],[(ComponentID, SourceState)],[(ComponentID, CompAction)],Bool)]
testIsAllowed net = let iconf = makeIslConf 2
                        sconf = makeSourceConfs net
                        act = makeActions net
                    in map (\(x,y,z) -> (x,y,z,isAllowed net x y z)) [(i,s,a)|i <- iconf, s <- sconf, a <- act]

testCond :: ColoredNetwork -> String
testCond net = let iconf = [[False,False],[False,True],[True,False],[True,True]]
                   acts = makeActions net
                   sconf = makeSourceConfs net
               in unlines $ map (\(x,y,z) -> makeCond net x y z) [(x,y,z)| x <- iconf, y <- sconf, z <- acts]

{-
testInpGroups :: ColoredNetwork -> [([ChannelID],[ChannelID])]
testInpGroups net = let isls = transferIslands net
                        ins = \x -> getIslIns x net
                    in map (\x -> getInpGroups net (ins x)) $ islSetToList isls
-}

--funConv :: ColoredNetwork -> ComponentID -> ConvState

allFunConv :: ColoredNetwork -> ConvState
allFunConv net = let funs = map (\(x,_) -> x) $ getAllFunctionsWithID net --getAllFunctionsWithID net ++ getAllSwitchesWithID net ++ getAllFJoinsWithID net 
                     switches = map (\(x,_) -> x) $ getAllSwitchesWithID net
                     joins = map (\(x,_) -> x) $ getAllFJoinsWithID net
                     isls = islSetToList $ transferIslands net
                     res = (map (\x -> funConv net x) funs) ++
                           (map (\x -> funConv net x) switches) ++
                           (map (\x -> funConv net x) joins) ++
                           (map (\x -> islRules net x) isls)
                 in foldr (\(ConvState m1 e1 _) (ConvState m2 e2 _) -> (ConvState (m1 ++ m2) (e1 ++ e2) 0)) convInitState res
                  

testProp :: ColoredNetwork -> [[(ChannelID,String)]]
testProp net = let isls = islSetToList $ transferIslands net
               in map (\x -> funcPropagation net x) isls

testCol1 :: Color
testCol1 = Color "red" (Left (VStruct Hash.empty))

testSConf :: ColoredNetwork -> [(ComponentID,SourceState)]
testSConf net = L.head $ makeSourceConfs net  

testSConf1 :: ColoredNetwork -> [(ComponentID,SourceState)]
testSConf1 net = (makeSourceConfs net) !! 1  

testFun1 :: MFunctionDisj
testFun1 = XVar 1

testFun2 :: MFunctionStruct
testFun2 = (XConcat Hash.empty)

testFun3 :: MFunctionDisj
testFun3 = (XChoice "blue" (Left (XConcat Hash.empty)))

testFun4 :: MFunctionBool
testFun4 = (XMatch (XVar 0) (XChoice "blue" (Left (XConcat Hash.empty))))

testFun5 :: MFunctionDisj
testFun5 = (XIfThenElseD testFun4 (XChoice "red" (Left (XConcat Hash.empty))) (XChoice "blue" (Left (XConcat Hash.empty))))

testFun6 :: MFunctionDisj
testFun6 = XSelect (XVar 0) (Hash.fromList [("red",XChoice "blue" (Left (XConcat Hash.empty))), ("blue",XChoice "red" (Left (XConcat Hash.empty)))])

testFun7 :: MFunctionDisj
testFun7 = XGetFieldDisj "left" (XChooseStruct "" (XVar 0))

testFun8 :: MFunctionVal
testFun8 = (XConst 10)

testFun9 :: MFunctionVal
testFun9 = (XBinOp Plus (XConst 2) (XConst 3))

testFun10 :: MFunctionVal
testFun10 = (XChooseVal "" (XChoice "blue" (Right (XConst 10))))

testFun11 :: MFunctionDisj
testFun11 = (XChoice "blue" (Right (XConst 10)))

testFun12 :: MFunctionVal
testFun12 = (XGetFieldVal "left" (XChooseStruct "" (XVar 0)))

testFun13 :: MFunctionBool
testFun13 = XTrue

testFun14 :: MFunctionBool
testFun14 = (XUnOpBool Not (XTrue))

testFun15 :: MFunctionBool
testFun15 = (XBinOpBool And (XTrue) (XFalse))

testFun16 :: MFunctionBool
testFun16 = XSelectB (XVar 0) (Hash.fromList [("red",XTrue), ("blue",XFalse)])

testFun17 :: MFunctionBool
testFun17 = (XIfThenElseB XTrue XFalse XTrue)

testFun18 :: MFunctionStruct
testFun18 = (XIfThenElseC 
             (XBinOpBool And (XMatch (XGetFieldDisj "left" (XChooseStruct "" (XVar 0))) (XChoice "blue" (Left (XConcat Hash.empty)))) 
              (XMatch (XGetFieldDisj "right" (XChooseStruct "" (XVar 0))) (XChoice "red" (Left (XConcat Hash.empty))))) 
             (XConcat (Hash.fromList [("right",Left (XChoice "blue" (Left (XConcat Hash.empty)))),("left",Left (XChoice "red" (Left (XConcat Hash.empty))))])) 
             (XChooseStruct "" (XVar 0)))

testFun19 :: MFunctionStruct
testFun19 = (XConcat (Hash.fromList [("right",Left (XChoice "blue" (Left (XConcat Hash.empty)))),("left",Left (XChoice "red" (Left (XConcat Hash.empty))))]))

--function (takes a function primitive, returns the primitive's function)
getFunctionFunc :: (XComponent Text) -> Maybe MFunctionDisj
getFunctionFunc (Function _ f _) = Just f
getFunctionFunc _ = Nothing

getFControlJoinPred :: (XComponent Text) -> Maybe MFunctionBool
getFControlJoinPred (FControlJoin _ f) = Just f
getFControlJoinPred _ = Nothing

getSwitchPred :: (XComponent Text) -> Maybe [MFunctionBool]
getSwitchPred (Switch _ fs) = Just fs
getSwitchPred _ = Nothing

{-
getSourceAct :: Action -> ComponentID -> Maybe SourceAction
getSourceAct (a,_,_) i = let a' = filter (\(j,_) -> if (j == i) then True else False) a
                         in if (a' /= []) then (Just (snd (head a'))) else Nothing

getSinkAct :: Action -> ComponentID -> Maybe SinkAction
getSinkAct (_,a,_) i = let a' = filter (\(j,_) -> if (j == i) then True else False) a
                       in if (a' /= []) then (Just (snd (head a'))) else Nothing

getMergeAct :: Action -> ComponentID -> Maybe MergeAction
getMergeAct (_,_,a) i = let a' = filter (\(j,_) -> if (j == i) then True else False) a
                        in if (a' /= []) then (Just (snd (head a'))) else Nothing
-}

computeAllOuts :: Show a => [(ChannelID, Color)] -> ColoredNetwork -> (Island a) -> [(ChannelID, Color)]
computeAllOuts xs net isl = Set.toList . Set.fromList . L.sort . concat $ map (\x -> computeOuts x net isl) xs

computeOuts :: Show a => (ChannelID, Color) -> ColoredNetwork -> (Island a) -> [(ChannelID, Color)]
computeOuts x net island = let o = Set.fromList $ getOutChannels net $ getTarget net $ fst x
                               ic = Set.fromList $ islToChanIDs island
                           in case Set.null $ Set.intersection o ic of
                                False -> computeOuts' x net island
                                True -> [x]
  where computeOuts' :: Show a => (ChannelID, Color) -> ColoredNetwork -> (Island a) -> [(ChannelID, Color)]
        computeOuts' (i,c) n isl = let comp = getComponent n (getTarget n i)
                                   in case comp of
                                        Source _ _ -> let couts = filter (\t -> elem t (islToChanIDs isl))
                                                                  (getOutChannels n (getTarget n i))
                                                      in concat (map (\w -> computeOuts w n isl)
                                                                 (map (\z -> (z,c)) couts))
                                        Sink _ -> let couts = filter (\t -> elem t (islToChanIDs isl))
                                                              (getOutChannels n (getTarget n i))
                                                  in map (\z -> (z,c)) couts
                                        Function _ f _ -> let couts = filter (\t -> elem t (islToChanIDs isl))
                                                                      (getOutChannels n (getTarget n i))
                                                          in case length couts of
                                                               0 -> []
                                                               1 -> let o = head couts
                                                                        (res :: Color) = eval (makeVArguments [c]) f
                                                                    in computeOuts (o, res) n isl
                                                               _ -> error "computeOuts: function error"
                                        Queue _ _ -> let couts = filter (\t -> elem t (islToChanIDs isl))
                                                                 (getOutChannels n (getTarget n i))
                                                     in concat (map (\w -> computeOuts w n isl)
                                                                 (map (\z -> (z,c)) couts))
                                        Switch _ fs -> let outs = getOutChannels n (getTarget n i)
                                                           (rs:: [Bool]) = map (\t -> eval (makeVArguments [c]) t) fs
                                                           couts = (filter (\(z,_) -> elem z (islToChanIDs isl))
                                                                     (map (\(t,_) -> (t,c)) (filter (\(_,b) -> b) (zip outs rs))))
                                                       in concat (map (\w -> computeOuts w n isl) couts)
                                        Merge _ -> let couts = filter (\t -> elem t (islToChanIDs isl))
                                                               (getOutChannels n (getTarget n i))
                                                   in concat (map (\w -> computeOuts w n isl) (map (\z -> (z,c)) couts))
                                        Fork _ -> let couts = filter (\t -> elem t (islToChanIDs isl))
                                                              (getOutChannels n (getTarget n i))
                                                  in concat (map (\w -> computeOuts w n isl) (map (\z -> (z,c)) couts))
                                        ControlJoin _ -> let j = head (getInChannels n (getTarget n i))
                                                         in case i == j of
                                                              True -> computeOuts (head (getOutChannels n (getTarget n i)),c) n isl
                                                              False -> []
                                        FControlJoin _ f -> let couts = getOutChannels n (getTarget n i)
                                                            in case eval (makeVArguments [c]) f of
                                                                 True -> concat (map (\w -> computeOuts w n isl)
                                                                                  (map (\t -> (t,c)) couts))
                                                                 _ -> []
                                        _ -> error "computeOuts: the component of this type is unexpected(Other)"


elem' :: Eq a => (a,b) -> [(a,b)] -> Bool
elem' (_,_) [] = False
elem' (x,z) ((y,_):ys)
  | x == y = True
  | otherwise = elem' (x,z) ys

uniqueIDs :: Eq a => [(a,b)] -> Bool
uniqueIDs [] = True
uniqueIDs (x:xs) = (not (elem' x xs)) && (uniqueIDs xs)

makeSourceConfs :: ColoredNetwork -> [[(ComponentID,SourceState)]]
makeSourceConfs network = Set.toList (Set.fromList (map (\j -> L.sort j) (filter (\t -> uniqueIDs t) (replicateM (length $ getAllSources network) $ getAllSourceStates network))))

getSourceStates :: ComponentID -> [(ComponentID, SourceState)]
getSourceStates i = [(i,Free),(i,Next)]

getAllSourceStates :: ColoredNetwork -> [(ComponentID, SourceState)]
getAllSourceStates net = let s = map (\(i,_) -> i) (getAllSourcesWithID net) in concat (map (\t -> getSourceStates t) s)

makeIslConf :: Int -> [[Bool]]
makeIslConf l = replicateM l [False, True]

getSourceConf :: ComponentID -> [(ComponentID,SourceState)] -> SourceState
getSourceConf i conf = if (filter (\(x,_) -> i == x) conf /= [])
                       then snd $ head $ filter (\(x,_) -> i == x) conf
                       else error "test 4"

isSource :: (XComponent Text) -> Bool
isSource (Source _ _) = True
isSource (PatientSource _ _) = True
isSource _ = False

isMerge :: (XComponent Text) -> Bool
isMerge (Merge _) = True
isMerge _ = False

isSink :: (XComponent Text) -> Bool
isSink (Sink _) = True
isSink _ = False

getMaxIslInputs :: ColoredNetwork -> Int
getMaxIslInputs net = getMaxIslInputs' 0 $ map (\x -> getIslIns x net) (islSetToList $ transferIslands net)
  where getMaxIslInputs' :: Int -> [[ChannelID]] -> Int
        getMaxIslInputs' res [] = res
        getMaxIslInputs' res (x:xs) = if (res < length x)
                                      then getMaxIslInputs' (length x) xs
                                      else getMaxIslInputs' res xs

argHash :: ColoredNetwork -> [(ComponentID, CompAction)] -> [(ComponentID,SourceState)] -> Hash.Map ComponentID String
argHash net act sconf = argHash'' net sconf $ argHash' net act Hash.empty 
  where argHash' :: ColoredNetwork -> [(ComponentID, CompAction)] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        argHash' _ [] hs = hs
        argHash' n ((x,a):xs) hs = case getComponent n x of
                                     (Source _ _) -> if (a == Inject)
                                                     then argHash' n xs (if (not $ Hash.member x hs) then (Hash.insert x ("y" ++ (show $ Hash.size hs)) hs) else hs)
                                                     else argHash' n xs hs
                                     (Sink _) -> if (a == Consume)
                                                 then argHash' n xs (if (not $ Hash.member x hs) then (Hash.insert x ("y" ++ (show $ Hash.size hs)) hs) else hs)
                                                 else argHash' n xs hs
                                     _ -> argHash' n xs hs
        argHash'' :: ColoredNetwork -> [(ComponentID,SourceState)] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        argHash'' _ [] hs = hs
        argHash'' n ((_,Free):xs) hs = argHash'' n xs hs
        argHash'' n ((x,Next):xs) hs = argHash'' n xs (if (not $ Hash.member x hs) then (Hash.insert x ("y" ++ (show $ Hash.size hs)) hs) else hs)
                                           
funHash :: ColoredNetwork -> Hash.Map ComponentID String
funHash net = let ids = map (\(x,_) -> x) $ getAllFunctionsWithID net ++ getAllSwitchesWithID net ++ getAllFJoinsWithID net
              in funHash' ids Hash.empty
  where funHash' :: [ComponentID] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        funHash' [] hs = hs
        funHash' (x:xs) hs = funHash' xs (Hash.insert x ("FR_" ++ (show $ Hash.size hs)) hs)

chanHash :: ColoredNetwork -> Hash.Map ChannelID String
chanHash net = let ids = getChannelIDs net
               in chanHash' ids Hash.empty
  where chanHash' :: [ChannelID] -> Hash.Map ChannelID String -> Hash.Map ChannelID String
        chanHash' [] hs = hs
        chanHash' (x:xs) hs = chanHash' xs (Hash.insert x (show $ Hash.size hs) hs)

queueHash :: ColoredNetwork -> Hash.Map ComponentID String
queueHash net = let ids = map (\(x,_) -> x) $ getAllQueuesWithID net
                in queueHash' ids Hash.empty
  where queueHash' :: [ComponentID] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        queueHash' [] hs = hs
        queueHash' (x:xs) hs = queueHash' xs (Hash.insert x ("q_" ++ (show $ Hash.size hs)) hs)

sourceHash :: ColoredNetwork -> Hash.Map ComponentID String
sourceHash net = let ids = map (\(x,_) -> x) $ getAllSourcesWithID net
                 in sourceHash' ids Hash.empty
  where sourceHash' :: [ComponentID] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        sourceHash' [] hs = hs
        sourceHash' (x:xs) hs = sourceHash' xs (Hash.insert x ("s_" ++ (show $ Hash.size hs)) hs)

sinkHash :: ColoredNetwork -> Hash.Map ComponentID String
sinkHash net = let ids = map (\(x,_) -> x) $ getAllSinksWithID net
               in sinkHash' ids Hash.empty
  where sinkHash' :: [ComponentID] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        sinkHash' [] hs = hs
        sinkHash' (x:xs) hs = sinkHash' xs (Hash.insert x ("si_" ++ (show $ Hash.size hs)) hs)        

mergeHash :: ColoredNetwork -> Hash.Map ComponentID String
mergeHash net = let ids = map (\(x,_) -> x) $ getAllMergesWithID net
               in mergeHash' ids Hash.empty
  where mergeHash' :: [ComponentID] -> Hash.Map ComponentID String -> Hash.Map ComponentID String
        mergeHash' [] hs = hs
        mergeHash' (x:xs) hs = mergeHash' xs (Hash.insert x ("m_" ++ (show $ Hash.size hs)) hs) 

getIslID :: ColoredNetwork -> Isle -> Maybe Int
getIslID net i = let isls = IM.assocs $ transferIslands net
                 in getIslID' isls
  where getIslID' :: [(Int, Isle)] -> Maybe Int
        getIslID' [] = Nothing
        getIslID' ((x,y):xs)
          | i == y = Just x
          | otherwise = getIslID' xs

funcPropagation :: ColoredNetwork -> (Island a) -> [(ChannelID,String)]
funcPropagation net isl = let h = funHash net
                              ins = getIslIns isl net
                              islChans = islToChanIDs isl
                          in funcPropagation' h ins islChans (map (\x -> (x,"x" ++ show (fromJust $ L.elemIndex x ins))) ins)
  where funcPropagation' :: Hash.Map ComponentID String -> [ChannelID] -> [ChannelID] -> [(ChannelID,String)] -> [(ChannelID,String)]
        funcPropagation' _ [] _ res = res
        funcPropagation' h (x:xs) ic res = let targ = getTarget net x
                                               getPrevArg = \((c::ChannelID),zs) -> snd $ head $ filter (\(a,_) -> a == c) zs
                                               onlyids = \r -> map (\(z,_) -> z) r
                                           in case getComponent net targ of
                                                (Function _ _ _) -> let res' = ([(head $ getOutChannels net targ,
                                                                                  h Hash.! targ ++ "(" ++ getPrevArg (x,res) ++ ")")] ++
                                                                                (filter (\(z,_) -> z /= x) res))
                                                                    in funcPropagation'
                                                                       h
                                                                       (onlyids res')
                                                                       ic
                                                                       res'
                                                (Fork _) -> let res' = ([((getOutChannels net targ) !! 0,
                                                                          getPrevArg (x,res)),
                                                                         ((getOutChannels net targ) !! 1,
                                                                          getPrevArg (x,res))] ++
                                                                        (filter (\(z,_) -> z /= x) res))
                                                            in funcPropagation'
                                                               h
                                                               (onlyids res')
                                                               ic
                                                               res'
                                                (ControlJoin _) -> let jinps = getInChannels net targ
                                                                       res' = ([((getOutChannels net targ) !! 0,
                                                                                 getPrevArg (x,res))] ++
                                                                               (filter (\(z,_) -> ((z /= jinps !! 0) && (z /= jinps !! 1))) res))
                                                                   in if (x == head jinps)
                                                                      then funcPropagation'
                                                                           h
                                                                           (onlyids res')
                                                                           ic
                                                                           res'
                                                                      else funcPropagation'
                                                                           h
                                                                           xs
                                                                           ic
                                                                           res
                                                (FControlJoin _ _) -> let res' = ([(head $ L.intersect (getOutChannels net targ) ic,
                                                                                    "W" ++ h Hash.! targ ++ "(" ++ getPrevArg (x,res) ++ ")")] ++
                                                                                  (filter (\(z,_) -> z /= x) res))
                                                                      in funcPropagation'
                                                                         h
                                                                         (onlyids res')
                                                                         ic
                                                                         res'
                                                (Switch _ _) -> let outid = head $ L.intersect (getOutChannels net targ) ic
                                                                    ch = chanHash net
                                                                    res' = ([(head $ L.intersect (getOutChannels net targ) ic,
                                                                              h Hash.! targ ++ "_" ++ ch Hash.! outid ++ "(" ++ getPrevArg (x,res) ++ ")")] ++
                                                                            (filter (\(z,_) -> z /= x) res))
                                                                in funcPropagation'
                                                                   h
                                                                   (onlyids res')
                                                                   ic
                                                                   res'
                                                (Merge _) -> let res' = ([(head $ getOutChannels net targ,
                                                                           getPrevArg (x,res))] ++
                                                                         (filter (\(z,_) -> z /= x) res))
                                                             in funcPropagation'
                                                                h
                                                                (onlyids res')
                                                                ic
                                                                res'
                                                _ -> funcPropagation' h xs ic res




