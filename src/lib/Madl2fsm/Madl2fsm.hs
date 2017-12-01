{-# LANGUAGE OverloadedStrings, ScopedTypeVariables#-}
module Madl2fsm.Madl2fsm
where

import Madl.MsgTypes
import Madl.Network
import Madl.MetaIslands
import Utils.Text
import Data.Maybe
import Control.Monad (replicateM)
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.HashMap as H
import qualified Data.IntMap as IM
import qualified Data.Bimap as BM
import qualified Data.ByteString.Char8 as B



conv :: String -> B.ByteString
conv s = B.pack s

getAllMergeIDs :: ColoredNetwork -> [ComponentID]
getAllMergeIDs net = let comps = getComponentIDs net
                         res = filter (\x -> case getComponent net x of (Merge _) -> True; _ -> False) comps
                     in res

getAllMultiMatchIDs :: ColoredNetwork -> [ComponentID]
getAllMultiMatchIDs net = let comps = getComponentIDs net
                              res = filter (\x -> case getComponent net x of (MultiMatch _ _) -> True; _ -> False) comps
                          in res

getAllLoadBalancerIDs :: ColoredNetwork -> [ComponentID]
getAllLoadBalancerIDs net = let comps = getComponentIDs net
                                res = filter (\x -> case getComponent net x of (LoadBalancer _) -> True; _ -> False) comps
                            in res                             


toBin :: Int -> [Int]
toBin 0 = []
toBin n = (toBin (n`div`2)) ++ [n `mod` 2]

fac :: Int -> Int
fac 0 = 1
fac n = n * fac (n - 1)

noslashes :: String -> String
noslashes str = filter (\x -> x /= '\"') str

enumMap :: ColoredNetwork -> H.Map String Int
enumMap net = enumMap' (map (\x -> show x) (networkTypes net)) H.empty 
  where enumMap' :: [String] -> H.Map String Int -> H.Map String Int
        enumMap' [] h = h
        enumMap' (y:ys) h = enumMap' ys (H.insert (noslashes y) (H.size h) h)

typeMap :: ColoredNetwork -> BM.Bimap (S.Set Color) String
typeMap net = let chans = getChannelIDs net
                  cols = L.nub $ map (\x -> let ColorSet c = getColorSet net x in c) chans
              in typeMap' cols 0 BM.empty
  where typeMap' :: [S.Set Color] -> Int -> BM.Bimap (S.Set Color) String -> BM.Bimap (S.Set Color) String
        typeMap' [] _ m = m
        typeMap' (x:xs) i m = typeMap' xs (i+1) (BM.insert x ("t" ++ (show i)) m)

inferEnum :: S.Set Color -> [String]
inferEnum cs = inferEnum' $ S.toList cs
  where inferEnum' :: [Color] -> [String]
        inferEnum' [] = []
        inferEnum' (x:xs) = let Color n ov = x in if (utxt n /= "" && case ov of
                                                                        Right _ -> False
                                                                        Left (VStruct hm) -> H.null hm)
                                                  then (utxt n:inferEnum' xs)
                                                  else error "wrong color type1"

                       
inferBV :: S.Set Color -> (String,Int)
inferBV cs = inferBV' (S.toList cs) ("",0)
  where inferBV' :: [Color] -> (String,Int) -> (String,Int)
        inferBV' [] res = res
        inferBV' (x:xs) res = let Color n ov = x in if (utxt n == "" && case ov of
                                                                          Right _ -> False
                                                                          Left (VStruct hm) -> let hm' = H.toList hm
                                                                                               in case head hm' of
                                                                                                    (_,Right (Value _)) -> True
                                                                                                    _ -> False)
                                                    then let Left (VStruct hm) = ov
                                                             (m,Right (Value i)) = head $ H.toList hm
                                                         in if (i > snd res)
                                                            then inferBV' xs (utxt m,i)
                                                            else inferBV' xs res
                                                    else error "wrong color type2"

inferStruct :: S.Set Color -> [(String, Either [String] Int)]
inferStruct cs = H.toList $ inferStruct' (S.toList cs) H.empty
  where inferStruct' :: [Color] -> H.Map String (Either [String] Int) -> H.Map String (Either [String] Int)
        inferStruct' [] res = res
        inferStruct' (x:xs) res = let Color n ov = x in if (utxt n == "" && case ov of
                                                                              Right _ -> False
                                                                              Left (VStruct hm) -> not $ H.null hm)
                                                        then let Left (VStruct hm) = ov
                                                             in inferStruct' xs $ updStruct hm res
                                                        else error "wrong color type3"

inferUnion :: S.Set Color -> [(String, [(String, (Either [String] Int))])]
inferUnion cs = map (\(x,y) -> (x,H.toList y)) $ H.toList $ inferUnion' (S.toList cs) H.empty
  where inferUnion' :: [Color] -> H.Map String (H.Map String (Either [String] Int)) -> H.Map String (H.Map String (Either [String] Int))
        inferUnion' [] res = res
        inferUnion' (x:xs) res = let Color n ov = x in if (utxt n /= "" && case ov of
                                                                             Right _ -> False
                                                                             Left (VStruct hm) -> not $ H.null hm)
                                                       then if (H.member (utxt n) res)
                                                            then let Left (VStruct hm) = ov
                                                                     h' = res H.! (utxt n)
                                                                     h'' = updStruct hm h'
                                                                 in inferUnion' xs $ H.insert (utxt n) (h'') res 
                                                            else let Left (VStruct hm) = ov
                                                                     h' = updStruct hm H.empty
                                                                 in inferUnion' xs $ H.insert (utxt n) h' res 
                                                       else error "wrong color type4"

updStruct :: H.Map Text (OrValue Color) -> H.Map String (Either [String] Int) -> H.Map String (Either [String] Int)
updStruct m1 m2 = updStruct' (H.toList m1) m2
  where updStruct' :: [(Text,(OrValue Color))] -> H.Map String (Either [String] Int) -> H.Map String (Either [String] Int)
        updStruct' [] res = res
        updStruct' (x:xs) res = case x of
                                  (n,Right (Value i)) -> if (H.member (utxt n) res)
                                                         then let j = res H.! (utxt n)
                                                              in case j of
                                                                   Left _ -> error "wrong color type5"
                                                                   Right j' -> if i > j'
                                                                               then updStruct' xs $ H.insert (utxt n) (Right i) res
                                                                               else updStruct' xs res
                                                         else updStruct' xs $ H.insert (utxt n) (Right i) res
                                  (n,Left (Color m _)) -> if (H.member (utxt n) res)
                                                          then let j = res H.! (utxt n)
                                                               in case j of
                                                                    Right _ -> error "wrong color type6"
                                                                    Left j' -> updStruct' xs $
                                                                               H.insert (utxt n) (Left (L.nub ((utxt m):j'))) res
                                                          else updStruct' xs $ H.insert (utxt n) (Left [utxt m]) res

defaultEnum :: S.Set Color -> String
defaultEnum cs = let Color n ov = head $ S.toList cs
                 in if (utxt n /= "" && case ov of
                                          Right _ -> False
                                          Left (VStruct hm) -> H.null hm)
                    then (utxt n)
                    else error "wrong color type7"

defaultBV :: S.Set Color -> String
defaultBV cs = let Color n ov = head $ S.toList cs
               in if (utxt n == "" && case ov of
                                        Right _ -> False
                                        Left (VStruct hm) -> let hm' = H.toList hm
                                                             in case head hm' of
                                                                  (_,Right (Value _)) -> True
                                                                  _ -> False)
                  then let (Left (VStruct hm)) = ov
                       in let hm' = H.toList hm
                          in let (_,Right (Value i)) = head hm'
                             in show i
                  else error "wrong color type8"


defaultStruct :: S.Set Color -> String
defaultStruct cs = let Color n ov = head $ S.toList cs
                   in if (utxt n == "" && case ov of
                                            Right _ -> False
                                            Left (VStruct hm) -> not $ H.null hm)
                      then let Left (VStruct hm) = ov
                           in "'{" ++ foldr (\x y -> case y of "" -> x; _ -> x ++ "," ++ y) ""
                              (map (\x -> case x of
                                            (_,Right (Value i)) -> {-(utxt a) ++ ":" ++-} show i
                                            (_,Left (Color m _)) -> {-(utxt a) ++ ":" ++-} (utxt m)) $ H.toList hm) ++ "}"
                      else error "wrong color type9"

defaultUnion :: S.Set Color -> String
defaultUnion cs = let Color n ov = head $ S.toList cs
                  in if (utxt n /= "" && case ov of
                                           Right _ -> False
                                           Left (VStruct hm) -> not $ H.null hm)
                     then let Left (VStruct hm) = ov
                          in "'{" ++ foldr (\x y -> case y of "" -> x; _ -> x ++ "," ++ y) ""
                              (map (\x -> case x of
                                            (_,Right (Value i)) -> {-(utxt a) ++ ":" ++-} show i
                                            (_,Left (Color m _)) -> {-(utxt a) ++ ":" ++-} (utxt m)) $ H.toList hm) ++ "}"
                     else error "wrong color type10"



defaultVal :: S.Set Color -> String
defaultVal o = let o' = head $ S.toList o
                   Color n ov = o'
               in if (utxt n /= "" && case ov of
                                              Right _ -> False
                                              Left (VStruct hm) -> H.null hm)
                  then defaultEnum o
                  else if (utxt n == "" && case ov of
                                                   Right _ -> False
                                                   Left (VStruct hm) -> let hm' = H.toList hm
                                                                        in case head hm' of
                                                                             (_,Right (Value _)) -> True
                                                                             _ -> False)
                       then defaultStruct o
                       else if (utxt n == "" && case ov of
                                                        Right _ -> False
                                                        Left (VStruct hm) -> not $ H.null hm)
                            then defaultBV o
                            else defaultUnion o


showColor :: Color -> String
showColor c = defaultVal $ S.singleton c

showColorTest :: ColoredNetwork -> String
showColorTest net = let src = head $ getSources $ metaIsles net
                        (MetaComp _ _ _ (IOColor c) _) = src
                    in (showMadlType net c) ++ "\n\n" ++ (show (head $ S.toList c)) ++ "\n\n" ++ (showColor ((S.toList c) !! 1))
                        

showEnum :: ColoredNetwork -> String -> [String]  -> String
showEnum net n o = let em = enumMap net
                       o' = map (\x -> x ++ "=" ++ show (em H.! x)) o
                   in "typedef enum {" ++ (foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" o')  ++ "} " ++ n ++ ";"

showBV :: String -> (String,Int) -> String
showBV n _ = "typedef int " ++ n ++ ";"
{-n (_,i) = let m = L.length $ toBin i
                 in "typedef bit[" ++ show m ++ ":0] " ++ n ++ ";"-}

showStruct :: String -> [(String, Either [String] Int)] -> String
showStruct n o = "typedef struct {\n\t" ++ (foldr (\x y -> case y of "" -> x ++ "\n" ++ y; _ -> x ++ "\n\t" ++ y) "" $ map (\x -> showStruct' x) o) ++ "} " ++ n ++ ";"
  where showStruct' :: (String, Either [String] Int) -> String
        showStruct' (z, Left zs) = "enum {" ++ foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) "" zs ++ "} " ++ z ++ ";"
        --showStruct' (z, Right i) = "bit[" ++ show (L.length (toBin i)) ++ ":0] " ++ z ++ ";"
        showStruct' (z, Right _) = "int " ++ z ++ ";"

showUnion :: String -> [(String, [(String, (Either [String] Int))])] -> String
showUnion n o = let o' = map (\(x,y) -> showStruct x y) o
                    r = foldr (\x y -> case y of "" -> x ++ ";\n" ++ y; _ -> x ++ ";\n\t" ++ y) "" $ map (\(x,y) -> x ++ " " ++ n ++ (show (fromJust $ L.elemIndex (x,y) o))) o
                in foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "\n" ++ y) "" o' ++
                   "\ntypedef union{\n\t" ++ r ++ "} " ++ n ++ ";" 

showMadlType :: ColoredNetwork -> S.Set Color -> String
showMadlType net o = if (S.null o)
                     then "typedef enum {any=0} " ++ ((typeMap net) BM.! o) ++ ";"
                     else let o' = head $ S.toList o
                              Color n ov = o'
                              tm = typeMap net
                          in if (utxt n /= "" && case ov of
                                                   Right _ -> False
                                                   Left (VStruct hm) -> H.null hm)
                             then showEnum net (tm BM.! o) $ inferEnum o
                             else if (utxt n == "" && case ov of
                                                        Right _ -> False
                                                        Left (VStruct hm) -> let hm' = H.toList hm
                                                                             in case head hm' of
                                                                                  (_,Right (Value _)) -> True
                                                                                  _ -> False)
                                  then showStruct (tm BM.! o) $ inferStruct o
                                  else if (utxt n == "" && case ov of
                                                             Right _ -> False
                                                             Left (VStruct hm) -> not $ H.null hm)
                                       then showBV (tm BM.! o) $ inferBV o
                                       else showUnion (tm BM.! o) $ inferUnion o

metaIsles :: ColoredNetwork -> MetaIslands
metaIsles net = makeMetaIslands net

qDeclGen :: Int  -> Int -> String -> String
qDeclGen i cap t = "typedef struct {\n\t" ++ t ++ " Contents[" ++ show cap ++ "];\n\tint Size;\n} queue" ++ show i ++ "_t;" 

qFirstGen :: Int -> String -> String
qFirstGen i t = "function " ++ t ++ " queue" ++ show i ++ "_first;\n\tinput queue" ++ show i ++ "_t x;\n\treturn x.Contents[0];\nendfunction"

qLastGen :: Int -> String -> String
qLastGen i t = "function " ++ t ++ " queue" ++ show i ++ "_last;\n\tinput queue" ++ show i ++ "_t x;\n\treturn x.Contents[(x.Size-1)];\nendfunction"

qEnqueueGen :: Int -> String -> String
qEnqueueGen i t = "function queue" ++ show i ++ "_t queue" ++ show i ++ "_enqueue;\n\tinput queue" ++ show i ++ "_t x;\n\tinput " ++ t ++ " y;\n\tqueue" ++ show i ++ "_t tmpq;\n\tif ($size(x.Contents) < x.Size) begin\n\t\tfor (int i=(x.Size-1); i>=0; i--) begin\n\t\t\ttmpq.Contents[i+1]=x.Contents[i];\n\t\tend\n\t\ttmpq.Contents[0] = y;\n\ttmpq.Size = x.Size + 1;\n\treturn tmpq;\n\tend\n\telse\n\t\treturn x;\nendfunction"  

qDequeueGen :: Int  -> String
qDequeueGen i = "function queue" ++ show i ++ "_t queue" ++ show i ++ "_dequeue;\n\tinput queue" ++ show i ++ "_t x;\n\tqueue" ++ show i ++ "_t tmpq;\n\tif (x.Size > 0)\n\t\ttmpq.Size = tmpq.Size - 1;\n\treturn tmpq;\nendfunction"

qExistsGen :: Int -> String -> String
qExistsGen i t = "function bit queue" ++ show i ++ "_exists;" ++ "\n\tinput queue" ++ show i ++ "_t x;\n\tinput " ++ t ++ " y;\n\tbit res;\n\tres = 0;\n\tfor (int i=0;i<x.Size;i++) begin\n\t\tif(x.Contents[i]==y)\n\t\t\tres = 1;\n\tend\n\treturn res;\nendfunction"


sizeGen :: Int -> B.ByteString
sizeGen q = (B.pack "`define SIZE ") `B.append` (B.pack (show q))

qOfIntSize :: ColoredNetwork -> Int
qOfIntSize net = let lconfs = illegalToLegal2 net
                     res = foldr (\(x,x') (y,y') -> if (L.length x' > L.length y') then (x,x') else (y,y')) ([],[[]]) lconfs
                 in L.length (snd res)
                    
typedefGen :: Int -> ColoredNetwork -> B.ByteString
typedefGen q net = let chans = getChannelIDs net
                       srcs = L.sort . uniqueIDMetaComps . getSources $ metaIsles net
                       --snks = L.sort . uniqueIDMetaComps . getSinks $ metaIsles net
                       --chans = L.nub $ L.concat (map (\x -> getOutChannels net (metaCompToID x)) srcs) ++
                       --        L.concat (map (\x -> getInChannels net (metaCompToID x)) snks)
                       qs = L.sort . uniqueIDMetaComps . getQueues $ metaIsles net
                       tm = typeMap net
                       (MetaIslands _ _ _ _ misls) = metaIsles net
                       nisls = L.length misls 
                       gt = \(c::MetaComp) -> compType c
                       res = L.nub $ map (\x -> let ColorSet c = getColorSet net x in c) chans
                       qdecl = ["typedef struct {\n\tbit[0:" ++ show (nisls - 1) ++ "] Contents[" ++ show (qOfIntSize net) ++ "];\n\t" ++ sizeToType q ++ " Size;\n} queue_of_int;"]
                       res' = ["typedef struct {"] ++
                              map (\x -> "\tbit Src" ++ show (fromJust $ L.elemIndex x srcs) ++ "_free;\n\t" ++ tm BM.! (gt x) ++ " Src" ++ show (fromJust $ L.elemIndex x srcs) ++ "_state;") srcs ++
                              map (\x -> let w = (L.length . toBin $ (L.length (getAllQueueStates x) - 1) - 1)
                                             r = case w of
                                                  0 -> "\tbit Q"
                                                  _ -> "\tbit[" ++ show w ++ ":0] Q"
                                         in r ++ show (fromJust $ L.elemIndex x qs) ++ "_state;") qs ++
                              ["} state;"] ++
                              ["typedef struct {\n\tstate Contents[`SIZE];\n\t" ++ sizeToType q ++ " Size;\n} determ_state;"]
                   in B.pack $ foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "\n" ++ y) "" $ (map (\x -> showMadlType net x) res) ++ qdecl ++ res'


--takes a MetaComp queue and computes the number of distinct states
nrOfQueueStates :: MetaComp -> Int
nrOfQueueStates (MetaComp _ _ Q (IOColor c) (Capacity i)) = L.length $ toBin $ nrOfQueueStates' (S.size c) i
  where
    nrOfQueueStates' :: Int -> Int -> Int
    nrOfQueueStates' n k
      | k > 0 = n^k + nrOfQueueStates' n (k-1)
      | otherwise = 0
nrOfQueueStates (MetaComp _ _ _ _ _) = 0

--takes a SIZE constant and returns the corresponding integer type as a string
sizeToType :: Int -> String
sizeToType n
  | n < 2 = "bit"
  | n < 128 = "byte"
  | n < 32768 = "showrtint"
  | n < 2147483648 = "int"
  | otherwise = "longint"

{-
qFunGen :: ColoredNetwork -> String
qFunGen net = let qs = L.sort . getQueues $ metaIsles net
                  tm = typeMap net
                  gt = \(c::MetaComp) -> compType c
                  gi = \(c::MetaComp) -> (fromJust $ L.elemIndex c qs)
                  res = map (\x -> qFirstGen (gi x) (tm BM.! (gt x)) ++ "\n\n" ++
                                   qLastGen (gi x) (tm BM.! (gt x)) ++ "\n\n" ++
                                   qEnqueueGen (gi x) (tm BM.! (gt x)) ++ "\n\n" ++
                                   qDequeueGen (gi x) ++ "\n\n" ++
                                   qExistsGen (gi x) (tm BM.! (gt x))
                            ) qs ++
                        ["function int queue_of_int_first;\n\tinput queue_of_int x;\n\treturn x.Contents[0];\nendfunction\n\nfunction int queue_of_int_last;\n\tinput queue_of_int x;\n\treturn x.Contents[(x.Size-1)];\nendfunction\n\nfunction queue_of_int queue_of_int_enqueue;\n\tinput queue_of_int x;\n\tinput int y;\n\tqueue_of_int tmpq;\n\tif ($size(x.Contents) < x.Size) begin\n\t\tfor (int i=(x.Size-1); i>=0; i--) begin\n\t\t\ttmpq.Contents[i+1]=x.Contents[i];\n\t\tend\n\t\ttmpq.Contents[0] = y;\n\t\ttmpq.Size = x.Size + 1;\n\t\treturn tmpq;\n\tend\n\telse\n\t\treturn x;\nendfunction\n\nfunction queue_of_int queue_of_int_dequeue;\n\tinput queue_of_int x;\n\tqueue_of_int tmpq;\n\tif (x.Size > 0)\n\t\ttmpq.Size = tmpq.Size - 1;\n\treturn tmpq;\nendfunction\n\nfunction bit queue_of_int_exists;\n\tinput queue_of_int x;\n\tinput int y;\n\tbit res;\n\tres = 0;\n\tfor (int i=0;i<x.Size;i++) begin\n\t\tif(x.Contents[i]==y)\n\t\t\tres = 1;\n\tend\n\treturn res;\nendfunction","function queue_of_int queue_of_queue_of_int_first;\n\tinput queue_of_queue_of_int x;\n\treturn x.Contents[0];\nendfunction\n\nfunction queue_of_int queue_of_queue_of_int_last;\n\tinput queue_of_queue_of_int x;\n\treturn x.Contents[(x.Size-1)];\nendfunction\n\nfunction queue_of_queue_of_int queue_of_queue_of_int_enqueue;\n\tinput queue_of_queue_of_int x;\n\tinput queue_of_int y;\n\tqueue_of_queue_of_int tmpq;\n\tif ($size(x.Contents) < x.Size) begin\n\t\tfor (int i=(x.Size-1); i>=0; i--) begin\n\t\t\ttmpq.Contents[i+1]=x.Contents[i];\n\t\tend\n\t\ttmpq.Contents[0] = y;\n\t\ttmpq.Size = x.Size + 1;\n\t\treturn tmpq;\n\tend\n\telse\n\t\treturn x;\nendfunction\n\nfunction queue_of_queue_of_int queue_of_queue_of_int_dequeue;\n\tinput queue_of_queue_of_int x;\n\tqueue_of_queue_of_int tmpq;\n\tif (x.Size > 0)\n\t\ttmpq.Size = tmpq.Size - 1;\n\treturn tmpq;\nendfunction\n\nfunction bit queue_of_queue_of_int_exists;\n\tinput queue_of_queue_of_int x;\n\tinput queue_of_int y;\n\tbit res;\n\tres = 0;\n\tfor (int i=0;i<x.Size;i++) begin\n\t\tif(x.Contents[i]==y)\n\t\t\tres = 1;\n\tend\n\treturn res;\nendfunction","function state determ_state_first;\n\tinput determ_state x;\n\treturn x.Contents[0];\nendfunction\n\nfunction state determ_state_last;\n\tinput determ_state x;\n\treturn x.Contents[(x.Size-1)];\nendfunction\n\nfunction determ_state determ_state_enqueue;\n\tinput determ_state x;\n\tinput state y;\n\tdeterm_state tmpq;\n\tif ($size(x.Contents) < x.Size) begin\n\t\tfor (int i=(x.Size-1); i>=0; i--) begin\n\t\t\ttmpq.Contents[i+1]=x.Contents[i];\n\t\tend\n\t\ttmpq.Contents[0] = y;\n\t\ttmpq.Size = x.Size + 1;\n\t\treturn tmpq;\n\tend\n\telse\n\t\treturn x;\nendfunction\n\nfunction determ_state determ_state_dequeue;\n\tinput determ_state x;\n\tdeterm_state tmpq;\n\tif (x.Size > 0)\n\t\ttmpq.Size = tmpq.Size - 1;\n\treturn tmpq;\nendfunction\n\nfunction bit determ_state_exists;\n\tinput determ_state x;\n\tinput state y;\n\tbit res;\n\tres = 0;\n\tfor (int i=0;i<x.Size;i++) begin\n\t\tif(x.Contents[i]==y)\n\t\t\tres = 1;\n\tend\n\treturn res;\nendfunction"]
              in foldr (\x y -> case y of "" -> x; _ -> x ++ "\n\n" ++ y) "" res
-}

qFunGen :: Int -> ColoredNetwork -> String
qFunGen q net = let (MetaIslands _ _ _ _ misls) = metaIsles net
                    nisls = L.length misls
                in "function queue_of_int queue_of_int_enqueue;\n\tinput queue_of_int x;\n\tinput bit [0:" ++ show (nisls - 1) ++ "] y;\n\tqueue_of_int tmpq;\n\n\tfor(byte i=0;i<$size(tmpq.Contents);i++) begin\n\t\ttmpq.Contents[i] = " ++ show nisls ++ "'b" ++ foldr (\x y -> x ++ y) "" (replicate nisls "0") ++ ";\n\tend\n\ttmpq.Size=0;\n\n\tif ($size(x.Contents) > x.Size) begin\n\t\tfor (byte i=0; i<($size(x.Contents)-1); i++) begin\n\t\t\ttmpq.Contents[i+1]=x.Contents[i];\n\t\tend\n\t\ttmpq.Contents[0] = y;\n\t\ttmpq.Size = x.Size + 1;\n\t\treturn tmpq;\n\tend\n\telse\n\t\treturn x;\nendfunction\n\n" ++
                   "function determ_state determ_state_enqueue;\n\tinput determ_state x;\n\tinput state y;\n\tdeterm_state tmpq;\n\n\tfor (byte i=0;i<$size(tmpq.Contents);i++) begin\n\t\ttmpq.Contents[i] = " ++ defaultStateGen net ++ ";\n\tend\n\ttmpq.Size = 0;\n\n\tif ($size(x.Contents) > x.Size) begin\n\t\tfor (" ++ sizeToType q ++ " i=0; i<($size(x.Contents)-1); i++) begin\n\t\t\ttmpq.Contents[i+1]=x.Contents[i];\n\t\tend\n\t\ttmpq.Contents[0] = y;\n\t\ttmpq.Size = x.Size + 1;\n\t\treturn tmpq;\n\tend\n\telse\n\t\treturn x;\nendfunction\n\n" ++ "function bit determ_state_exists;\n\tinput determ_state x;\n\tinput state y;\n\tbit res;\n\tres = 0;\n\tfor (" ++ sizeToType q ++ " i=0;i<$size(x.Contents);i++) begin\n\t\tif(x.Contents[i]==y & i < x.Size)\n\t\t\tres = 1;\n\tend\n\treturn res;\nendfunction"


interfaceGen :: ColoredNetwork -> String
interfaceGen net = let srcs = L.sort . uniqueIDMetaComps . getSources $ metaIsles net
                       snks = L.sort . uniqueIDMetaComps . getSinks $ metaIsles net
                       tm = typeMap net
                       gt = \(c::MetaComp) -> compType c
                       insrc = \(c::MetaComp) (i::Int) -> ["input wire Src" ++ show i ++ "_o_irdy,","input " ++ tm BM.! (gt c) ++ " Src" ++ show i ++ "_o_data,"]
                       insnk = \(c::MetaComp) (i::Int) -> ["input wire Snk" ++ show i ++ "_i_trdy,","input " ++ tm BM.! (gt c) ++ " Snk" ++ show i ++ "_i_data,"]
                       res = ["input Clock,","input Reset,"] ++
                             (L.concat $ map (\x -> insrc x (fromJust $ L.elemIndex x srcs)) srcs) ++
                             (L.concat $ map (\x -> insnk x (fromJust $ L.elemIndex x snks)) snks) ++
                             ["output reg Error,","output reg Overflow"]
                   in foldr (\x y -> case y of "" -> "\t" ++ x ++ y; _ -> "\t" ++ x ++ "\n" ++ y) "" res
                      
--compType, defaultVal
localParamGen :: ColoredNetwork -> String
localParamGen net = let --srcs = L.sort . uniqueIDMetaComps . getSources $ metaIsles net
                        --qs = L.sort . uniqueIDMetaComps . getQueues $ metaIsles net
                        res = "\nlocalparam\n" ++ "\tdeterm_state InitialState = '{'{`SIZE{" ++ defaultStateGen net ++
                              "}},1'b1};"
                    in res

defaultStateGen :: ColoredNetwork -> String
defaultStateGen net = let srcs = L.sort . uniqueIDMetaComps . getSources $ metaIsles net
                          qs = L.sort . uniqueIDMetaComps . getQueues $ metaIsles net
                          res = "'{" ++ foldr (\x y -> case y of "" -> x ++ y; _ -> x ++ "," ++ y) ""
                                (map (\x -> "1'b1," ++ (defaultVal $ compType x)) srcs ++
                                 map (\x -> show (nrOfQueueStates x) ++ "'b" ++ foldr (\p q -> p ++ q) "" (replicate (nrOfQueueStates x) "0")) qs) ++ "}"
                      in res

hasElemGen :: ColoredNetwork -> String
hasElemGen net = let (MetaIslands _ _ _ _ misls) = metaIsles net
                     nisls = L.length misls
                 in "function bit hasElem;\n\tinput " ++ sizeToType nisls ++ " e;\n\tinput bit [0:" ++ show (nisls - 1) ++ "] c;\n\n\treturn c[e];\nendfunction"


  
varGen :: ColoredNetwork -> String
varGen net = let (MetaIslands _ _ _ _ misls) = metaIsles $ net
             in "determ_state CurrentState;\ndeterm_state NextState;\nstate tmpState;\nqueue_of_int Confs;\nbit[0:" ++ show (L.length misls -1) ++ "] TIsls;\n\nbit check;\nbit err;\nbit ovf;"

beginGen :: String
beginGen = "initial begin\n\tCurrentState = InitialState;\n\tError = 0;\nend"

alwaysGen :: String
alwaysGen = "always@(posedge Clock) begin\n\tif (Reset) CurrentState <= InitialState;\n\telse CurrentState <= NextState;\nend"

{-
getLegalConfsGen :: ColoredNetwork -> String
getLegalConfsGen net = let legalConfs = getLegalConfsGen' net
                           (MetaIslands _ _ _ _ misls) = metaIsles net
                           legalConfs' = map (\(xs,xss) -> (map (\z -> show z) xs,map (\hs -> map (\h -> show h) hs) xss)) legalConfs 
                           printConf = \(xs::[String]) -> "'{Contents:{" ++ foldr (\x y -> case y of "" -> x; _ -> x ++ "," ++ y) "" (xs ++ (replicate ((L.length misls) - (L.length xs)) "0")) ++ "},Size:" ++ show (L.length xs) ++ "}"
                           cases = map (\(x,xs) -> "\n\t\t" ++ printConf x ++ " : begin" ++
                                       foldr (\a b -> case b of "" -> a ++ ";"; _ -> a ++ ";" ++ b) "" (map (\z -> "\n\t\t\tloc_confs = queue_of_queue_of_int_enqueue(loc_confs," ++ printConf z ++ ")") xs) ++ "\n\t\t\tend") legalConfs'
                           cases' = foldr (\x y -> x ++ y) "" cases
                           res = "function queue_of_queue_of_int getLegalConfs;\n\tinput queue_of_int confs;\n\tqueue_of_queue_of_int loc_confs;\n\n\tcase(confs)" ++ cases' ++ "\n\t\tdefault: loc_confs = queue_of_queue_of_int_nequeue(loc_confs,confs);\n\tendcase\n\treturn loc_confs;\nendfunction"
                       in res
-}
{-
function queue_of_int getLegalConfs;
   input bit [(`NUM_ISLS - 1):0] confs;//must be a bit vector
   queue_of_int loc_confs;//must be a queue_of_int

   for (byte i=0;i<$size(loc_confs.Contents);i++) begin//change
      loc_confs.Contents[i] = 3'b000;
   end
   loc_confs.Size = 0;
   
   //change all things below, but it should be similar, in general
   if (confs == 3'b011) begin
      loc_confs = queue_of_int_enqueue(loc_confs,3'b010);
      loc_confs = queue_of_int_enqueue(loc_confs,3'b001);
   end
   else if (confs == 3'b111) begin
      loc_confs = queue_of_int_enqueue(loc_confs,3'b110);
      loc_confs = queue_of_int_enqueue(loc_confs,3'b101);
   end
   else if (confs != 3'b000)
     loc_confs = queue_of_int_enqueue(loc_confs,confs);
   return loc_confs;
endfunction
-}

getLegalConfsGen :: Int -> ColoredNetwork -> B.ByteString
getLegalConfsGen q net = let confs = illegalToLegal2 net
                             conds = foldr (\a b -> if (b /= B.empty) then (a `B.append` (B.pack " & ") `B.append` b) else (a `B.append` b)) B.empty  $ map (\(x,_) -> (B.pack "confs != ") `B.append` (B.pack $ show (L.length misls)) `B.append` (B.pack "'b") `B.append` B.concat (map (\y -> B.pack (show y)) x)) confs
                             conds' = if (conds /= B.empty)
                                      then ((B.pack " & ") `B.append` conds)
                                      else conds
                             (MetaIslands _ _ _ _ misls) = metaIsles net
                             res = foldl (\a b -> if (a == B.empty) then (a `B.append` (B.pack "\n\t") `B.append` b) else (a `B.append` (B.pack "\n\t") `B.append` b)) B.empty ((map (\(x,xs) -> (B.pack "if (confs == ") `B.append` (B.pack $ show (L.length misls)) `B.append` (B.pack "'b") `B.append` B.concat (map (\y -> B.pack (show y)) x) `B.append` (B.pack ") begin") `B.append` B.concat (map (\z -> (B.pack "\n\t\tloc_confs = queue_of_int_enqueue(loc_confs,") `B.append` (B.pack $ show (L.length misls)) `B.append` (B.pack "'b") `B.append` B.concat (map (\y -> (B.pack $ show y)) z) `B.append` (B.pack ");")) xs) `B.append` (B.pack "\n\tend")) confs) ++ [(B.pack "if (confs != ") `B.append` (B.pack (show $ L.length misls)) `B.append` (B.pack "'b") `B.append` B.concat (take (L.length misls) (repeat (B.pack "0"))) `B.append` conds' `B.append` (B.pack ")\n\t\tloc_confs = queue_of_int_enqueue(loc_confs,confs);")])
                         in (B.pack "function queue_of_int getLegalConfs;\n\tinput bit[0:") `B.append` (B.pack (show $ L.length misls - 1)) `B.append` (B.pack "] confs;\n\tqueue_of_int loc_confs;\n\n\tfor (") `B.append` (B.pack $ sizeToType q) `B.append` (B.pack " i=0;i<$size(loc_confs.Contents);i++) begin\n\t\tloc_confs.Contents[i] = ") `B.append` (B.pack (show $ L.length misls)) `B.append` (B.pack "'b") `B.append` B.concat (take (L.length misls) (repeat $ B.pack "0")) `B.append` (B.pack ";\n\tend\n\tloc_confs.Size = 0;\n\n") `B.append` res `B.append` (B.pack "\n\treturn loc_confs;\nendfunction")

updConf :: [Int] -> Int -> [Int]
updConf [] _ = []
updConf (x:xs) ind
  | x == 0 = (-1:updConf xs (ind + 1))
  | otherwise = (ind:updConf xs (ind + 1))

getLegalConfsGen' :: ColoredNetwork -> [([Int],[[Int]])]
getLegalConfsGen' net = let misles = metaIsles net
                            (MetaIslands _ nrm legalConfs _ mi) = misles
                            (confs::[[Int]]) = replicateM (L.length mi) [0,1]
                            res = map (\x -> (x,filter (\y -> if (L.elem x legalConfs)
                                                              then y == x
                                                              else (countDifference x y == nrm)
                                                       ) legalConfs)) confs
                            res' = filter (\(_,xs) -> L.length xs > 1) res
                        in map (\(xs,xss) -> (filter (\x -> if (x == -1) then False else True) (updConf xs 0),map (\hs -> filter (\x -> if (x == -1) then False else True) (updConf hs 0)) xss)) res'

countDifference :: [Int] -> [Int] -> Int
countDifference as bs
  | L.length as /= L.length bs = error "Illegal comparison"
  | otherwise = countDifference' as bs 0
  where countDifference' :: [Int] -> [Int] -> Int -> Int
        countDifference' [] [] i = i
        countDifference' (x:xs) (y:ys) i
          | x /= y = countDifference' xs ys (i+1)
          | otherwise = countDifference' xs ys i
        countDifference' _ _ _ = error "Illegal comparison"

{-
updGen :: ColoredNetwork -> String
updGen net = let misls = metaIsles net
                 (MetaIslands _ _ _ _ misls') = misls
                 srcs = L.nub $ getSources misls
                 srcs' = foldr (\x y -> x ++ y) "" $
                         map (\x -> let i = (show $ srcInd net x) in "\n\tloc_s.Src" ++ i ++ "_state = s.Src" ++ i ++ "_state;") srcs
                 cs = foldr (\x y -> x ++ y) "" $ map (\x -> caseGen net x) misls'
                 res = "function state upd;\n\tinput int i;\n\tinput state s;\n\tstate loc_s;\n" ++ srcs' ++
                       "\n\n\tcase(i)" ++
                       cs ++
                       "\n\tendcase\n\treturn loc_s;\nendfunction"
             in res
-}

caseGen :: ColoredNetwork -> MetaIsle -> String
caseGen net (MetaIsle i _ inps outs) = let outs' = foldr (\x y -> x ++ y) "" $
                                                   map (\x -> let j = (show $ qInd net x) in "\n\t\t\t" ++ "loc_s.Q" ++ j ++ "_state = queue"++ j ++ "_enqueue(s.Q" ++ j ++ "_state," ++ caseGen' net x ++ ");") $ filter (\(MetaComp _ _ t _ _) -> case t of Q -> True; _ -> False) outs
                                           inps' = foldr (\x y -> x ++ y) "" $
                                                   map (\x -> let j = (show $ qInd net x) in "\n\t\t\tloc_s.Q" ++ j ++ "_state = queue" ++ j ++ "_dequeue(s.Q" ++ j ++ "_state);") $ filter (\(MetaComp _ _ t _ _) -> case t of Q -> True; _ -> False) inps
                                           res = "\n\t\t" ++ show i ++ ":begin" ++ inps' ++ outs' ++ "\n\t\tend"
                                       in res

caseGen' :: ColoredNetwork -> MetaComp -> String
caseGen' net (MetaComp _ (Arg i) _ _ _) = case getComponent net i of
                                            (Queue _ _) -> let qs = getQueues $ metaIsles net
                                                               q = getComp qs i
                                                           in "s.Q" ++ show (qInd net q) ++ "_state"
                                            (Source _ _) -> let srcs = getSources $ metaIsles net
                                                                src = getComp srcs i
                                                            in  "Src" ++ show (srcInd net src) ++ "_o_data"
                                            _ -> error "wrong component"
caseGen' net (MetaComp _ (Fun i [Arg j]) _ _ _) = case getComponent net j of
                                                    (Queue _ _) -> let qs = getQueues $ metaIsles net
                                                                       q = getComp qs j
                                                                   in "deq" ++ show i ++ "(s.Q" ++ show (qInd net q) ++ "_state)"
                                                    (Source _ _) -> let srcs = getSources $ metaIsles net
                                                                        src = getComp srcs j
                                                                    in  "deq" ++ show i ++ "(Src" ++ show (srcInd net src) ++ "_o_data)"
                                                    _ -> error "wrong component"
caseGen' _ (MetaComp _ x _ _ _) = error $ show x


checkIslsGen :: ColoredNetwork -> String
checkIslsGen net = let (MetaIslands _ _ _ _ misls) = metaIsles net
                       conds = foldr (\x y -> x ++ y) "" $ map (\x -> checkGen net x) misls
                       res = "function bit[0:" ++ show (L.length misls - 1) ++ "] checkIsls;\n\tinput state s;\n\tbit[0:" ++ show (L.length misls - 1) ++ "] loc_isls;\n\n\tloc_isls = " ++ show (L.length misls) ++ "'b" ++ concat (take (L.length misls) (repeat "0")) ++ ";\n" ++
                             conds ++
                             "\n\treturn loc_isls;\nendfunction"
                   in res

--		if (s.Q0_state.Size > 0 & Snk0_i_trdy)
--			if (Snk0_i_data == s.Q0_state.Contents[Q0_state.Size-1]) //
--				loc_isls = queue_of_int_enqueue(loc_isls,0); //
--		if (Src0_o_irdy & s.Q0_state.Size < Q0_cap) //
--			loc_isls = queue_of_int_enqueue(loc_isls,1); //

checkGen :: ColoredNetwork -> MetaIsle -> String
checkGen net (MetaIsle i _ ins outs) = let --outs' = filter (\(MetaComp _ _ t _ _) -> case t of Snk -> True; _ -> False) outs
                                           inconds = map (\x -> inCheckGen net x) ins
                                           outconds = map (\x -> outCheckGen net x) outs
--                                           outconds' = map (\x -> outCheckGen' net x) outs'
                                           res = {-if (outconds' == [])
                                                 then-} "\n\tif (" ++
                                                        foldr (\x y -> case y of "" -> x; _ -> x ++ " & " ++ y) "" (inconds ++ outconds) ++
                                                        ")\n\t\tloc_isls[" ++ show i ++ "] = 1'b1;" 
                                                 {-else "\n\tif (" ++
                                                      foldr (\x y -> case y of "" -> x; _ -> x ++ " & " ++ y) "" (inconds ++ outconds) ++
                                                      ")\n\t\tif (" ++
                                                      foldr (\x y -> case y of "" -> x; _ -> x ++ " & " ++ y) "" (outconds') ++
                                                      ")\n\t\t\tloc_isls = queue_of_int_enqueue(loc_isls," ++ show i ++ ");"-}
                                       in res

{-
srcs = uniqueIDMetaComps . getSources $ metaIsles net
                        srcs' = filter (\(MetaComp i _ _ _ _) -> L.elem i (map (\y -> metaCompToID $ fst y) ins)) srcs
                        res = map (\x -> let sind = elemInd x srcs
-}

inCheckGen :: ColoredNetwork -> MetaComp -> String
inCheckGen net comp = let (MetaComp _ _ t _ _) = comp
                      in case t of
                           Src -> let srcs = uniqueIDMetaComps . getSources $ metaIsles net
                                      sind = elemInd comp srcs 
                                  in "Src" ++ show sind ++ "_o_irdy"
                           Q -> let qs = uniqueIDMetaComps . getQueues $ metaIsles net
                                    qind = elemInd comp qs
                                in "!q" ++ show qind ++ "_is_empty(s.Q" ++ show qind ++ "_state)"
                           _ -> error "Wrong component"

outCheckGen :: ColoredNetwork -> MetaComp -> String
outCheckGen net comp = let (MetaComp _ _ t _ _) = comp
                       in case t of
                            Snk -> let snks = uniqueIDMetaComps . getSinks $ metaIsles net
                                       sind = elemInd comp snks
                                   in "Snk" ++ show sind ++ "_i_trdy"
                            Q -> let qs = uniqueIDMetaComps . getQueues $ metaIsles net
                                     qind = elemInd comp qs
                                 in "!q" ++ show qind ++ "_is_full(s.Q" ++ show qind ++ "_state)"
                            _ -> error "Wrong component"

outCheckGen' :: ColoredNetwork -> MetaComp -> String
outCheckGen' net comp = let (MetaComp _ f t _ _) = comp
                            (MetaIslands _ _ _ _ misls) = metaIsles net
                            allinps = L.concat $ map (\(MetaIsle _ _ x _) -> x) misls
                            allouts = L.concat $ map (\(MetaIsle _ _ _ x) -> x) misls
                            allcomps = allinps ++ allouts
                        in case t of
                             Snk -> case f of
                                      (Arg c) -> case getCompType (getComp allinps c) of
                                                   Src -> "Snk" ++ show (snkInd net comp) ++ "_i_data == Src" ++ show (srcInd net (getComp allcomps c)) ++ "_o_data"
                                                   Q -> "Snk" ++ show (snkInd net comp) ++ "_i_data == s.Q" ++ show (qInd net (getComp allcomps c)) ++ "_state.Contents[Q" ++ show (qInd net (getComp allcomps c)) ++ "_state.Size-1]"
                                                   _ -> error "Wrong component"
                                      _ -> error "Functions support is currently limited"
                             _ -> error "Wrong component"

{-

function bit checkAct;
   for(byte i=0;i<$size(CurrentState.Contents);i++) begin
      if ((CurrentState.Contents[i].Src0_free == 0 & (!Src0_o_irdy || Src0_o_data != CurrentState.Contents[i].Src0_state)) & i<CurrentState.Size)
	return 0;
   end
   return 1;
endfunction

-}

checkActGen :: Int -> ColoredNetwork -> String
checkActGen q net = let srcs = getSources $ metaIsles net
                        conds = map (\x -> let i = srcInd net x in "(CurrentState.Contents[i].Src" ++ show i ++ "_free == 0 & (!Src" ++ show i ++ "_o_irdy || Src" ++ show i ++ "_o_data != CurrentState.Contents[i].Src" ++ show i ++ "_state)) & i<CurrentState.Size") srcs
                        res = "function bit checkAct;\n\tfor(" ++ sizeToType q ++ " i=0;i<$size(CurrentState.Contents);i++) begin\n\t\tif (" ++
                              foldr (\x y -> case y of "" -> x; _ -> x ++ " & " ++ y) "" conds ++
                              ")\n\t\t\treturn 0;\n\tend\n\treturn 1;\nendfunction"
                    in res

mainGen :: Int -> ColoredNetwork -> String
mainGen q net = let srcs = uniqueIDMetaComps . getSources $ metaIsles net
                    (MetaIslands _ _ _ _ misls) = metaIsles $ net
                    conds = foldr (\x y -> x ++ y) ""
                            (map (\x -> let i = inpInd net x
                                            j = elemInd x srcs
                                            i' = foldr (\g h -> case h of "" -> g ++ h; _ -> g ++ " | " ++ h) "" (map (\w -> "hasElem(" ++ (show w) ++ ",Confs.Contents[j])") i)
                                        in "\n\t\t\t\t\t\t\t\tcheck = (" ++ i' ++ ");\n\n\t\t\t\t\t\t\t\tif (check == 0 && Src" ++ (show j) ++ "_o_irdy == 1) begin\n\t\t\t\t\t\t\t\t\ttmpState.Src" ++ show j ++ "_state = Src" ++ show j ++ "_o_data;\n\t\t\t\t\t\t\t\t\ttmpState.Src" ++ show j ++ "_free = 0;\n\t\t\t\t\t\t\t\tend\n\t\t\t\t\t\t\t\tcheck = (" ++ i' ++ ") ;\n\n\t\t\t\t\t\t\t\tif (check == 1 && Src" ++ show j ++ "_o_irdy == 1)\n\t\t\t\t\t\t\t\t\ttmpState.Src" ++ show j ++ "_free = 1;\n\t\t\t\t\t\t\t\tfor(" ++ sizeToType (L.length misls) ++ " h=0;h<" ++ show (L.length misls) ++ ";h++) begin\n\t\t\t\t\t\t\t\t\tif(Confs.Contents[j][h] == 1) begin\n\t\t\t\t\t\t\t\t\t\ttmpState = upd(h,tmpState);\n\t\t\t\t\t\t\t\t\tend\n\t\t\t\t\t\t\t\tend") srcs)
                    conds' = foldr (\x y -> x ++ y) ""
                             (map (\x -> let j = elemInd x srcs
                                         in "\n\t\t\t\t\t\t\t\tif(Src" ++ show j ++ "_o_irdy == 1) begin\n\t\t\t\t\t\t\t\t\ttmpState.Src" ++ show j ++ "_state = Src" ++ show j ++ "_o_data;\n\t\t\t\t\t\t\t\t\ttmpState.Src" ++ show j ++ "_free = 0;\n\t\t\t\t\t\t\t\tend") srcs)
                    res = "always@(posedge Clock) begin\n\tif (Reset) begin\n\t\tCurrentState = InitialState;\n\t\tfor (" ++ sizeToType q ++ " i=0;i<`SIZE;i++) begin\n\t\t\tNextState.Contents[i] = " ++ defaultStateGen net ++ ";\n\t\tend\n\n\t\tTIsls = " ++ show (L.length misls) ++ "'b" ++ concat (take (L.length misls) (repeat "0")) ++ ";\n\n\t\tfor (" ++ sizeToType q ++ " i=0;i<$size(Confs.Contents);i++) begin\n\t\t\tConfs.Contents[i] = " ++ show (L.length misls) ++ "'b" ++ concat (take (L.length misls) (repeat "0")) ++ ";\n\t\tend\n\t\tConfs.Size = 0;\n\n\t\ttmpState = " ++ defaultStateGen net ++ ";\n\n\t\tNextState.Size = 0;\n\n\t\tcheck = 0;\n\n\t\terr = 0;\n\t\tovf = 0;\n\n\t\tError = 0;\n\t\tOverflow = 0;\n\n\tend\n\telse begin\n\n\t\terr = 0;\n\n\t\tovf = 0;\n\n\t\tcheck = 1;\n\n\t\tif (!Error & !Overflow) begin\n\t\t\tcheck = checkAct();\n\n\t\t\tif (check) begin\n\n\t\t\t\tfor (" ++ sizeToType q ++ " i = 0;i<$size(NextState.Contents);i++) begin\n\t\t\t\t\tNextState.Contents[i] = " ++ defaultStateGen net ++ ";\n\t\t\t\tend\n\n\t\t\t\tNextState.Size = 0;\n\n\t\t\t\tfor(" ++ sizeToType q ++ " i=0;i<$size(CurrentState.Contents);i++) begin\n\n\t\t\t\t\tif(i<CurrentState.Size) begin\n\n\t\t\t\t\t\tConfs.Size = 0;\n\n\t\t\t\t\t\tTIsls = checkIsls(CurrentState.Contents[i]);\n\n\t\t\t\t\t\tConfs = getLegalConfs(TIsls);\n\t\t\t\t\t\ttmpState = CurrentState.Contents[i];\n\n\t\t\t\t\t\tfor(" ++ sizeToType q ++ " j=0;j<$size(Confs.Contents);j++) begin\n\t\t\t\t\t\t\tif (j<Confs.Size) begin\n\t\t\t\t\t\t\t\ttmpState = CurrentState.Contents[i];" ++
                          conds ++ "\n\t\t\t\t\t\t\tend\n\n\t\t\t\t\t\t\tif (Confs.Size == 0) begin\n\t\t\t\t\t\t\t\ttmpState = CurrentState.Contents[i];"
                          ++ conds' ++ "\n\t\t\t\t\t\t\tend\n\n\t\t\t\t\t\t\tcheck = determ_state_exists(NextState,tmpState);\n\n\t\t\t\t\t\t\tif(check == 0)\n\t\t\t\t\t\t\t\tif(NextState.Size <`SIZE)\n\t\t\t\t\t\t\t\t\tNextState = determ_state_enqueue(NextState,tmpState);\n\t\t\t\t\t\t\t\telse\n\t\t\t\t\t\t\t\t\tovf = 1;\n\t\t\t\t\t\tend\n\t\t\t\t\tend\n\t\t\t\tend\n\t\t\tend\n\t\t\telse err = 1;\n\t\tend\n\n\t\tCurrentState = NextState;\n\t\tError = err;\n\t\tOverflow = ovf;\n\tend\nend"
                in res

      
 

--data MetaComp = MetaComp ComponentID FunComp CompType IOColor Capacity
getAllQueueStates :: MetaComp -> [[Color]]
getAllQueueStates (MetaComp _ _ Q (IOColor c) (Capacity n)) = [[]] ++ (L.sort $ concat [replicateM i ((S.toList c))| i <- [1..n]])
getAllQueueStates (MetaComp _ _ _ _ _) = []

getAllQueueStatesTest :: ColoredNetwork -> String
getAllQueueStatesTest net = let qs = L.sort . uniqueIDMetaComps . getQueues $ metaIsles net
                            in show $ map (\x -> getAllQueueStates x) qs
--data CompType = Src | Snk | Q | Frk | CJ | FJ | Swtch | Mrg deriving (Show,Eq,Ord)
condGen' :: ColoredNetwork -> MetaComp -> Color -> String
condGen' net comp col = case comp of
                          (MetaComp _ _ Src (IOColor c) _) -> let c' = S.toList c
                                                              in if (L.elem col c')
                                                                 then let srcs = uniqueIDMetaComps . getSources $ metaIsles net
                                                                          sind = elemInd comp srcs
                                                                          tm = typeMap net
                                                                          col' = if ((showColor col) /= "")
                                                                                 then if (head (showColor col) == '\'')
                                                                                      then (tm BM.! c) ++ (showColor col)
                                                                                      else showColor col
                                                                                 else showColor col
                                                                      in "Src" ++ show sind ++ "_o_data == " ++ col'
                                                                 else error "condGen' : wrong color"
                          (MetaComp _ _ Q (IOColor c) _) -> let c' = S.toList c
                                                            in if (L.elem col c')
                                                               then let qs = uniqueIDMetaComps . getQueues $ metaIsles net
                                                                        qind = elemInd comp qs
                                                                        qstates = filter (\x -> x /= []) $ getAllQueueStates comp
                                                                        qstates' = filter (\x -> last x == col) qstates
                                                                        --binaryState (L.length . toBin $ L.length queueStates) (fromJust (L.elemIndex x queueStates))
                                                                        res = map (\x -> "s.Q" ++ show qind ++ "_state == " ++ binaryState (L.length (toBin (L.length (getAllQueueStates comp) - 1))) (fromJust (L.elemIndex x (getAllQueueStates comp)))) qstates'
                                                                    in "(" ++ (foldr (\x y -> case y of "" -> x; _ -> x ++ " | " ++ y) "" res) ++ ")"
                                                               else error "condGen' : wrong color"
                          _ -> error "condGen' : wrong component"

condGen'' :: ColoredNetwork -> MetaComp -> [(ChannelID,Color)] -> String
condGen'' net m cs = let snks = uniqueIDMetaComps . getSinks $ metaIsles net
                         (MetaComp _ _ _ (IOColor c) _) = m
                         sind = elemInd m snks
                         tm = typeMap net
                         m' = head $ getInChannels net $ metaCompToID m
                         res = case filter (\(x,_) -> x == m') cs of
                                 [] -> ""
                                 z -> let col = snd $ head z
                                          col' = if ((showColor col) /= "")
                                                 then if (head (showColor col) == '\'')
                                                      then (tm BM.! c) ++ (showColor col)
                                                      else showColor col
                                                 else showColor col
                                      in "Snk" ++ show sind ++ "_i_data == " ++ col'
                     in res

elemInd :: MetaComp -> [MetaComp] -> Int
elemInd m1 m2 = elemInd' m1 m2 0
  where elemInd' :: MetaComp -> [MetaComp] -> Int -> Int
        elemInd' _ [] _ = error "elemInd : component not found"
        elemInd' (MetaComp i q w e r) ((MetaComp j _ _ _ _):ms) n = if (i == j)
                                                                    then n
                                                                    else elemInd' (MetaComp i q w e r) ms (n+1)

condGenTest :: ColoredNetwork -> String
condGenTest net = let q = head . uniqueIDMetaComps . getQueues $ metaIsles net
                      (MetaComp _ _ _ (IOColor c) _) = q
                      col = (S.toList c) !! 1
                  in condGen' net q col


updGen :: ColoredNetwork -> String
updGen net = let (MetaIslands _ _ _ _ misls) = metaIsles net
                 islconds = concat $ map (\x -> updIslGen net x) misls
                 res = "function state upd;\n\tinput " ++ sizeToType (L.length misls) ++ " i;\n\tinput state s;\n\tstate loc_s;\n\n\tloc_s = s;\n\n\tcase(i)" ++ islconds ++ "\n\tendcase\n\treturn loc_s;\nendfunction"
             in res

lstrip :: String -> String
lstrip = dropWhile (\x -> L.elem x [' ','\t','\n'])
                
updIslGen :: ColoredNetwork -> MetaIsle -> String
updIslGen net misl = let (MetaIsle i _ ins outs) = misl
                         outs' = map (\(MetaComp t _ _ _ _) -> head $ getInChannels net t) outs
                         inColors = allIns net misl
                         inQueues = filter (\x -> case x of (MetaComp _ _ Q _ _) -> True; _ -> False) ins
                         outQueues = filter (\x -> case x of (MetaComp _ _ Q _ _) -> True; _ -> False) outs
                         snks = filter (\x -> case x of (MetaComp _ _ Snk _ _) -> True; _ -> False) outs
                         conds = map (\z -> let p = propagateColors net misl (map (\((MetaComp t _ _ _ _),t') -> ((head $ getOutChannels net t),t')) z)
                                                p' = map (\(w,_) -> w) p
                                                cond = S.isSubsetOf (S.fromList outs') (S.fromList p') 
                                            in "if(" ++ foldr (\m n -> case n of "" -> m; _ -> m ++ " & " ++ n) "" ((map (\(x,y) -> condGen' net x y) z) ++ (map (\x -> condGen'' net x p) snks)) ++ ") begin" ++ (case cond of True -> ((outQueuesUpd net p outQueues) ++ (inQueuesUpd net inQueues)); _ -> (failedUpd net z)) ++ "\n\t\t\tend") inColors
                     in "\n\t\t" ++ show i ++ ":begin" ++ (foldl (\x y -> case x of "" -> "\n\t\t\t" ++ y; _ -> x ++ {- "\n\t\t\telse " ++ y) -} "\n\t\t\t" ++ y) "" conds) ++ "\n\t\tend"

outQueuesUpd :: ColoredNetwork -> [(ChannelID,Color)] -> [MetaComp] -> String
outQueuesUpd net ps cs = let qs = uniqueIDMetaComps . getQueues $ metaIsles net
                             res = map (\x -> let qind = elemInd x qs
                                                  col = case (filter (\(y,_) -> y == (head $ getInChannels net (metaCompToID x))) ps) of
                                                          [] -> error "outQueuesUpd : error"
                                                          w -> snd $ head w
                                              in "\n\t\t\t\tloc_s.Q" ++ show qind ++ "_state = q" ++ show qind ++ "_upd_in(s.Q" ++ show qind ++ "_state," ++ showColor col ++ ");"  
                                       ) cs
                         in concat res

inQueuesUpd :: ColoredNetwork -> [MetaComp] -> String
inQueuesUpd net cs = let qs = uniqueIDMetaComps . getQueues $ metaIsles net
                         res = map (\x -> let qind = elemInd x qs
                                          in "\n\t\t\t\tloc_s.Q" ++ show qind ++ "_state = q" ++ show qind ++ "_upd_out(s.Q" ++ show qind ++ "_state);"
                                   ) cs
                     in concat res

failedUpd :: ColoredNetwork -> [(MetaComp,Color)] -> String
failedUpd net ins = let srcs = uniqueIDMetaComps . getSources $ metaIsles net
                        srcs' = filter (\(MetaComp i _ _ _ _) -> L.elem i (map (\y -> metaCompToID $ fst y) ins)) srcs
                        res = map (\x -> let sind = elemInd x srcs
                                         in "\n\t\t\t\tloc_s.Src" ++ show sind ++ "_free = 0;\n\t\t\t\tloc_s.Src" ++ show sind ++ "_state = Src" ++ show sind ++ "_o_data;" 
                                  ) srcs'
                    in concat res

updIslGenTest :: ColoredNetwork -> String
updIslGenTest net = let (MetaIslands _ _ _ _ misls) = metaIsles net
                    in updIslGen net (misls !! 0)

--data MetaComp = MetaComp ComponentID FunComp CompType IOColor Capacity deriving (Show,Eq,Ord)

allIns :: ColoredNetwork -> MetaIsle -> [[(MetaComp,Color)]]
allIns _ (MetaIsle _ _ ins _) = let cols = map (\(MetaComp _ _ _ (IOColor c) _) -> S.toList c) ins
                                    cols' = permute cols
                                    --ins' = map (\(MetaComp i _ _ _ _) -> head $ getOutChannels net i) ins
                                    res = map (\x -> zip ins x) cols'
                                in res

permute :: [[a]] -> [[a]]
permute [] = [[]]
permute (xs:xss) = [[y] ++ ys|y <- xs,ys <- permute xss]

allInsTest :: ColoredNetwork -> String
allInsTest net = let (MetaIslands _ _ _ _ misls) =  metaIsles net in show $ allIns net (head misls)

updQueueGen :: ColoredNetwork -> String
updQueueGen net = let queues = uniqueIDMetaComps . getQueues $ metaIsles net
                  in L.concat $ map (\x -> (updQueueInGen net x) ++ "\n" ++ (updQueueOutGen net x) ++ "\n" ++ (updQueueIsFullGen net x) ++ "\n" ++ (updQueueIsEmptyGen net x) ++ "\n\n") queues

binaryState :: Int -> Int -> String
binaryState a x = let y = toBin x
                      z = L.length y
                  in show a ++ "'b" ++ (L.concat $ map (\(t::Int) -> show t) $ take (a-z) $ repeat 0) ++ (L.concat $ map (\t -> show t) y)

updQueueInGen :: ColoredNetwork -> MetaComp -> String
updQueueInGen net comp = let queues = metaCompsToIDs . uniqueIDMetaComps . getQueues $ metaIsles net
                             queueStates = getAllQueueStates comp
                             qind = fromJust $ L.elemIndex (metaCompToID comp) queues
                             (MetaComp _ _ _ (IOColor c) (Capacity cap)) = comp
                             c' = S.toList c
                             tm = typeMap net
                             qtype = tm BM.! c
                             nxt = \(s::[Color]) (a::Color) -> case (L.length (a:s) <= cap) of
                                                                 True -> (a:s)
                                                                 False -> s 
                             cases = L.concat $ map (\x -> "\n\t\t" ++ binaryState (L.length . toBin $ (L.length queueStates - 1)) (fromJust (L.elemIndex x queueStates)) ++ ": begin\n\t\t\tcase(d)" ++ (L.concat $ map (\y -> "\n\t\t\t\t" ++ showColor y ++ ":return " ++ binaryState (L.length . toBin $ (L.length queueStates - 1)) (fromJust (L.elemIndex (nxt x y) queueStates)) ++ ";") c') ++ "\n\t\t\tendcase\n\t\tend") queueStates
                         in let w = ((L.length (toBin (L.length queueStates - 1))) - 1)
                                r = case w of
                                      0 -> "\tbit"
                                      _ -> "\tbit[" ++ show w ++ ":0]"
                            in "function " ++ r ++ " q" ++ show qind ++ "_upd_in;\n\tinput " ++ r ++ " q" ++ show qind ++ "_old_state;\n\tinput " ++ qtype ++ " d;\n\tcase(q" ++ show qind ++ "_old_state)" ++ cases ++ "\n\tendcase\nendfunction"
--(L.length . toBin $ (L.length (getAllQueueStates x) - 1) - 1)
updQueueInGenTest :: ColoredNetwork -> String
updQueueInGenTest net = let q = head . uniqueIDMetaComps . getQueues $ metaIsles net
                        in updQueueInGen net q


updQueueOutGen :: ColoredNetwork -> MetaComp -> String
updQueueOutGen net comp = let queues = metaCompsToIDs . uniqueIDMetaComps . getQueues $ metaIsles net
                              queueStates = getAllQueueStates comp
                              qind = fromJust $ L.elemIndex (metaCompToID comp) queues
                              nxt = \(s::[Color]) -> case (L.length s > 0) of
                                                       True -> (take ((L.length s) - 1) s)
                                                       False -> s
                              cases = L.concat $ map (\x -> "\n\t\t" ++ binaryState (L.length . toBin $ (L.length queueStates - 1)) (fromJust (L.elemIndex x queueStates)) ++ ":return " ++ binaryState (L.length . toBin $ (L.length queueStates - 1)) (fromJust (L.elemIndex (nxt x) queueStates)) ++ ";") queueStates
                              w = ((L.length (toBin (L.length queueStates - 1))) - 1)
                              r = case w of
                                    0 -> "\tbit"
                                    _ -> "\tbit[" ++ show w ++ ":0]"
                          in "function " ++ r ++ " q" ++ show qind ++ "_upd_out;\n\tinput " ++ r ++ " q" ++ show qind ++ "_old_state;\n\tcase(q" ++ show qind ++ "_old_state)" ++ cases ++ "\n\tendcase\nendfunction"
                              
updQueueOutGenTest :: ColoredNetwork -> String
updQueueOutGenTest net = let q = head . uniqueIDMetaComps . getQueues $ metaIsles net
                         in updQueueOutGen net q


updQueueIsFullGen :: ColoredNetwork -> MetaComp -> String
updQueueIsFullGen net  comp = let queues = metaCompsToIDs . uniqueIDMetaComps . getQueues $ metaIsles net
                                  queueStates = getAllQueueStates comp
                                  qind = fromJust $ L.elemIndex (metaCompToID comp) queues
                                  (MetaComp _ _ _ _ (Capacity cap)) = comp
                                  rst = \(s::[Color]) -> case L.length s < cap of
                                                           True -> "1'b0"
                                                           False -> "1'b1"
                                  w = ((L.length (toBin (L.length queueStates - 1))) - 1)
                                  r = case w of
                                        0 -> "\tbit"
                                        _ -> "\tbit[" ++ show w ++ ":0]"
                                  cases = L.concat $ map (\x -> "\n\t\t" ++ binaryState (L.length . toBin $ (L.length queueStates - 1)) (fromJust (L.elemIndex x queueStates)) ++ ":return " ++ rst x ++ ";") queueStates
                              in "function bit q" ++ show qind ++ "_is_full;\n\tinput " ++ r ++ " q" ++ show qind ++ "_s;\n\tcase(q" ++ show qind ++ "_s)" ++ cases ++ "\n\tendcase\nendfunction"

updQueueIsFullTest :: ColoredNetwork -> String
updQueueIsFullTest net = let q = head . uniqueIDMetaComps . getQueues $ metaIsles net
                         in updQueueIsFullGen net q


updQueueIsEmptyGen :: ColoredNetwork -> MetaComp -> String
updQueueIsEmptyGen net  comp = let queues = metaCompsToIDs . uniqueIDMetaComps . getQueues $ metaIsles net
                                   queueStates = getAllQueueStates comp
                                   qind = fromJust $ L.elemIndex (metaCompToID comp) queues
                                   rst = \(s::[Color]) -> case L.length s > 0 of
                                                            True -> "1'b0"
                                                            False -> "1'b1"
                                   w = ((L.length (toBin (L.length queueStates - 1))) - 1)
                                   r = case w of
                                         0 -> "\tbit"
                                         _ -> "\tbit[" ++ show w ++ ":0]"
                                   cases = L.concat $ map (\x -> "\n\t\t" ++ binaryState (L.length . toBin $ (L.length queueStates - 1)) (fromJust (L.elemIndex x queueStates)) ++ ":return " ++ rst x ++ ";") queueStates
                               in "function bit q" ++ show qind ++ "_is_empty;\n\tinput " ++ r ++ " q" ++ show qind ++ "_s;\n\tcase(q" ++ show qind ++ "_s)" ++ cases ++ "\n\tendcase\nendfunction"

updQueueIsEmptyTest :: ColoredNetwork -> String
updQueueIsEmptyTest net = let q = head . uniqueIDMetaComps . getQueues $ metaIsles net
                          in updQueueIsEmptyGen net q

elem' :: Eq a => (a,b) -> [(a,b)] -> Bool
elem' (_,_) [] = False
elem' (x,z) ((y,_):ys)
  | x == y = True
  | otherwise = elem' (x,z) ys

uniqueIDs :: Eq a => [(a,b)] -> Bool
uniqueIDs [] = True
uniqueIDs (x:xs) = (not (elem' x xs)) && (uniqueIDs xs)

getIslInps :: ColoredNetwork -> MetaIsle -> [[(ChannelID,Color)]]
getIslInps net (MetaIsle _ _ ins _) = let x = concat $ map (\(MetaComp i _ _ (IOColor c) _) -> [(head (getOutChannels net i),c')| c' <- S.toList c]) ins
                                      in filter (\y -> uniqueIDs y) $ replicateM (L.length ins) x




propTest :: ColoredNetwork -> String
propTest net = let (MetaIslands _ _ _ _ misls) = makeMetaIslands net
                   m = misls !! 0
                   (MetaIsle _ _ m' _) = m
                   ins = map (\(MetaComp z _ _ (IOColor c) _) -> ((head $ getOutChannels net z), head $ S.toList c)) m'
               in (show $ propagateColors net m ins)

propagateColors :: ColoredNetwork -> MetaIsle -> [(ChannelID,Color)] -> [(ChannelID,Color)]
propagateColors net (MetaIsle _ m _ _) z = propagateColors' z []
  where propagateColors' :: [(ChannelID,Color)] -> [(ChannelID,Color)] -> [(ChannelID,Color)]
        propagateColors' [] res = res
        propagateColors' ((x,col):xs) res = let x' = getTarget net x
                                                ins = L.intersect (getInChannels net x') m
                                                ins' = L.nub $ filter (\(t,_) -> elem t ins) ((x,col):xs)
                                                other = L.nub $ filter (\(t,_) -> not $ elem t ins) ((x,col):xs)
                                            in if (L.length ins == L.length ins')
                                               then case getComponent net x' of
                                                      (Source _ _) -> error "propagateColors - wrong component: Source"
                                                      (PatientSource _ _) -> error "propagateColors - wrong component: PatientSource"
                                                      (Sink _) -> propagateColors' other (L.nub (ins' ++ res))
                                                      (DeadSink _) -> propagateColors' other (L.nub (ins' ++ res))
                                                      (Queue _ _) -> propagateColors' other (L.nub (ins' ++ res))
                                                      (Function _ f _) -> let col' = eval (makeVArguments [col]) f
                                                                              out = head $ getOutChannels net x'
                                                                          in propagateColors' (L.nub ((out,col'):other) ++ res) []
                                                      (Switch _ ps) -> let outs = getOutChannels net x'
                                                                           (rs:: [Bool]) = map (\t -> eval (makeVArguments [col]) t) ps
                                                                           out = if (L.intersect outs m /= [])
                                                                                 then if (rs !! (fromJust $ L.elemIndex (head (L.intersect outs m)) outs))
                                                                                      then ([(head (L.intersect outs m),col)])
                                                                                      else []
                                                                                 else []
                                                                       in propagateColors' (L.nub (out ++ other ++ res)) []
                                                      (Merge _) -> let outs = getOutChannels net x'
                                                                       out = map (\t -> (t,col)) (L.intersect outs m)
                                                                   in propagateColors' (L.nub (out ++ other ++ res)) []
                                                      (Fork _) -> let outs = getOutChannels net x'
                                                                      outs' = map (\t -> (t,col)) outs
                                                                  in propagateColors' (L.nub (outs' ++ other ++ res)) []
                                                      (ControlJoin _) -> let outs = getOutChannels net x'
                                                                             out = outs !! 0
                                                                             outs' = map (\t -> (t,col)) $ L.intersect [out] m
                                                                         in propagateColors' (L.nub (outs' ++ other ++ res)) []
                                                      (FControlJoin _ p) -> let outs = getOutChannels net x'
                                                                                out = head outs
                                                                                i = getInChannels net x'
                                                                                i' = map (\t -> (t,getInColor t ((x,col):xs))) i
                                                                                (rs:: [Bool]) = map (\(_,t) -> eval (makeVArguments [t]) p) i'
                                                                                r = fromJust $ L.elemIndex True rs
                                                                                i'' = i' !! r
                                                                                outs' = if (L.elem i'' ins')
                                                                                        then [(out,snd i'')]
                                                                                        else []
                                                                            in propagateColors' (L.nub (outs' ++ other ++ res)) []
                                                      (Match _ _) -> error "propagateColors: match primitive is not supported yet"
                                                      (MultiMatch _ p) -> let i = L.intersect (getInChannels net x') (map (\(t,_) -> t) ins')
                                                                              index1 = fromJust $ L.elemIndex (i !! 0) (getInChannels net x')
                                                                              index2 = fromJust $ L.elemIndex (i !! 1) (getInChannels net x')
                                                                              inp1 = if (index1 < index2)
                                                                                     then i !! 0
                                                                                     else i !! 1
                                                                              inp2 = if (index1 > index2)
                                                                                     then i !! 0
                                                                                     else i !! 1
                                                                              c1 = getInColor inp1 ((x,col):xs)
                                                                              c2 = getInColor inp2 ((x,col):xs)
                                                                              cond = matched p c1 c2
                                                                              out = if (L.intersect (getOutChannels net x') m /= [])
                                                                                    then head $ L.intersect (getOutChannels net x') m
                                                                                    else error "propagateColors: MultiMatch error"
                                                                          in if cond
                                                                             then propagateColors' (L.nub ([(out,c1)] ++ other ++ res)) []
                                                                             else propagateColors' other (L.nub (ins' ++ res))
                                                      (LoadBalancer _) -> let outs = getOutChannels net x'
                                                                              outs' = map (\t -> (t,col)) $ L.intersect outs m
                                                                              outs'' = if ((L.length outs') /= 0)
                                                                                       then [head outs']
                                                                                       else []
                                                                          in propagateColors' (L.nub (outs'' ++ other ++ res)) []
                                                      _ -> []
                                               else propagateColors' xs ((x,col):res)


confsSub :: [Int] -> [Int] -> [Int]
confsSub c1 c2 = let res = confsSub' c1 c2
                     res' = filter (\x -> x >= 0) res
                 in if (L.length res == L.length res')
                    then res
                    else c1
  where confsSub' :: [Int] -> [Int] -> [Int]
        confsSub' [] [] = []
        confsSub' [] (_:_) = error "confsSub' : lengths of configurations do not match"
        confsSub' (_:_) [] = error "confsSub' : lengths of configurations do not match"
        confsSub' (x:xs) (y:ys) = if (x-y >= 0)
                                  then (x-y:confsSub' xs ys)
                                  else (0:confsSub' xs ys)

confsSubTest :: [Int] -> [Int] -> String
confsSubTest x y = show $ confsSub x y

illegalToLegal :: ColoredNetwork -> [([Int],[[Int]])]
illegalToLegal net = let (MetaIslands _ _ _ _ misls) = makeMetaIslands net
                         confs = replicateM (L.length misls) [0,1]
                         lconfs = allLegalConfs net
                         ilconfs = confs L.\\ lconfs
                     in map (\x -> illegalToLegal' x x lconfs (x,[])) ilconfs
  where illegalToLegal' :: [Int] -> [Int] -> [[Int]] -> ([Int],[[Int]]) -> ([Int],[[Int]])
        illegalToLegal' _ _ [] res = res --error "illegalToLegal : error"
        illegalToLegal' ic jc (l:ls) (g,gs) = let ic' = foldr (\x y -> x + y) 0 ic
                                                  chk = foldr (\x y -> x && y) True $ map (\x -> if (l !! x == jc !! x) then True else False) (islandsWithoutNDComponents net)
                                              in if (ic' == 0)
                                                 then (g,gs)
                                                 else if chk
                                                      then let z = confsSub (nullNonNDIslands net ic) (nullNonNDIslands net l)
                                                               z' = foldr (\x y -> x + y) 0 z
                                                               z'' = foldr (\x y -> x + y) 0 (nullNonNDIslands net ic)
                                                           in if (z' < z'')
                                                              then illegalToLegal' z jc ls (g,gs++[l])
                                                              else illegalToLegal' ic jc ls (g,gs)
                                                      else illegalToLegal' ic jc ls (g,gs)

checkZeroes :: [Int] -> [Int] -> Bool
checkZeroes [] (_:_) = error "checkZeroes : configuration sizes do not match"
checkZeroes (_:_) [] = error "checkZeroes : configuration sizes do not match"
checkZeroes [] [] = True
checkZeroes (0:_) (1:_) = False
checkZeroes (_:xs) (_:ys) = checkZeroes xs ys 

confDiff :: [Int] -> [Int] -> Int
confDiff [] (_:_) = error "checkZeroes : configuration sizes do not match"
confDiff (_:_) [] = error "checkZeroes : configuration sizes do not match"
confDiff [] [] = 0
confDiff (x:xs) (y:ys)
  | x /= y = 1 + (confDiff xs ys)
  | otherwise = confDiff xs ys

illegalToLegal2 :: ColoredNetwork -> [([Int],[[Int]])]
illegalToLegal2 net = let (MetaIslands _ _ _ _ misls) = makeMetaIslands net
                          confs = replicateM (L.length misls) [0,1]
                          lconfs = allLegalConfs net
                          ilconfs = confs L.\\ lconfs
                      in map (\x -> (x,illegalToLegal2' x lconfs)) ilconfs
  where illegalToLegal2' :: [Int] -> [[Int]] -> [[Int]]
        illegalToLegal2' conf lconfs = let aconfs = filter (\x -> checkZeroes conf x) lconfs
                                           minDif = if (L.length aconfs /= 0)
                                                    then (L.minimum $ map (\x -> confDiff conf x) aconfs)
                                                    else L.length conf
                                       in filter (\x -> case (confDiff conf x == minDif) of True -> True ; _ -> False) aconfs

--returns indices of islands, which do not contain non-deterministic components (merges, load balancers, multimatches)
islandsWithoutNDComponents :: ColoredNetwork -> [Int]
islandsWithoutNDComponents net = let (MetaIslands _ _ _ _ misls) = makeMetaIslands net
                                 in islandsWithoutNDComponents' misls [] 0
  where islandsWithoutNDComponents' :: [MetaIsle] -> [Int] -> Int -> [Int]
        islandsWithoutNDComponents' [] res _ = res
        islandsWithoutNDComponents' (m:ms) res i = let (MetaIsle _ chans _ _) = m
                                                       mrgs = getAllMergeIDs net
                                                       lbs = getAllLoadBalancerIDs net
                                                       mms = getAllMultiMatchIDs net
                                                       mrgsins = L.concat $ map (\x -> getInChannels net x) mrgs
                                                       lbsouts = L.concat $ map (\x -> getOutChannels net x) lbs
                                                       mmsins = L.concat $ map (\x -> getInChannels net x) mms
                                                   in if (L.intersect (mrgsins ++ lbsouts ++ mmsins) chans == [])
                                                      then islandsWithoutNDComponents' ms (i:res) (i+1)
                                                      else islandsWithoutNDComponents' ms res (i+1)

islandsWithoutNDComponentsTest :: ColoredNetwork -> String
islandsWithoutNDComponentsTest net = show $ islandsWithoutNDComponents net

nullNonNDIslands :: ColoredNetwork -> [Int] -> [Int]
nullNonNDIslands net conf = nullNonNDIslands' conf 0 (islandsWithoutNDComponents net) []
  where nullNonNDIslands' :: [Int] -> Int -> [Int] -> [Int] -> [Int]
        nullNonNDIslands' [] _ _ res = res
        nullNonNDIslands' (x:xs) i nonnd res = if (L.elem i nonnd)
                                               then nullNonNDIslands' xs (i+1) nonnd (res ++ [0])
                                               else nullNonNDIslands' xs (i+1) nonnd (res ++ [x])
                                                 
nullNonNDIslandsTest :: ColoredNetwork -> String
nullNonNDIslandsTest net = show (nullNonNDIslands net [1,1,1]) ++ " " ++ show (nullNonNDIslands net [1,1,0])
                                     
{-
findLegal :: [Int] -> [[Int]] -> Maybe [Int]
findLegal x xs = findLegal' x xs Nothing
  where findLegal' :: [Int] -> [[Int]] -> Maybe [Int] -> Maybe [Int]
        findLegal' _ [] res = res
        findLegal' y (z:zs) res = let t = confsSub y z
                                      t' = foldr (\a b -> a + b) 0 t
                                      y' = foldr (\a b -> a + b) 0 y
                                  in if (t' < y')
                                     then case res of
                                            Nothing -> findLegal' y zs (Just z)
                                            Just p -> if (t' > (foldr (\a b -> a + b) 0 p))
                                                      then findLegal' y zs (Just z)
                                                      else findLegal' y zs res
                                     else findLegal' y zs res
-}
illegalToLegalTest :: ColoredNetwork -> String
illegalToLegalTest net = show $ illegalToLegal net

allLegalConfs :: ColoredNetwork -> [[Int]]
allLegalConfs net = let (MetaIslands _ _ _ _ misls) = makeMetaIslands net
                        confs = replicateM (L.length misls) [0,1]
                        res = filter (\x -> checkConf net x) confs
                    in res

--data MetaIsle = MetaIsle Int [ChannelID] [MetaComp] [MetaComp] deriving (Show,Eq,Ord)
getTransferChannels :: ColoredNetwork -> [Int] -> [ChannelID]
getTransferChannels net conf = getTransferChannels' net conf 0 []
  where getTransferChannels' :: ColoredNetwork -> [Int] -> Int -> [ChannelID] -> [ChannelID]
        getTransferChannels' _ [] _ res = res
        getTransferChannels' n (x:xs) i res = let (MetaIslands _ _ _ _ misls) = makeMetaIslands n
                                                  (MetaIsle _ chans _ _) = misls !! i
                                              in if (x == 1)
                                                 then getTransferChannels' net xs (i+1) (L.nub $ res ++ chans)
                                                 else getTransferChannels' net xs (i+1) res

checkConf :: ColoredNetwork -> [Int] -> Bool
checkConf net conf = let trans = getTransferChannels net conf
                         merges = getAllMergeIDs net
                         mms = getAllMultiMatchIDs net
                         lbs = getAllLoadBalancerIDs net
                         merges' = map (\x -> checkMergeLegal net x trans) merges
                         mms' = map (\x -> checkMultiMatchLegal net x trans) mms
                         lbs' = map (\x -> checkLoadBalancerLegal net x trans) lbs
                         res = foldr (\x y -> x && y) True (merges' ++ mms' ++ lbs')
                     in res
        
--network, merge componentID, island channels
checkMergeLegal :: ColoredNetwork -> ComponentID -> [ChannelID] -> Bool
checkMergeLegal net c ms = let ins = getInChannels net c
                           in L.length (L.intersect ins ms) < 2

--network, load balancer componentID, island channels
checkLoadBalancerLegal :: ColoredNetwork -> ComponentID -> [ChannelID] -> Bool
checkLoadBalancerLegal net c ms = let outs = getOutChannels net c
                        in L.length (L.intersect outs ms) < 2

--network, multimatch componentID, island channels
checkMultiMatchLegal :: ColoredNetwork -> ComponentID -> [ChannelID] -> Bool
checkMultiMatchLegal net c ms = let ins = getInChannels net c
                                    outs = getOutChannels net c
                                    ins1 = take (L.length outs) ins
                                    ins2 = drop (L.length outs) ins
                                    x = L.length (L.intersect ins1 ms)
                                    y = L.length (L.intersect ins2 ms)
                                in ((x == 0 && y == 0) || (x == 1 && y == 1))

legalConfsTest :: ColoredNetwork -> String
legalConfsTest net = show $ allLegalConfs net

getInColor :: ChannelID -> [(ChannelID,Color)] -> Color
getInColor i cs = case (filter (\(x,_) -> i == x) cs) of
                    [] -> error "getInColor: channel not found"
                    _ -> head $ map (\(_,x) -> x) $ (filter (\(x,_) -> i == x) cs)

nrStates :: ColoredNetwork -> Int
nrStates net = let misls = metaIsles net
                   srcs = getSources misls
                   srcs' = map (\(MetaComp _ _ _ (IOColor c) _) -> (S.size c) + 1) srcs
                   qs = getQueues misls
                   qs' = map (\(MetaComp _ _ _ (IOColor c) (Capacity cap)) -> (if (cap > 1)
                                                                               then (((S.size c) + 1) + foldr (\a b -> a + b) 0 [(S.size c)^k | k <- [2..cap]])
                                                                               else ((S.size c) + 1))) qs
               in foldr (\x y -> x + y) 0 (srcs' ++ qs')

  
funGen :: ColoredNetwork -> MFunctionDisj -> String
funGen net func = let (fm,_) = funPredMap net
                      fiom = funIOMap net
                      tm = typeMap net
                      i = fm BM.!> func
                      (it,ot) = fiom IM.! (fm BM.!> func)
                      it' = tm BM.! it
                      ot' = tm BM.! ot
                      res = "function " ++ ot' ++ " func" ++ show i ++ "\n\tinput " ++ it' ++ " x;\n\n\treturn x;\nend"
                  in res

predGen :: ColoredNetwork -> MFunctionBool -> String
predGen net p = let (_,pm) = funPredMap net
                    fim = predIOMap net
                    tm = typeMap net
                    i = pm BM.!> p
                    it = fim IM.! (pm BM.!> p)
                    it' = tm BM.! it
                    res = "function bit pred" ++ show i ++ "\n\tinput " ++ it' ++ " x;\n\n\treturn x;\nend"
                in res

funPredGen :: ColoredNetwork -> String
funPredGen net = let (MetaIslands _ _ _ (fm,pm) _) = metaIsles net
                     fm' = map (\(_,x) -> x) $ BM.toList fm
                     pm' = map (\(_,x) -> x) $ BM.toList pm
                     res = (map (\x -> funGen net x)  fm') ++ (map (\x -> predGen net x) pm')
                     res' = foldr (\x y -> case y of "" -> x ++ "\n"; _ -> x ++ "\n" ++ y) "" res
                 in res'

