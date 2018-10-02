{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleInstances, CPP #-}

module Madl2smv.Converter
where

import Madl.MsgTypes
import Madl.Network
import Madl.MsgTypes()
import Madl.Invariants
import Madl.Deadlock.Formulas
import Madl.Deadlock.DeadlockDetection
import Madl.Islands
import Utils.Text
import Data.Maybe
import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Bimap as BM
import qualified Data.Text as T
import qualified Data.Sequence as Seq

data ChanType = Irdy | Trdy | Data


defaultColor :: Int
defaultColor = 0

--Gets all ComponentIDs of Sink components of the given network
getAllSinkIDs :: ColoredNetwork -> [ComponentID]
getAllSinkIDs net = let comps = getComponentIDs net
                        res = filter (\x -> case getComponent net x of (Sink _) -> True; _ -> False) comps
                     in res

--Gets all ComponentIDs of Queue components of the given network
getAllQueueIDs :: ColoredNetwork -> [ComponentID]
getAllQueueIDs net = let comps = getComponentIDs net
                         res = filter (\x -> case getComponent net x of (Queue _ _) -> True; _ -> False) comps
                     in res

--Gets all ComponentIDs of Merge components of the given network
getAllMergeIDs :: ColoredNetwork -> [ComponentID]
getAllMergeIDs net = let comps = getComponentIDs net
                         res = filter (\x -> case getComponent net x of (Merge _) -> True; _ -> False) comps
                     in res

--Takes a network and creates a Color-Int bimap based on packets which sources, queue, and sinks can work with.
typeMap :: ColoredNetwork -> BM.Bimap Color Int
typeMap net = let cids = getComponentIDs net
                  colors = L.nub $ L.concat $ map (\x -> compColors net x) cids
              in BM.fromList (L.zip colors [1..((L.length colors)+1)])

--Takes a network and creates a ComponentID-Int bimap
compMap :: ColoredNetwork -> BM.Bimap ComponentID Int
compMap net = let cids = getComponentIDs net
              in BM.fromList (L.zip cids [0..(L.length cids)])

chanMap :: ColoredNetwork -> BM.Bimap ChannelID Int
chanMap net = let cids = getChannelIDs net
              in BM.fromList (L.zip cids [0..(L.length cids)])

--Takes a network, a componentID and returns a set of colors that it can work with. If the component is neither source, nor queue, nor sink, then an empty list is returned.
compColors :: ColoredNetwork -> ComponentID -> [Color]
compColors net cid = case (getComponent net cid) of
                       (Queue _ _) -> let x = (getInChannels net cid)
                                          (ColorSet y) = getColorSet net (L.head x)
                                          z = S.toList y
                                      in z
                       (Source _ _) -> let x = (getOutChannels net cid)
                                           (ColorSet y) = getColorSet net (L.head x)
                                           z = S.toList y
                                       in z
                       (Sink _) -> let x = (getInChannels net cid)
                                       (ColorSet y) = getColorSet net (L.head x)
                                       z = S.toList y
                                   in z
                       _ -> []

--Takes a network, a componentID, and returns a list of (Color,Int) tuples, where Color is a color with which the component can work and Int is the identifier of the Color.
compType :: ColoredNetwork -> ComponentID -> [(Color, Int)]
compType net cid = let tm = typeMap net
                       c = compColors net cid
                   in filter (\(x,_) -> L.elem x c) (BM.toList tm)

--Takes a network, a ComponentID, a string addition and returns the variable name.
varName :: ColoredNetwork -> ComponentID -> String -> String
varName net cid r = let cm = compMap net
                    in case (getComponent net cid) of
                          (Source _ _) -> "src" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_" ++ r
                          (Sink _) -> "snk" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_" ++ r
                          (Merge _) -> "mrg" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_sel"
                          --(Queue _ _) -> "queue123"
                          _ -> error "varName: unexpected component type"

--Takes a network, a ComponentID, a channel type (irdy, trdy, or data) and makes a variable declaration
varDecl :: ColoredNetwork -> ComponentID -> ChanType -> String
varDecl net cid t = let c = compType net cid
                        c' = foldr (\a b -> case b of "" -> noslashes (show a); _ -> noslashes (show a) ++ "," ++ noslashes (show b)) "" (map (\(_,x) -> x) c)
                    in case t of
                          Irdy -> "\t" ++ varName net cid "irdy" ++ " : boolean;"
                          Trdy -> "\t" ++ varName net cid "trdy" ++ " : boolean;"
                          Data -> "\t" ++ varName net cid "data" ++ " : {" ++ c' ++ "};"

mVarName :: ColoredNetwork -> ComponentID -> String
mVarName net cid = let cm = compMap net
                   in case (getComponent net cid) of
                        (Merge _) -> "mrg" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_sel"
                        _ -> error "mVarName: unexpected component type"

mVarDecl :: ColoredNetwork -> ComponentID -> String
mVarDecl net cid = let c = compType net cid
                       c' = foldr (\a b -> case b of "" -> noslashes (show a); _ -> noslashes (show a) ++ "," ++ noslashes (show b)) "" (map (\(_,x) -> x) c)
                   in "\t" ++ mVarName net cid ++ " : {1,2};"

--Takes a network, a ComponentID and returns the state name for the given component
stateName :: ColoredNetwork -> ComponentID -> String
stateName net cid = let cm = compMap net
                    in case (getComponent net cid) of
                          (Source _ _) -> "src" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_state"
                          (Queue _ _) -> "q" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_state"
                          (Merge _) -> "mrg" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_state"
                          _ -> error "stateName: unexpected component type"

--Takes a network, a ComponentID and returns the state declaration for the given component
stateDecl :: ColoredNetwork -> ComponentID -> String
stateDecl net cid = let c = compType net cid
                        c' = "0," ++ (foldr (\a b -> case b of "" -> noslashes (show a); _ -> noslashes (show a) ++ "," ++ noslashes (show b)) "" (map (\(_,x) -> x) c))
                    in case (getComponent net cid) of
                          (Source _ _) -> "\t" ++ stateName net cid ++ " : {" ++ c' ++ "};"
                          (Queue _ n) -> "\t" ++ stateName net cid ++ " : array 0.." ++ noslashes (show (n-1)) ++ " of {" ++ c' ++ "};"
                          (Merge _) -> "\t" ++ stateName net cid ++ " : {0,1,2};"

--Takes a network, a ComponentID (has to be a queue) and returns a qInd variable name
qIndName :: ColoredNetwork -> ComponentID -> String
qIndName net cid = case (getComponent net cid) of
                      (Queue _ n) -> "q" ++ noslashes (show ((fromJust $ BM.lookup cid $ compMap net)::Int)) ++ "_ind"
                      _ -> error "qIndName: unexpected component type"

--Takes a network, a ComponentID (has to be a queue) and returns a qInd variable declaration
qInd :: ColoredNetwork -> ComponentID -> String
qInd net cid = case (getComponent net cid) of
                  (Queue _ n) -> "\tq" ++ noslashes (show ((fromJust $ BM.lookup cid $ compMap net)::Int)) ++ "_ind : 0.." ++ noslashes (show n) ++ ";"
                  _ -> error "qInd: unexpected component type"

--Takes a network, a ComponentID (has to be a queue) and returns the size of the given queue
getQueueSize :: ColoredNetwork -> ComponentID -> Int
getQueueSize net cid = case (getComponent net cid) of
                          (Queue _ n) -> n
                          _ -> error "getQueueSize: unexpected component type"

--Takes a string and removes some redundand symbols
noslashes :: String -> String
noslashes str = filter (\x -> x /= '\"') str

--Takes a network and makes an IVAR block
makeIVAR :: ColoredNetwork -> String
makeIVAR net = let srcs = getAllSourceIDs net
                   snks = getAllSinkIDs net
               in "IVAR\n" ++
                  foldr (\a b -> a ++ "\n" ++ b) "" ((map (\x -> varDecl net x Irdy ++ "\n" ++ varDecl net x Data) srcs) ++
                                                     (map (\x -> varDecl net x Trdy ++ "\n" ++ varDecl net x Data) snks))

makeBIVAR :: ColoredNetwork -> ChannelID -> String -> String
makeBIVAR net cid r = let chMap = chanMap net
                      in "\t" ++ r ++ " : boolean;"

--Takes a network and makes a VAR block
makeVAR :: ColoredNetwork -> String
makeVAR net = let srcs = getAllSourceIDs net
                  snks = getAllSinkIDs net
                  qs = getAllQueueIDs net
                  mrgs = getAllMergeIDs net
                  chans = getChannelIDs net
                  tm = typeMap net
                  chMap = chanMap net
              in "VAR\n" ++
                 foldr (\a b -> a ++ "\n" ++ b) "" ((map (\x -> varDecl net x Irdy) srcs) ++
                                                    --(map (\x -> varDecl net x Trdy) srcs) ++
                                                    (map (\x -> varDecl net x Data) srcs) ++
                                                    --(map (\x -> varDecl net x Irdy) snks) ++
                                                    (map (\x -> varDecl net x Trdy) snks) ++
                                                    (map (\x -> varDecl net x Data) snks) ++
                                                    (map (\x -> mVarDecl net x) mrgs) ++
                                                    (map (\x -> stateDecl net x) srcs) ++
                                                    (map (\x -> stateDecl net x) qs) ++
                                                    (map (\x -> stateDecl net x) mrgs) ++
                                                    (map (\x -> qInd net x) qs) ++
                                                    (L.concat $ map (\x -> let (ColorSet c) = getColorSet net x
                                                                               c' = S.toList c
                                                                           in map (\y -> makeBIVAR net x ("block" ++ show (chMap BM.! x) ++ "_" ++ show (tm BM.! y))) c') chans) ++
                                                    (L.concat $ map (\x -> let (ColorSet c) = getColorSet net x
                                                                               c' = S.toList c
                                                                           in map (\y -> makeBIVAR net x ("idle" ++ show (chMap BM.! x) ++ "_" ++ show (tm BM.! y))) c') chans))

--Takes a network and makes an INIT block
makeINIT :: ColoredNetwork -> String
makeINIT net = let srcs = getAllSourceIDs net
                   qs = getAllQueueIDs net
                   mrgs = getAllMergeIDs net
               in foldr (\a b -> a ++ "\n" ++ b) "" ((map (\x -> "\tinit(" ++ stateName net x ++ ") := 0;") srcs) ++
                                                     (map (\x -> "\tinit(" ++ qIndName net x ++ ") := 0;") qs) ++
                                                     (map (\x -> foldr (\a b -> a ++ "\n" ++ b) "" (map (\y -> "\tinit(" ++ stateName net x ++ "[" ++ noslashes (show y) ++ "]) := 0;") [0..((getQueueSize net x)-1)])) qs)
                                                      )

makeSMV :: ColoredNetwork -> String
makeSMV net = "MODULE main\n" ++
              makeVAR net ++ "\n" ++
              "ASSIGN\n" ++
              makeINIT net ++
              makeNEXT net ++
              makeInvar net ++
              makeInvarSpec net

showChannels :: ColoredNetwork -> String
showChannels net = (show $ chanMap net) ++ "\n" ++ (show net)

----------Later, I should move it to a separate file--------------
--Data structure for source states
data SourceState = Free | Next Int deriving Show
type QueueState = [Int]
data MergeState = Any | Committed Bool deriving Show


data Expr = S_Upd Args deriving Show
data Args = Arg Arg | Args Arg Args deriving Show
data Arg =    S SourceState
            | Q QueueState
            | M MergeState
            | Src_Upd BDArgs
            | Q_Upd BDArgs
            | Mrg_Upd BDArgs deriving Show
data BDArgs = BDArgs BArgs DArgs V deriving Show
data BArgs =    BArg BExpr
              | BArgs BExpr BArgs deriving Show
data DArgs =    DArg DExpr
              | DArgs DExpr DArgs deriving Show
data BExpr =    B Bool
              | Y String
--              | AssignB BExpr
              | Negation BExpr
              | NotEmpty V
              | NotFull V
              | Conj BExpr BExpr
              | Disj BExpr BExpr
              | Equals DExpr DExpr deriving Show
data DExpr =    D Int
              | X String
              | GetLast V
--              | AssignD DExpr
              | If BExpr DExpr DExpr deriving Show
data V = V String deriving Show

--join, fork, function, merge, queue, sink, source, switch
data T = Join_t | Fork_t | Function_t | Merge_t | Queue_t | Sink_t | Source_t | Switch_t deriving Eq

data MaDL = MaDL { x :: [ComponentID],
                   g :: [ChannelID],
                   c_g :: ChannelID -> [Int],
                   fun :: ComponentID -> Int -> Int,
                   inv :: ComponentID -> Int -> Int,
                   prd :: ComponentID -> Int -> Bool,
                   inp :: ComponentID -> [ChannelID],
                   outp :: ComponentID -> [ChannelID],
                   initiator :: ChannelID -> ComponentID,
                   target :: ChannelID -> ComponentID,
                   isFirst :: ChannelID -> Bool,
                   t :: ComponentID -> T,
                   qSize :: String -> Int,
                   intName :: ComponentID -> String -> String,
                   stName :: ComponentID -> String,
                   cMap :: BM.Bimap ComponentID Int,
                   chMap :: BM.Bimap ChannelID Int,
                   def :: Int } deriving Show

getX :: ColoredNetwork -> [ComponentID]
getX net = getComponentIDs net

getG :: ColoredNetwork -> [ChannelID]
getG net = getChannelIDs net

getCg :: ColoredNetwork -> ChannelID -> [Int]
getCg net chan = let (ColorSet x) = getColorSet net chan
                     x' = S.toList x
                     tm = typeMap net
                 in map (\z -> tm BM.! z) x'

getFun :: ColoredNetwork -> ComponentID -> Int -> Int
getFun net cid x = let tm = typeMap net
                   in case (getComponent net cid) of
                        (Function _ f _) -> let xin = tm BM.!> x
                                                xout = eval (makeVArguments [xin]) f
                                                xout' = tm BM.! xout
                                            in xout'
                        _ -> error "getFun: unexpected component type"

getInverse :: ColoredNetwork -> ComponentID -> Int -> Int
getInverse net cid x = let tm = typeMap net
                           o = L.head $ getOutChannels net cid
                           (ColorSet cols) = getColorSet net o
                           cols' = S.toList cols
                       in case (getComponent net cid) of
                            (Function _ f _) -> let dom = map (\z -> tm BM.! (eval (makeVArguments [z]) f)) cols'
                                                    xout = filter (\z -> z == x) dom
                                                in if (xout /= [])
                                                   then L.head xout
                                                   else error "getInverse: unable to compute the inverse"
                            _ -> error "getInverse: unexpected component type"

getPrd :: ColoredNetwork -> ComponentID -> Int -> Bool
getPrd net cid x = let tm = typeMap net
                       in case (getComponent net cid) of
                            (Switch _ p) -> let xin = tm BM.!> x
                                                xout = eval (makeVArguments [xin]) (L.head p)
                                            in xout

--not really needed
getInp :: ColoredNetwork -> ComponentID -> [ChannelID]
getInp net cid = getInChannels net cid

--not really needed
getOutp :: ColoredNetwork -> ComponentID -> [ChannelID]
getOutp net cid = getOutChannels net cid

--not really needed
getInit :: ColoredNetwork -> ChannelID -> ComponentID
getInit net cid = getInitiator net cid

--not really needed
getTarg :: ColoredNetwork -> ChannelID -> ComponentID
getTarg net cid = getTarget net cid

getIsFirst :: ColoredNetwork -> ChannelID -> Bool
getIsFirst net cid = case (getComponent net (getTarget net cid)) of
                        (Merge _) -> let ins = getInChannels net (getTarget net cid)
                                     in cid == L.head ins
                        _ -> error "getIsFirst: unexpected component type"

getT :: ColoredNetwork -> ComponentID -> T
getT net cid = case (getComponent net cid) of
                  (ControlJoin _) -> Join_t
                  (Fork _) -> Fork_t
                  (Function _ _ _) -> Function_t
                  (Merge _) -> Merge_t
                  (Queue _ _) -> Queue_t
                  (Sink _) -> Sink_t
                  (Source _ _) -> Source_t
                  (Switch _ _) -> Switch_t
                  _ -> error "getT: unexpected component type"

getQSize :: ColoredNetwork -> String -> Int
getQSize net name = let cm = compMap net
                        i = getID name
                        cid = cm BM.!> i
                    in getQueueSize net cid

getMaDL :: ColoredNetwork -> MaDL
getMaDL net = MaDL { x = getX net,
                     g = getG net,
                     c_g = getCg net,
                     fun = getFun net,
                     inv = getInverse net,
                     prd = getPrd net,
                     inp = getInp net,
                     outp = getOutp net,
                     initiator = getInitiator net,
                     target = getTarget net,
                     isFirst = getIsFirst net,
                     t = getT net,
                     qSize = getQSize net,
                     intName = varName net,
                     stName = stateName net,
                     cMap = compMap net,
                     chMap = chanMap net,
                     def = defaultColor
                    }

instance Show T where
  show Join_t = "Join"
  show Fork_t = "Fork"
  show Function_t = "Function"
  show Merge_t = "Merge"
  show Queue_t = "Queue"
  show Sink_t = "Sink"
  show Source_t = "Source"
  show Switch_t = "Switch"

instance Show (ChannelID -> [Int]) where
  show _ = "stub1"

instance Show (ChannelID -> ComponentID) where
  show _ = "stub2"

instance Show (ChannelID -> Bool) where
  show _ = "stub3"

instance Show (ComponentID -> Int -> Int) where
  show _ = "stub4"

instance Show (ComponentID -> Int -> Bool) where
  show _ = "stub5"

instance Show (ComponentID -> [ChannelID]) where
  show _ = "stub6"

instance Show (ComponentID -> T) where
  show _ = "stub7"

instance Show (ComponentID -> String) where
  show _ = "stub8"

instance Show (ComponentID -> String -> String) where
  show _ = "stub9"

instance Show (String -> Int) where
  show _ = "stub10"


mkExpr :: MaDL -> Expr
mkExpr madl = S_Upd (mkArgs madl (filter (\y -> ((t madl) y == Source_t) || ((t madl) y == Queue_t) || (((t madl) y == Merge_t))) (x madl)))

mkArgs :: MaDL -> [ComponentID] -> Args
mkArgs madl xs
  | L.length xs > 1 = Args (mkArg madl (L.head xs)) (mkArgs madl (L.tail xs))--Arg (S Free)
  | otherwise = Arg (mkArg madl (L.head xs))

mkArg :: MaDL -> ComponentID -> Arg
mkArg madl x = case ((t madl) x) of
                  Source_t -> Src_Upd (mkSrcArgs madl x)
                  Queue_t -> Q_Upd (mkQArgs madl x)
                  Merge_t -> Mrg_Upd (mkMrgArgs madl x)
                  _ -> error "mkArg: unexpected component type"

mkSrcArgs :: MaDL -> ComponentID -> BDArgs
mkSrcArgs madl x = BDArgs (BArgs (mkBexprOIrdy madl x (L.head ((outp madl) x))) (BArg (mkBexprOTrdy madl x (L.head ((outp madl) x))))) (DArg (mkDexprO madl x (L.head ((outp madl) x)))) (V $ (stName madl) x)

mkQArgs :: MaDL -> ComponentID -> BDArgs
mkQArgs madl x = BDArgs (BArgs (mkBexprIIrdy madl x (L.head ((inp madl) x))) (BArgs (mkBexprITrdy madl x (L.head ((inp madl) x))) (BArgs (mkBexprOIrdy madl x (L.head ((outp madl) x))) (BArg (mkBexprOTrdy madl x (L.head ((outp madl) x))))))) (DArgs (mkDexprI madl x (L.head ((inp madl) x))) (DArg (mkDexprO madl x (L.head ((outp madl) x))))) (V $ (stName madl) x)

mkMrgArgs :: MaDL -> ComponentID -> BDArgs
mkMrgArgs madl x = BDArgs (BArgs (mkBexprIIrdy madl x (((inp madl) x) !! 0)) (BArgs (mkBexprITrdy madl x (((inp madl) x) !! 0)) (BArgs (mkBexprIIrdy madl x (((inp madl) x) !! 1)) (BArgs (mkBexprITrdy madl x (((inp madl) x) !! 1)) (BArgs (mkBexprOIrdy madl x (L.head ((outp madl) x))) (BArg (mkBexprOTrdy madl x (L.head ((outp madl) x))))))))) (DArg (D 0)) (V $ (stName madl) x)

mkBexprIIrdy :: MaDL -> ComponentID -> ChannelID -> BExpr
mkBexprIIrdy madl cid chan = case ((t madl) cid) of
                                Source_t -> error "mkBexprIIrdy: unexpected component type"
                                _ -> mkBexprOIrdy madl ((initiator madl) chan) chan

mkBexprOIrdy :: MaDL -> ComponentID -> ChannelID -> BExpr
mkBexprOIrdy madl cid chan = case ((t madl) cid) of
                                Join_t -> Conj (mkBexprIIrdy madl cid (((inp madl) cid) !! 0)) (mkBexprIIrdy madl cid (((inp madl) cid) !! 1))
                                Fork_t -> Conj (mkBexprIIrdy madl cid (L.head ((inp madl) cid))) (mkBexprOTrdy madl cid (L.head $ filter (\x -> x /= chan) ((outp madl) cid)))
                                Function_t -> mkBexprIIrdy madl cid (L.head ((inp madl) cid))
                                Merge_t -> Disj (mkBexprIIrdy madl cid (((inp madl) cid) !! 0)) (mkBexprIIrdy madl cid (((inp madl) cid) !! 1))
                                Queue_t -> NotEmpty (V $ (stName madl) cid)
                                Sink_t -> error "mkBexprOIrdy: unexpected component type"
                                Source_t -> Y ((intName madl) cid "irdy")
                                Switch_t -> if (chan /= (((outp madl) cid) !! 1))
                                            then Conj (mkBexprIIrdy madl cid (L.head ((inp madl) cid))) (mkPred madl cid ((c_g madl) chan))
                                            else Conj (mkBexprIIrdy madl cid (L.head ((inp madl) cid))) (mkPred madl cid ((c_g madl) chan))

mkBexprITrdy :: MaDL -> ComponentID -> ChannelID -> BExpr
mkBexprITrdy madl cid chan = case ((t madl) cid) of
                                Fork_t -> Conj (mkBexprOTrdy madl cid (((outp madl) cid) !! 0)) (mkBexprOTrdy madl cid (((outp madl) cid) !! 1))
                                Function_t -> mkBexprOTrdy madl cid (((outp madl) cid) !! 0)
                                Join_t -> Conj (mkBexprIIrdy madl cid (L.head $ filter (\x -> x /= chan) ((inp madl) cid))) (mkBexprOTrdy madl cid (L.head ((outp madl) cid)))
                                Merge_t -> if (chan /= (((inp madl) cid) !! 1))
                                           then Conj (Conj (Equals (X ((intName madl) cid "")) (D 1)) (mkBexprOTrdy madl cid (L.head ((outp madl) cid)))) (mkBexprIIrdy madl cid (((inp madl) cid) !! 1))
                                           else Conj (Conj (Equals (X ((intName madl) cid "")) (D 2)) (mkBexprOTrdy madl cid (L.head ((outp madl) cid)))) (mkBexprIIrdy madl cid (((inp madl) cid) !! 0))
                                Queue_t -> NotFull (V $ (stName madl) cid)
                                Sink_t -> Conj (Y ((intName madl) cid "trdy")) (Equals (mkDexprO madl ((initiator madl) chan) chan) (mkDexprI madl cid chan))
                                Switch_t -> Disj (Conj (mkBexprOIrdy madl cid (((outp madl) cid) !! 0)) (mkBexprOTrdy madl cid (((outp madl) cid) !! 0))) (Conj (mkBexprOIrdy madl cid (((outp madl) cid) !! 1)) (mkBexprOTrdy madl cid (((outp madl) cid) !! 1)))
                                Source_t -> error "mkBexprITrdy: unexpected component type"

mkBexprOTrdy :: MaDL -> ComponentID -> ChannelID -> BExpr
mkBexprOTrdy madl cid chan = case ((t madl) cid) of
                                Sink_t -> error "mkBexprOTrdy: unexpected component type"
                                _ -> mkBexprITrdy madl ((target madl) chan) chan

mkDexprI :: MaDL -> ComponentID -> ChannelID -> DExpr
mkDexprI madl cid chan = case ((t madl) cid) of
                            Sink_t -> X ((intName madl) cid "data")
                            _ -> mkDexprO madl ((initiator madl) chan) chan

mkDexprO :: MaDL -> ComponentID -> ChannelID -> DExpr
mkDexprO madl cid chan = case ((t madl) cid) of
                            Source_t -> X ((intName madl) cid "data")
                            Sink_t -> error "mkDexprO: unexpected component type"
                            Queue_t -> GetLast (V $ (stName madl) cid)
                            Function_t -> mkFun madl cid ((c_g madl) chan)
                            _ -> mkDexprI madl cid (L.head ((inp madl) cid))


--prd :: ComponentID -> Int -> Bool
mkPred :: MaDL -> ComponentID -> [Int] -> BExpr
mkPred madl cid [] = B False
mkPred madl cid (x:[]) = Equals (mkDexprI madl cid (L.head ((inp madl) cid))) (D x)
mkPred madl cid (x:xs) = Disj (Equals (mkDexprI madl cid (L.head ((inp madl) cid))) (D x)) (mkPred madl cid xs)

mkPred' :: MaDL -> ComponentID -> DExpr -> [Int] -> BExpr
mkPred' madl cid expr [] = B False
mkPred' madl cid expr (x:[]) = Equals expr (D x)
mkPred' madl cid expr (x:xs) = Disj (Equals expr (D x)) (mkPred' madl cid expr xs)

mkSrcIdle :: DExpr -> [Int] -> BExpr
mkSrcIdle expr [] = B True
mkSrcIdle expr (x:[]) = Negation (Equals expr (D x))
mkSrcIdle expr (x:xs) = Conj (Negation (Equals expr (D x))) (mkSrcIdle expr xs)

mkSnkBlock :: DExpr -> [Int] -> BExpr
mkSnkBlock expr [] = B True
mkSnkBlock expr (x:[]) = Negation (Equals expr (D x))
mkSnkBlock expr (x:xs) = Conj (Negation (Equals expr (D x))) (mkSnkBlock expr xs)

--fun :: ComponentID -> Int -> Int
mkFun :: MaDL -> ComponentID -> [Int] -> DExpr
mkFun madl cid cols
  | L.length cols > 2 = If (Equals (mkDexprI madl cid (L.head ((inp madl) cid))) (D $ L.head cols))
                           (D ((fun madl) cid (L.head cols)))
                           (mkFun madl cid (L.tail cols))
  | L.length cols == 2 = If (Equals (mkDexprI madl cid (L.head ((inp madl) cid))) (D $ L.head cols))
                            (D ((fun madl) cid (L.head cols)))
                            (D ((fun madl) cid (L.head $ L.tail cols)))
  | L.length cols == 1 = (D ((fun madl) cid (L.head cols)))
  | otherwise = D 0

mkFun' :: MaDL -> ComponentID -> DExpr -> [Int] -> DExpr
mkFun' madl cid expr cols
  | L.length cols > 2 = If (Equals expr (D $ L.head cols))
                           (D ((fun madl) cid (L.head cols)))
                           (mkFun' madl cid expr (L.tail cols))
  | L.length cols == 2 = If (Equals expr (D $ L.head cols))
                            (D ((fun madl) cid (L.head cols)))
                            (D ((fun madl) cid (L.head $ L.tail cols)))
  | L.length cols == 1 = (D ((fun madl) cid (L.head cols)))
  | otherwise = D 0

mkInverse :: MaDL -> ComponentID -> DExpr -> [Int] -> DExpr
mkInverse madl cid expr cols
  | L.length cols > 2 = If (Equals expr (D $ L.head cols))
                           (D ((inv madl) cid (L.head cols)))
                           (mkInverse madl cid expr (L.tail cols))
  | L.length cols == 2 = If (Equals expr (D $ L.head cols))
                            (D ((inv madl) cid (L.head cols)))
                            (D ((inv madl) cid (L.head $ L.tail cols)))
  | L.length cols == 1 = (D ((inv madl) cid (L.head cols)))
  | otherwise = D 0

getCompName :: Arg -> String
getCompName (Src_Upd (BDArgs _ _ (V s))) = s
getCompName (Q_Upd (BDArgs _ _ (V s))) = s
getCompName (Mrg_Upd (BDArgs _ _ (V s))) = s
getCompName _ = ""

getAllNames :: Expr -> [String]
getAllNames (S_Upd (Arg arg)) = if (getCompName arg /= "")
                              then [(getCompName arg)]
                              else []
getAllNames (S_Upd (Args arg args)) = if (getCompName arg /= "")
                                      then ((getCompName arg):(getAllNames (S_Upd args)))
                                      else (getAllNames (S_Upd args))

getType :: String -> T
getType ('s':_) = Source_t
getType ('q':_) = Queue_t
getType ('m':_) = Merge_t
getType _ = error "getType: unexpected input"

getPref :: String -> String
getPref [] = []
getPref ('_':xs) = []
getPref (x:xs) = (x:getPref xs)

getID :: String -> Int
getID name = let digits = filter (\x -> C.isDigit x) name
             in case L.length digits of
                  0 -> error "getID: wrong input"
                  _ -> read digits

{-
((src_state = 0) & ((src_irdy & src_trdy) | !src_irdy)) | ((src_state = src_data) & src_irdy & src_trdy) : 0; --(state = 0 & ()) ()
((src_state = 0) | (src_state = src_data)) & src_irdy & !src_trdy : src_data;
TRUE : src_state;
-}
makeSrcNEXT :: MaDL -> String -> String
makeSrcNEXT madl sname = let expr = mkExpr madl
                             arg = nameToArg expr sname
                             oirdy = printBExpr madl $ getSrcOIrdy arg
                             otrdy = printBExpr madl $ getSrcOTrdy arg
                             odata = printDExpr madl $ getSrcOData arg
                         in "\tnext(" ++ sname ++ ") := case\n" ++
                            "\t\t\t\t((" ++ sname ++ " = 0) & ((" ++ oirdy ++ " & " ++ otrdy ++ ") | !" ++ oirdy ++ ")) | ((" ++ sname ++ " = " ++ odata ++ ") & " ++ oirdy ++ " & " ++ otrdy ++ ") : 0;\n" ++
                            "\t\t\t\t(" ++ sname ++ " = 0 | (" ++ sname ++ " = " ++ odata ++ ")) & " ++ oirdy ++ " & !" ++ otrdy ++ " : " ++ odata ++ ";\n"  ++
                            "\t\t\t\tTRUE : " ++ sname ++ ";\n" ++
                            "\t\t\tesac;"


makeQNEXT :: MaDL -> String -> String
makeQNEXT madl sname = let expr = mkExpr madl
                           arg = nameToArg expr sname
                           iirdy = printBExpr madl $ getQIIrdy arg
                           itrdy = printBExpr madl $ getQITrdy arg
                           oirdy = printBExpr madl $ getQOIrdy arg
                           otrdy = printBExpr madl $ getQOTrdy arg
                           idata = printDExpr madl $ getQIData arg
                           odata = printDExpr madl $ getQOData arg
                           qsize = ((qSize madl) sname)
                           cells = (map (\x -> makeQCell madl sname x) [0..qsize - 1]) ++ [(makeQInd madl sname)]
                       in foldr (\z z' -> case z' of "" -> z; _ -> z ++ "\n" ++ z') "" cells


makeQInd :: MaDL -> String -> String
makeQInd madl sname = let expr = mkExpr madl
                          arg = nameToArg expr sname
                          iirdy = printBExpr madl $ getQIIrdy arg
                          itrdy = printBExpr madl $ getQITrdy arg
                          oirdy = printBExpr madl $ getQOIrdy arg
                          otrdy = printBExpr madl $ getQOTrdy arg
                          idata = printDExpr madl $ getQIData arg
                          odata = printDExpr madl $ getQOData arg
                      in "\tnext(q" ++ show (getID sname) ++ "_ind) := case\n" ++
                         "\t\t\t\t(" ++ iirdy ++ " & " ++ itrdy ++ ") & !(" ++ oirdy ++ " & " ++ otrdy ++ ") : q" ++ show (getID sname) ++ "_ind + 1;\n" ++
                         "\t\t\t\t!(" ++ iirdy ++ " & " ++ itrdy ++  ") & (" ++ oirdy ++ " & " ++ otrdy ++ ") : q" ++ show (getID sname) ++ "_ind - 1;\n" ++
                         "\t\t\t\tTRUE : q" ++ show (getID sname) ++ "_ind;\n" ++
                         "\t\t\tesac;"


makeQCell :: MaDL -> String -> Int -> String
makeQCell madl sname cell = let expr = mkExpr madl
                                arg = nameToArg expr sname
                                iirdy = printBExpr madl $ getQIIrdy arg
                                itrdy = printBExpr madl $ getQITrdy arg
                                oirdy = printBExpr madl $ getQOIrdy arg
                                otrdy = printBExpr madl $ getQOTrdy arg
                                idata = printDExpr madl $ getQIData arg
                                odata = printDExpr madl $ getQOData arg
                            in case cell of
                                  0 -> "\tnext(" ++ sname ++ "[0]) := case\n" ++
                                       "\t\t\t\t(" ++ iirdy ++ " & " ++ itrdy ++ ") & !(" ++ oirdy ++ " & " ++ otrdy ++ ") : " ++ idata ++ ";\n" ++
                                       "\t\t\t\t!(" ++ iirdy ++ " & " ++ itrdy ++ ") & (" ++ oirdy ++ " & " ++ otrdy ++ ") & (q" ++ show (getID sname) ++ "_ind" ++ " = 1) : 0;\n" ++
                                       "\t\t\t\t(" ++ iirdy ++ " & " ++ itrdy ++ ") & (" ++ oirdy ++ " & " ++ otrdy ++ ") : " ++ idata ++ ";\n" ++
                                       "\t\t\t\tTRUE: " ++ sname ++ "[0];\n" ++
                                       "\t\t\tesac;\n"
                                  _ -> "\tnext(" ++ sname ++ "[" ++ show cell ++ "]) := case\n" ++
                                       "\t\t\t\t(" ++ iirdy ++ " & " ++ itrdy ++ ") & !(" ++ oirdy ++ " & " ++ otrdy ++ ") : " ++ sname ++ "[" ++ show (cell - 1) ++ "]" ++ ";\n" ++
                                       "\t\t\t\t!(" ++ iirdy ++ " & " ++ itrdy ++ ") & (" ++ oirdy ++ " & " ++ otrdy ++ ") & (" ++ show cell ++ " = " ++ show (((qSize madl) sname) - 1) ++ ") : 0;\n" ++
                                       "\t\t\t\t(" ++ iirdy ++ " & " ++ itrdy ++ ") & (" ++ oirdy ++ " & " ++ otrdy ++ ") : (" ++ show cell ++ " <= q" ++ show (getID sname) ++ "_ind - 1)? " ++ sname ++ "[" ++ show (cell - 1) ++ "] : " ++ sname ++ "[" ++ show cell ++ "]" ++ ";\n" ++
                                       "\t\t\t\tTRUE: " ++ sname ++ "[" ++ show cell ++ "];\n" ++
                                       "\t\t\tesac;\n"

makeMrgNEXT :: MaDL -> String -> String
makeMrgNEXT madl sname = let expr = mkExpr madl
                             arg = nameToArg expr sname
                             i0irdy = printBExpr madl $ getMrgI0Irdy arg
                             i0trdy = printBExpr madl $ getMrgI0Trdy arg
                             i1irdy = printBExpr madl $ getMrgI1Irdy arg
                             i1trdy = printBExpr madl $ getMrgI1Trdy arg
                             oirdy = printBExpr madl $ getMrgOIrdy arg
                             otrdy = printBExpr madl $ getMrgOTrdy arg
                             mname = "mrg" ++ show (getID sname) ++ "_sel"
                         in "\tnext(" ++ sname ++ ") := case\n" ++
                            --((state = 0) | (state = sel)) & ((i0i & i0t & !sel) | (i1i & i1t & sel)) -> 0
                            "\t\t\t\t((" ++ sname ++ " = 0) | (" ++ sname ++ " = " ++ mname ++ ")) & ((" ++ i0irdy ++ " & " ++ i0trdy ++ " & (" ++ mname ++ " = 1)) | (" ++ i1irdy ++ " & " ++ i1trdy ++ " & (" ++ mname ++ " = 2))) : 0;\n" ++
                            --((state = 0) | (state = sel)) & (!(i0i & i01) & !sel) -> 1
                            "\t\t\t\t((" ++ sname ++ " = 0) | (" ++ sname ++ " = " ++ mname ++ ")) & (!(" ++ i0irdy ++ " & " ++ i1irdy ++ ") & (" ++ mname ++ " = 1)) : 1;\n" ++
                            --((state = 0) | (state = sel)) & (!(i0i & i01) & sel) -> 2
                            "\t\t\t\t((" ++ sname ++ " = 0) | (" ++ sname ++ " = " ++ mname ++ ")) & (!(" ++ i0irdy ++ " & " ++ i1irdy ++ ") & (" ++ mname ++ " = 2)) : 2;\n" ++
                            "\t\t\t\tTRUE: " ++ sname ++ ";\n" ++
                            "\t\t\tesac;\n"
{-
mkBlock :: MaDL -> ChannelID -> DExpr -> BExpr
mkBlock madl cid expr = let targ = (target madl) cid
                            comptype = (t madl) targ
                            ind = (cMap madl) BM.! targ
                        in case comptype of
                              Fork_t -> Disj (mkBlock madl (((outp madl) targ) !! 0) expr) (mkBlock madl (((outp madl) targ) !! 1) expr)
                              Function_t -> mkBlock madl (((outp madl) targ) !! 0) (mkFun' madl targ expr ((c_g madl) cid))
                              Join_t -> if (cid /= (((inp madl) targ) !! 0))
                                        then Disj (mkIdle madl (((inp madl) targ) !! 1) expr) (mkBlock madl (((outp madl) targ) !! 0) expr)
                                        else Disj (mkIdle madl (((inp madl) targ) !! 0) expr) (Conj (mkBexprIIrdy madl targ (((inp madl) targ) !! 0)) (mkBlock madl (((outp madl) targ) !! 0) (mkDexprI madl targ (((inp madl) targ) !! 0))))
                              Merge_t -> let j = if (cid == (L.head ((inp madl) targ)))
                                                 then 1
                                                 else 2
                                         in Disj
                                            (Conj (Equals (X ("mrg" ++ show ind ++ "_sel")) (D j)) (mkBlock madl (((outp madl) targ) !! 0) expr))
                                            (Conj (Negation (Equals (X ("mrg" ++ show ind ++ "_sel")) (D j))) (Conj (mkBexprIIrdy madl targ (((inp madl) targ) !! 1)) (mkBlock madl (((inp madl) targ) !! 0) (mkDexprI madl targ (((inp madl) targ) !! (j-1))))))
                              Queue_t -> Conj (mkBlock madl (((outp madl) targ) !! 0) (X ("q" ++ show ind ++ "state[" ++ show ((qSize madl) ("q" ++ show ind ++ "_state")) ++ "]"))) (Equals (X ("q" ++ show ind ++ "_ind")) (D ((qSize madl) ("q" ++ show ind ++ "_state"))))
                              Sink_t -> B False
                              Source_t -> error "mkBlock: sources do not have block equations"
                              Switch_t -> Disj (Conj (mkPred' madl targ expr ((c_g madl) cid)) (mkBlock madl (((outp madl) targ) !! 0) expr)) (Conj (mkPred' madl targ expr ((c_g madl) cid)) (mkBlock madl (((outp madl) targ) !! 1) expr))
-}

getInvarName :: String -> String
getInvarName [] = []
getInvarName (' ':xs) = []
getInvarName (x:xs) = (x:getInvarName xs)

invarExists :: String -> [String] -> Bool
invarExists n ivs = let n' = getInvarName n in elem True (map (\x -> n' == getInvarName x) ivs)


mkBlock :: MaDL -> ChannelID -> DExpr -> [String] -> [String]
mkBlock madl chan expr r = let targ = (target madl) chan
                               comptype = (t madl) targ
                               compind = (cMap madl) BM.! targ
                               chanind = (chMap madl) BM.! chan
                               chancol = printDExpr madl expr
                               invar = "block" ++ show chanind ++ "_" ++ chancol
                               r' = (invar:r)
                           in if (L.elem invar r)
                              then []
                              else case comptype of
                                      Fork_t -> let o1 = ((outp madl) targ) !! 0
                                                    o2 = ((outp madl) targ) !! 1
                                                    chanind1 = (chMap madl) BM.! o1
                                                    chanind2 = (chMap madl) BM.! o2
                                                in ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = (block" ++ show chanind1 ++  "_" ++ chancol ++ " | block" ++ show chanind2 ++  "_" ++ chancol ++ ")"] ++
                                                   (mkBlock madl o1 expr r') ++
                                                   (mkBlock madl o2 expr r')
                                      Function_t -> let o1 = ((outp madl) targ) !! 0
                                                        chanind1 = (chMap madl) BM.! o1
                                                        icol = case expr of
                                                                  (D n) -> n
                                                                  _ -> error "mkBlock: unable to extract an integer from the DExpr"
                                                        ocol = (fun madl) targ icol
                                                    in ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = block" ++ show chanind1 ++ "_" ++ show ocol] ++
                                                       (mkBlock madl o1 (D ocol) r')
                                      Join_t -> let i1 = ((inp madl) targ) !! 0
                                                    i2 = ((inp madl) targ) !! 1
                                                    chanind1 = (chMap madl) BM.! i1
                                                    chanind2 = (chMap madl) BM.! i2
                                                    chanindo = (chMap madl) BM.! (((outp madl) targ) !! 0)
                                                    i1col = (c_g madl) i1
                                                    i2col = (c_g madl) i2
                                                    expr' = case expr of
                                                              (D n) -> n
                                                              _ -> error ("mkBlock: 1 unable to extract an integer from the DExpr" ++ (printDExpr madl expr))
                                                    i1res = foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] (map (\x -> "(idle" ++ show chanind2 ++ "_" ++ show x ++ " | block" ++ show chanindo ++ "_" ++ show expr' ++ ")") i2col)
                                                    i1res' = ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = " ++ i1res] ++
                                                             (L.concat $ map (\x -> (mkIdle madl i2 (D x) r')) i2col) ++
                                                             (mkBlock madl (((outp madl) targ) !! 0) expr r')
                                                    i2res = foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] (map (\x -> "(idle" ++ show chanind1 ++ "_" ++ show x ++ " | (" ++ (printBExpr madl (mkBexprIIrdy madl targ (((inp madl) targ) !! 0))) ++ " & block" ++ show chanindo ++ "_" ++ show x ++ "))") i1col)
                                                    i2res' = ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = " ++ i2res] ++
                                                             (L.concat $ map (\x -> (mkIdle madl i1 (D x) r')) i1col) ++
                                                             (L.concat $ map (\x -> (mkBlock madl (((outp madl) targ) !! 0) (D x) r')) i1col)
                                                in if (chan == i1)
                                                   then i1res'
                                                   else i2res'
                                      Merge_t -> let (j::Int) = if (chan == (L.head ((inp madl) targ)))
                                                                then 1
                                                                else 2
                                                     (k::Int) = if (j == 1)
                                                                then 2
                                                                else 1
                                                     i1 = ((inp madl) targ) !! 0
                                                     i2 = ((inp madl) targ) !! 1
                                                     o = ((outp madl) targ) !! 0
                                                     chanind1 = (chMap madl) BM.! i1
                                                     chanind2 = (chMap madl) BM.! i2
                                                     chanindo = (chMap madl) BM.! o
                                                     expr' = case expr of
                                                               (D n) -> n
                                                               _ -> error "mkBlock: 2 unable to extract an integer from the DExpr"
                                                     res1 = "INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = (mrg" ++ show compind ++ "_sel = " ++ show j ++ " & block" ++ show chanindo ++ "_" ++ show expr' ++ ")"
                                                     ikcols = (c_g madl) (((inp madl) targ) !! (k - 1))
                                                     res2 = foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] (map (\x -> "(mrg" ++ show compind ++ "_sel != " ++ show j ++ " & " ++ (printBExpr madl (mkBexprIIrdy madl targ (((inp madl) targ) !! (k - 1)))) ++ " & " ++ "block" ++ show chanindo ++ "_" ++ show x ++")") ikcols)
                                                     res3 = if (res1 /= "" && res2 /= "")
                                                            then res1 ++ " | " ++ res2
                                                            else res1 ++ res2
                                                     res = [res3] ++
                                                           (mkBlock madl o expr r') ++
                                                           (L.concat $ map (\x -> (mkBlock madl o (D x) r')) ikcols)
                                                 in res
                                      Queue_t -> let i = ((inp madl) targ) !! 0
                                                     o = ((outp madl) targ) !! 0
                                                     chanindo = (chMap madl) BM.! o
                                                     ocol = (c_g madl) o
                                                     qs = (qSize madl) ("q" ++ show compind ++ "_state")
                                                     qlast = "q" ++ show compind ++ "_state[" ++ show (qs - 1) ++ "]"
                                                     res = map (\x -> ["(block" ++ show chanindo ++ "_" ++
                                                                       show x ++ " & (" ++
                                                                       qlast ++ " = " ++
                                                                       show x ++ ") & (q" ++
                                                                       show compind ++
                                                                       "_ind = " ++
                                                                       show qs ++ "))"]) ocol -- ++ (mkBlock madl o (D x) r')) ocol
                                                     res' = ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = " ++ (foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] (L.concat res))]
                                                     res'' = L.concat (map (\x -> mkBlock madl o (D x) r') ocol)
                                                 in res' ++ res''
                                      Sink_t -> ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = FALSE"]
                                      Source_t -> error "mkBlock: sources do not have block equations"
                                      Switch_t -> let o1 = ((outp madl) targ) !! 0
                                                      o2 = ((outp madl) targ) !! 1
                                                      chanindo1 = (chMap madl) BM.! o1
                                                      chanindo2 = (chMap madl) BM.! o2
                                                      o1cols = (c_g madl) o1
                                                      o2cols = (c_g madl) o2
                                                      icol = case expr of
                                                                (D n) -> n
                                                                _ -> error "mkBlock: unable to extract an integer from the DExpr"
                                                      condl = L.elem icol o1cols
                                                      condr = L.elem icol o2cols
                                                      resl = if condl
                                                             then "(" ++ printBExpr madl (mkPred' madl targ expr ((c_g madl) chan)) ++ " & block" ++ show chanindo1 ++ "_" ++ show icol ++ ")"
                                                             else ""
                                                      resr = if condr
                                                             then "(" ++ printBExpr madl (mkPred' madl targ expr ((c_g madl) chan)) ++ " & block" ++ show chanindo2 ++ "_" ++ show icol ++ ")"
                                                             else ""
                                                      res = if (resl /= "") && (resr /= "")
                                                            then "(" ++ resl ++ " | " ++ resr ++ ")"
                                                            else resl ++ resr
                                                      block1 = if condl
                                                               then (mkBlock madl o1 (D icol) r')
                                                               else []
                                                      block2 = if condr
                                                               then (mkBlock madl o2 (D icol) r')
                                                               else []
                                                  in ["INVAR block" ++ show chanind ++ "_" ++ chancol ++ " = " ++ res] ++
                                                     block1 ++
                                                     block2



mkIdle :: MaDL -> ChannelID -> DExpr -> [String] -> [String]
mkIdle madl chan expr r = let inttr = (initiator madl) chan
                              comptype = (t madl) inttr
                              compind = (cMap madl) BM.! inttr
                              chanind = (chMap madl) BM.! chan
                              chancol = printDExpr madl expr
                              invar = "idle" ++ show chanind ++ "_" ++ chancol
                              r' = (invar:r)
                          in if L.elem invar r
                             then []
                             else case comptype of
                                    Fork_t -> let o = L.head $ filter (\x -> x /= chan) ((outp madl) inttr)
                                                  i = ((inp madl) inttr) !! 0
                                                  chanindo = (chMap madl) BM.! o
                                                  chanindi = (chMap madl) BM.! i
                                              in ["INVAR idle" ++ show chanind ++ "_" ++ chancol ++ " = (idle" ++ show chanindi ++ "_" ++ chancol ++ " | block" ++ show chanindo ++ "_" ++ chancol ++ ")"] ++
                                                 (mkIdle madl i expr r') ++
                                                 (mkBlock madl o expr r')
                                    Function_t -> let i = ((inp madl) inttr) !! 0
                                                      chanindi = (chMap madl) BM.! i
                                                      ocol = case expr of
                                                                (D n) -> n
                                                                _ -> error "mkIdle: unable to extract an integer from the DExpr"
                                                      icol = (inv madl) inttr ocol
                                                  in ["INVAR idle" ++ show chanind ++ "_" ++ show ocol ++ " = idle" ++ show chanindi ++ "_" ++ show icol] ++
                                                     (mkIdle madl i (mkInverse madl inttr expr ((c_g madl) chan)) r')
                                    Join_t -> let i1 = ((inp madl) inttr) !! 0
                                                  i2 = ((inp madl) inttr) !! 1
                                                  chanindi1 = (chMap madl) BM.! i1
                                                  chanindi2 = (chMap madl) BM.! i2
                                                  i2col = (c_g madl) i2
                                                  ocol = case expr of
                                                            (D n) -> n
                                                            _ -> error "mkIdle: unable to extract an integer out of a DExpr"
                                                  res = (foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] (map (\x -> "idle" ++ show chanindi2 ++ "_" ++ show x) i2col)) ++ " | idle" ++ show chanindi1 ++ "_" ++ show ocol
                                                  res' = ["INVAR idle" ++ show chanind ++ "_" ++ chancol ++ " = " ++ res] ++
                                                         (L.concat $ map (\x -> mkIdle madl i2 (D x) r') i2col) ++
                                                         (mkIdle madl i1 expr r')
                                              in res'
                                    --FIX THIS
                                    Merge_t -> let i1 = ((inp madl) inttr) !! 0
                                                   i2 = ((inp madl) inttr) !! 1
                                                   chanindi1 = (chMap madl) BM.! i1
                                                   chanindi2 = (chMap madl) BM.! i2
                                                   i1col = (c_g madl) i1
                                                   i2col = (c_g madl) i2
                                                   expr' = case expr of
                                                             (D n) -> n
                                                             _ -> error "mkIdle: unable to extract an integer out of a DExpr"
                                                   --res1 = "(" ++ (foldr (\a b -> case b of [] -> a; _ -> a ++ " & " ++ b) [] ((map (\x -> "idle" ++ show chanindi1 ++ "_" ++ show x) [expr']) ++ (map (\x -> "idle" ++ show chanindi2 ++ "_" ++ show x) [expr']))) ++ ")"
                                                   i1col' = i1col L.\\ [expr']
                                                   i2col' = i2col L.\\ [expr']
                                                   res1 = if (L.intersect i1col [expr']) /= []
                                                          then "idle" ++ show chanindi1 ++ "_" ++ show expr'
                                                          else "TRUE"
                                                   res1' = if (L.intersect i2col [expr']) /= []
                                                           then "idle" ++ show chanindi2 ++ "_" ++ show expr'
                                                           else "TRUE"
                                                   res1'' = "(" ++ res1 ++ " & " ++ res1' ++ ")"
                                                   res2 = (map (\x -> "(mrg" ++ show compind ++ "_sel = 1 & " ++ printDExpr madl (mkDexprI madl inttr i1) ++ " = " ++ show x ++ " & block" ++ show chanind ++ "_" ++ show x ++ ")") i1col') ++
                                                          (map (\x -> "(mrg" ++ show compind ++ "_sel = 2 & " ++ printDExpr madl (mkDexprI madl inttr i2) ++ " = " ++ show x ++ " & block" ++ show chanind ++ "_" ++ show x ++ ")") i2col')
                                                   res2' = foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] res2
                                                   res2'' = case res2' of
                                                              "" -> res2'
                                                              _ -> " | (" ++ res2' ++ ")"
                                                   res = ["INVAR idle" ++ show chanind ++ "_" ++ chancol ++ " = " ++ res1'' ++ res2''] ++
                                                         (L.concat (map (\x -> mkIdle madl i1 (D x) r') (L.intersect [expr'] i1col))) ++
                                                         (L.concat (map (\x -> mkIdle madl i2 (D x) r') (L.intersect [expr'] i2col))) ++
                                                         (L.concat (map (\x -> mkBlock madl chan (D x) r') i1col')) ++
                                                         (L.concat (map (\x -> mkBlock madl chan (D x) r') i2col'))
                                               in res
                                    Queue_t -> let i = ((inp madl) inttr) !! 0
                                                   chanindi = (chMap madl) BM.! i
                                                   qs = ((qSize madl) ("q" ++ show compind ++ "_state"))
                                                   qlast = "q" ++ show compind ++ "_state[" ++ show (qs - 1) ++ "]"
                                                   expr' = case expr of
                                                              (D n) -> n
                                                              _ -> error "mkIdle: unable to extract an integer out of a DExpr"
                                                   ocol = (c_g madl) chan
                                                   ocol' = ocol L.\\ [expr']
                                                   res = map (\x -> "(q" ++ show compind ++ "_ind > 0 & !(" ++ qlast ++ " = " ++ show expr' ++ ") & block" ++ show chanind ++ "_" ++ show x ++ " & (" ++ qlast ++ " = " ++ show x ++ "))") ocol'
                                                   res' = foldr (\a b -> case b of [] -> a; _ -> a ++ " | " ++ b) [] res
                                                   blocks = L.nub $ L.concat $ map (\x -> mkBlock madl chan (D x) r') ocol'
                                                   res'' = case res' of
                                                              "" -> res'
                                                              _ -> " | (" ++ res' ++ ")"
                                               in ["INVAR idle" ++ show chanind ++ "_" ++ chancol ++ " = ((" ++ "q" ++ show compind ++ "_ind = 0 & idle" ++ show chanindi ++ "_" ++ show expr' ++ ")" ++ res'' ++ ")"] ++
                                                  (mkIdle madl i expr r') ++
                                                  blocks
                                                  --(mkBlock madl chan (X ("q" ++ show compind ++ "state[" ++ show ((qSize madl) ("q" ++ show compind ++ "_state")) ++ "]")) r')
                                    Sink_t -> error "mkIdle: sinks do not have idle equations"
                                    Source_t -> ["INVAR idle" ++ show chanind ++ "_" ++ chancol ++ " = " ++ (printBExpr madl (mkSrcIdle expr ((c_g madl) chan)))]
                                    Switch_t -> let i = ((inp madl) inttr) !! 0
                                                    chanindi = (chMap madl) BM.! i
                                                in ["INVAR idle" ++ show chanind ++ "_" ++ chancol ++ " = idle" ++ show chanindi ++ "_" ++ chancol] ++
                                                   (mkIdle madl i expr r')

{-
mkIdle :: MaDL -> ChannelID -> DExpr -> BExpr
mkIdle madl cid expr = let targ = (initiator madl) cid
                           comptype = (t madl) targ
                           ind = (cMap madl) BM.! targ
                       in case comptype of
                             Fork_t -> let o = L.head $ filter (\x -> x /= cid) ((outp madl) targ)
                                       in Disj (mkIdle madl (((inp madl) targ) !! 0) expr) (mkBlock madl o expr)
                             Function_t -> mkIdle madl (((inp madl) targ) !! 0) (mkInverse madl targ expr ((c_g madl) cid))
                             Join_t -> Disj (mkIdle madl (((inp madl) targ) !! 1) (mkDexprI madl targ (((inp madl) targ) !! 1))) (mkIdle madl (((inp madl) targ) !! 0) expr)
                             Merge_t -> Disj
                                        (Conj (mkIdle madl (((inp madl) targ) !! 0) (mkDexprI madl targ (((inp madl) targ) !! 0))) (mkIdle madl (((inp madl) targ) !! 1) (mkDexprI madl targ (((inp madl) targ) !! 1))))
                                        (Disj
                                        (Conj (Equals (X ("mrg" ++ show ind ++ "_sel")) (D 1)) (Conj (mkBexprIIrdy madl targ (((inp madl) targ) !! 0)) (Conj (Negation (Equals (mkDexprI madl targ (((inp madl) targ) !! 0)) expr)) (mkBlock madl (((outp madl) targ) !! 0) (mkDexprI madl targ (((inp madl) targ) !! 0))))))
                                        (Conj (Equals (X ("mrg" ++ show ind ++ "_sel")) (D 2)) (Conj (mkBexprIIrdy madl targ (((inp madl) targ) !! 1)) (Conj (Negation (Equals (mkDexprI madl targ (((inp madl) targ) !! 1)) expr)) (mkBlock madl (((outp madl) targ) !! 0) (mkDexprI madl targ (((inp madl) targ) !! 1)))))))
                             Queue_t -> Disj (Conj (Equals (X ("q" ++ show ind ++ "_ind")) (D 0)) (mkIdle madl (((inp madl) targ) !! 0) expr))
                                             (Conj (Negation (Equals (X ("q" ++ show ind ++ "_ind")) (D 0))) (Conj (Negation (Equals (X ("q" ++ show ind ++ "state[" ++ show ((qSize madl) ("q" ++ show ind ++ "_state")) ++ "]")) expr)) (mkBlock madl (((outp madl) targ) !! 0) (X ("q" ++ show ind ++ "state[" ++ show ((qSize madl) ("q" ++ show ind ++ "_state")) ++ "]")))))
                             Sink_t -> error "mkIdle: sinks do not have idle equations"
                             Source_t -> mkSrcIdle expr ((c_g madl) cid)
                             Switch_t -> mkIdle madl (((inp madl) targ) !! 0) expr
-}

getSrcOIrdy :: Arg -> BExpr
getSrcOIrdy (Src_Upd (BDArgs (BArgs x _) _ _)) = x
getSrcOIrdy _ = error "getSrcOIrdy: unexpected input"

getSrcOTrdy :: Arg -> BExpr
getSrcOTrdy (Src_Upd (BDArgs (BArgs _ (BArg x)) _ _)) = x
getSrcOTrdy _ = error "getSrcOTrdy: unexpected input"

getSrcOData :: Arg -> DExpr
getSrcOData (Src_Upd (BDArgs _ (DArg x) _)) = x
getSrcOData _ = error "getSrcOData: unexpected input"

getQIIrdy :: Arg -> BExpr
getQIIrdy (Q_Upd (BDArgs (BArgs x _) _ _)) = x
getQIIrdy _ = error "getQIIrdy: unexpected input"

getQITrdy :: Arg -> BExpr
getQITrdy (Q_Upd (BDArgs (BArgs _ (BArgs x _)) _ _)) = x
getQITrdy _ = error "getQITrdy: unexpected input"

getQOIrdy :: Arg -> BExpr
getQOIrdy (Q_Upd (BDArgs (BArgs _ (BArgs _ (BArgs x _))) _ _)) = x
getQOIrdy _ = error "getQOIrdy: unexpected input"

getQOTrdy :: Arg -> BExpr
getQOTrdy (Q_Upd (BDArgs (BArgs _ (BArgs _ (BArgs _ (BArg x)))) _ _)) = x
getQOTrdy _ = error "getQOTrdy: unexpected input"

getQIData :: Arg -> DExpr
getQIData (Q_Upd (BDArgs _ (DArgs x _) _)) = x
getQIData _ = error "getQIData: unexpected input"

getQOData :: Arg -> DExpr
getQOData (Q_Upd (BDArgs _ (DArgs _ (DArg x)) _)) = x
getQOData _ = error "getQOData: unexpected input"

getMrgI0Irdy :: Arg -> BExpr
getMrgI0Irdy (Mrg_Upd (BDArgs (BArgs x _) _ _)) = x

getMrgI0Trdy :: Arg -> BExpr
getMrgI0Trdy (Mrg_Upd (BDArgs (BArgs _ (BArgs x _)) _ _)) = x

getMrgI1Irdy :: Arg -> BExpr
getMrgI1Irdy (Mrg_Upd (BDArgs (BArgs _ (BArgs _ (BArgs x _))) _ _)) = x

getMrgI1Trdy :: Arg -> BExpr
getMrgI1Trdy (Mrg_Upd (BDArgs (BArgs _ (BArgs _ (BArgs _ (BArgs x _)))) _ _)) = x

getMrgOIrdy :: Arg -> BExpr
getMrgOIrdy (Mrg_Upd (BDArgs (BArgs _ (BArgs _ (BArgs _ (BArgs _ (BArgs x _))))) _ _)) = x

getMrgOTrdy :: Arg -> BExpr
getMrgOTrdy (Mrg_Upd (BDArgs (BArgs _ (BArgs _ (BArgs _ (BArgs _ (BArgs _ (BArg x)))))) _ _)) = x

nameToArg :: Expr -> String -> Arg
nameToArg (S_Upd args) name = nameToArg' args
  where nameToArg' :: Args -> Arg
        nameToArg' (Args (Src_Upd (BDArgs a b (V s))) args) = if (s == name)
                                                              then (Src_Upd (BDArgs a b (V s)))
                                                              else nameToArg' args
        nameToArg' (Args (Q_Upd (BDArgs a b (V s))) args) = if (s == name)
                                                            then (Q_Upd (BDArgs a b (V s)))
                                                            else nameToArg' args
        nameToArg' (Args (Mrg_Upd (BDArgs a b (V s))) args) = if (s == name)
                                                              then (Mrg_Upd (BDArgs a b (V s)))
                                                              else nameToArg' args
        nameToArg' (Arg (Src_Upd (BDArgs a b (V s)))) = if (s == name)
                                                        then (Src_Upd (BDArgs a b (V s)))
                                                        else error "nameToArg: unexpected input"
        nameToArg' (Arg (Q_Upd (BDArgs a b (V s)))) = if (s == name)
                                                      then (Q_Upd (BDArgs a b (V s)))
                                                      else error "nameToArg: unexpected input"
        nameToArg' (Arg (Mrg_Upd (BDArgs a b (V s)))) = if (s == name)
                                                        then (Mrg_Upd (BDArgs a b (V s)))
                                                        else error "nameToArg: unexpected input"
        nameToArg' (Arg _) = error "nameToArg: unexpected input"
        nameToArg' _ = error "nameToArg: unexpected input"


printBExpr :: MaDL -> BExpr -> String
printBExpr _ (B True) = "TRUE"
printBExpr _ (B False) = "FALSE"
printBExpr _ (Y s) = s
printBExpr madl (Negation bexpr) = "!(" ++ printBExpr madl bexpr ++ ")"
printBExpr madl (NotEmpty (V s)) = let i = getID s in "(q" ++ show i ++ "_ind > 0)"
printBExpr madl (NotFull (V s)) = let i = getID s in "(q" ++ show i ++ "_ind < " ++ (show ((qSize madl) s)) ++ ")"
printBExpr madl (Conj b1 b2) = "(" ++ printBExpr madl b1 ++ " & " ++ printBExpr madl b2 ++ ")"
printBExpr madl (Disj b1 b2) = "(" ++ printBExpr madl b1 ++ " | " ++ printBExpr madl b2 ++ ")"
printBExpr madl (Equals d1 d2) = "(" ++ printDExpr madl d1 ++ " = " ++ printDExpr madl d2 ++ ")"


printDExpr :: MaDL -> DExpr -> String
printDExpr _ (D i) = show i
printDExpr _ (X s) = s
printDExpr madl (GetLast (V s)) = s ++ "[" ++ (show (((qSize madl) s) - 1)) ++ "]"
printDExpr madl (If b d1 d2) = "(" ++ printBExpr madl b ++ "? " ++ printDExpr madl d1 ++ " : " ++ printDExpr madl d2 ++ ")"


makeNEXT :: ColoredNetwork -> String
makeNEXT net = let madl = getMaDL net
                   expr = mkExpr madl
                   nxts = map (\x -> case getType x of
                                        Source_t -> makeSrcNEXT madl x
                                        Queue_t -> makeQNEXT madl x
                                        Merge_t -> makeMrgNEXT madl x
                                        _ -> "") $ getAllNames expr
               in foldr (\z z' -> case z' of "" -> z; _ -> z ++ "\n" ++ z') "" $ filter (\x -> x /= "") nxts
{-
makeInvarSpec :: ColoredNetwork -> String
makeInvarSpec net = let srcs = getAllSourceIDs net
                        madl = getMaDL net
                        b = map (\x -> let inp = varName net x "data"
                                       in mkBlock madl (L.head (getOutChannels net x)) (X inp)) srcs
                        b' = map (\x -> "INVARSPEC !" ++ printBExpr madl x) b
                    in "\n\n" ++ (foldr (\z z' -> case z' of "" -> z; _ -> z ++ "\n" ++ z') "" $ filter (\x -> x /= "") b')
-}

makeInvar :: ColoredNetwork -> String
makeInvar net = let srcs = getAllSourceIDs net
                    madl = getMaDL net
                    b = map (\x -> let o = L.head ((outp madl) x)
                                       cols = (c_g madl) o
                                       blocks = L.nub $ L.concat $ L.nub $ map (\y -> (mkBlock madl o (D y) [])) cols
                                   in {-foldr (\w w' -> case w' of "" -> w; _ -> w ++ "\n" ++ w') ""-} (filter (\z -> z /= []) blocks)) srcs
                    b' = (L.nub $ L.concat b)
                in "\n\n" ++ (foldr (\z z' -> case z' of "" -> z; _ -> z ++ "\n" ++ z') "" $ filter (\x -> x /= "") b')

makeInvarSpec :: ColoredNetwork -> String
makeInvarSpec net = let srcs = getAllSourceIDs net
                        madl = getMaDL net
                        chMap = chanMap net
                        b = L.nub $ L.concat $ map (\x -> let c = L.head $ getOutChannels net x
                                                              cols = (c_g madl) c
                                                              invspecs = map (\y -> "INVARSPEC !block" ++ (show (chMap BM.! c)) ++ "_" ++ show y) cols
                                                          in invspecs) srcs
                    in "\n\n" ++ (foldr (\z z' -> case z' of "" -> z; _ -> z ++ "\n" ++ z') "" $ filter (\x -> x /= "") b)
