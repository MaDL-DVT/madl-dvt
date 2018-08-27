{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleInstances, CPP #-}

module Madl2smv.Converter
where

import Madl.MsgTypes
import Madl.Network
import Madl.MsgTypes()
import Madl.Islands
import Utils.Text
import Data.Maybe
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Bimap as BM

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
              in BM.fromList (L.zip colors [0..(L.length colors)])

--Takes a network and creates a ComponentID-Int bimap
compMap :: ColoredNetwork -> BM.Bimap ComponentID Int
compMap net = let cids = getComponentIDs net
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
                          _ -> error "irdyName: unexpected component type"

--Takes a network, a ComponentID, a channel type (irdy, trdy, or data) and makes a variable declaration
varDecl :: ColoredNetwork -> ComponentID -> ChanType -> String
varDecl net cid t = let c = compType net cid
                        c' = foldr (\a b -> case b of "" -> noslashes (show a); _ -> noslashes (show a) ++ "," ++ noslashes (show b)) "" (map (\(_,x) -> x) c)
                    in case t of
                          Irdy -> "\t" ++ varName net cid "irdy" ++ " : boolean;"
                          Trdy -> "\t" ++ varName net cid "trdy" ++ " : boolean;"
                          Data -> "\t" ++ varName net cid "data" ++ " : {" ++ c' ++ "};"

--Takes a network, a ComponentID and returns the state name for the given component
stateName :: ColoredNetwork -> ComponentID -> String
stateName net cid = let cm = compMap net
                    in case (getComponent net cid) of
                          (Source _ _) -> "src" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_state"
                          (Queue _ _) -> "q" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_state"

--Takes a network, a ComponentID and returns the state declaration for the given component
stateDecl :: ColoredNetwork -> ComponentID -> String
stateDecl net cid = let c = compType net cid
                        c' = foldr (\a b -> case b of "" -> noslashes (show a); _ -> noslashes (show a) ++ "," ++ noslashes (show b)) "" (map (\(_,x) -> x) c)
                    in case (getComponent net cid) of
                          (Source _ _) -> "\t" ++ stateName net cid ++ " : {" ++ c' ++ "};"
                          (Queue _ n) -> "\t" ++ stateName net cid ++ " : array 0.." ++ noslashes (show (n-1)) ++ " of : {" ++ c' ++ "};"

--Takes a network, a ComponentID (has to be a queue) and returns a qInd variable name
qIndName :: ColoredNetwork -> ComponentID -> String
qIndName net cid = case (getComponent net cid) of
                      (Queue _ n) -> "q" ++ noslashes (show ((fromJust $ BM.lookup cid $ compMap net)::Int))
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

--Takes a network and makes a VAR block
makeVAR :: ColoredNetwork -> String
makeVAR net = let srcs = getAllSourceIDs net
                  snks = getAllSinkIDs net
                  qs = getAllQueueIDs net
              in "VAR\n" ++
                 foldr (\a b -> a ++ "\n" ++ b) "" ((map (\x -> varDecl net x Trdy) srcs) ++
                                                    (map (\x -> varDecl net x Irdy) snks) ++
                                                    (map (\x -> stateDecl net x) srcs) ++
                                                    (map (\x -> stateDecl net x) qs) ++
                                                    (map (\x -> qInd net x) qs))

--Takes a network and makes an INIT block
makeINIT :: ColoredNetwork -> String
makeINIT net = let srcs = getAllSourceIDs net
                   qs = getAllQueueIDs net
               in foldr (\a b -> a ++ "\n" ++ b) "" ((map (\x -> "\tinit(" ++ stateName net x ++ ") := 0;") srcs) ++
                                                     (map (\x -> "\tinit(" ++ qIndName net x ++ ") := 0;") qs) ++
                                                     (map (\x -> foldr (\a b -> a ++ "\n" ++ b) "" (map (\y -> "\tinit(" ++ stateName net x ++ "[" ++ noslashes (show y) ++ "]) := 0;") [0..((getQueueSize net x)-1)])) qs)
                                                      )


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
              | AssignB BExpr
              | Not BExpr
              | NotEmpty V
              | NotFull V
              | GetLast V
              | And BExpr BExpr
              | Or BExpr BExpr deriving Show
data DExpr =    D Int
              | X String
              | AssignD DExpr
              | Eq DExpr DExpr
              | If BExpr DExpr DExpr deriving Show
data V = V String deriving Show

--join, fork, function, merge, queue, sink, source, switch
data T = Join_t | Fork_t | Function_t | Merge_t | Queue_t | Sink_t | Source_t | Switch_t

data MaDL = MaDL { x :: [ComponentID],
                   g :: [ChannelID],
                   c_g :: ChannelID -> [Int],
                   fun :: ComponentID -> Int -> Int,
                   prd :: ComponentID -> Int -> Bool,
                   inp :: ComponentID -> [ChannelID],
                   outp :: ComponentID -> [ChannelID],
                   initiator :: ChannelID -> ComponentID,
                   target :: ChannelID -> ComponentID,
                   isFirst :: ChannelID -> Bool,
                   t :: ComponentID -> T,
                   def :: Int }

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
--Join_t | Fork_t | Function_t | Merge_t | Queue_t | Sink_t | Source_t | Switch_t
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

getMaDL :: ColoredNetwork -> MaDL
getMaDL net = MaDL { x = getX net,
                     g = getG net,
                     c_g = getCg net,
                     fun = getFun net,
                     prd = getPrd net,
                     inp = getInp net,
                     outp = getOutp net,
                     initiator = getInitiator net,
                     target = getTarget net,
                     isFirst = getIsFirst net,
                     t = getT net,
                     def = defaultColor
                    }

{-instance Show Prediction where
  show (Prediction a b c) = show a ++ "-" ++ show b ++ "-" ++ show c-}
