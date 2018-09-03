{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleInstances, CPP #-}

module Madl2smv.Converter
where

import Madl.MsgTypes
import Madl.Network
import Madl.MsgTypes()
import Madl.Islands
import Utils.Text
import Data.Maybe
import qualified Data.Char as C
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
              in BM.fromList (L.zip colors [1..((L.length colors)+1)])

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
                          (Merge _) -> "mrg" ++ noslashes (show ((fromJust $ BM.lookup cid cm)::Int)) ++ "_sel"
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
                   in "\t" ++ mVarName net cid ++ " : {0,1,2};"

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

--Takes a network and makes a VAR block
makeVAR :: ColoredNetwork -> String
makeVAR net = let srcs = getAllSourceIDs net
                  snks = getAllSinkIDs net
                  qs = getAllQueueIDs net
                  mrgs = getAllMergeIDs net
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
                                                    (map (\x -> qInd net x) qs))

--Takes a network and makes an INIT block
makeINIT :: ColoredNetwork -> String
makeINIT net = let srcs = getAllSourceIDs net
                   qs = getAllQueueIDs net
               in foldr (\a b -> a ++ "\n" ++ b) "" ((map (\x -> "\tinit(" ++ stateName net x ++ ") := 0;") srcs) ++
                                                     (map (\x -> "\tinit(" ++ qIndName net x ++ ") := 0;") qs) ++
                                                     (map (\x -> foldr (\a b -> a ++ "\n" ++ b) "" (map (\y -> "\tinit(" ++ stateName net x ++ "[" ++ noslashes (show y) ++ "]) := 0;") [0..((getQueueSize net x)-1)])) qs)
                                                      )

makeSMV :: ColoredNetwork -> String
makeSMV net = "MODULE main\n" ++
              makeVAR net ++ "\n" ++
              "ASSIGN\n" ++
              makeINIT net ++
              makeNEXT net

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
                     def = defaultColor
                    }

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
                                            else Conj (mkBexprIIrdy madl cid (L.head ((inp madl) cid))) (Negation (mkPred madl cid ((c_g madl) chan)))

mkBexprITrdy :: MaDL -> ComponentID -> ChannelID -> BExpr
mkBexprITrdy madl cid chan = case ((t madl) cid) of
                                Fork_t -> Conj (mkBexprOTrdy madl cid (((outp madl) cid) !! 0)) (mkBexprOTrdy madl cid (((outp madl) cid) !! 0))
                                Function_t -> mkBexprOTrdy madl cid (((outp madl) cid) !! 0)
                                Join_t -> Conj (mkBexprIIrdy madl cid (L.head $ filter (\x -> x /= chan) ((inp madl) cid))) (mkBexprOTrdy madl cid (L.head ((outp madl) cid)))
                                Merge_t -> if (chan /= (((inp madl) cid) !! 1))
                                           then Conj (Conj (Y ((intName madl) cid "")) (mkBexprOTrdy madl cid (L.head ((outp madl) cid)))) (mkBexprIIrdy madl cid (((inp madl) cid) !! 1))
                                           else Conj (Conj (Negation (Y ((intName madl) cid ""))) (mkBexprOTrdy madl cid (L.head ((outp madl) cid)))) (mkBexprIIrdy madl cid (((inp madl) cid) !! 0))
                                Queue_t -> NotFull (V $ (stName madl) cid)
                                Sink_t -> Conj (Y ((intName madl) cid "trdy")) (Equals (mkDexprO madl ((initiator madl) chan) chan) (mkDexprI madl cid chan))
                                Switch_t -> Disj (Conj (mkBexprOIrdy madl cid (((outp madl) cid) !! 0)) (mkBexprOTrdy madl cid (((inp madl) cid) !! 0))) (Conj (mkBexprOIrdy madl cid (((inp madl) cid) !! 1)) (mkBexprOTrdy madl cid (((inp madl) cid) !! 1)))

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
mkPred madl cid [] = error "mkPred: list of colors can not be empty"
mkPred madl cid (x:[]) = Equals (mkDexprI madl cid (L.head ((inp madl) cid))) (D x)
mkPred madl cid (x:xs) = Disj (Equals (mkDexprI madl cid (L.head ((inp madl) cid))) (D x)) (mkPred madl cid xs)

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
  | otherwise = error "mkFun: list of colors can not be empty"

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
                            "\t\t\t\t((" ++ sname ++ " = 0) | (" ++ sname ++ " = " ++ mname ++ ")) & ((" ++ i0irdy ++ " & " ++ i0trdy ++ " & !" ++ mname ++ ") | (" ++ i1irdy ++ " & " ++ i1trdy ++ " & " ++ mname ++ ")) : 0;\n" ++
                            --((state = 0) | (state = sel)) & (!(i0i & i01) & !sel) -> 1
                            "\t\t\t\t((" ++ sname ++ " = 0) | (" ++ sname ++ " = " ++ mname ++ ")) & (!(" ++ i0irdy ++ " & " ++ i1irdy ++ ") & !" ++ mname ++ ") : 1;\n" ++
                            --((state = 0) | (state = sel)) & (!(i0i & i01) & sel) -> 2
                            "\t\t\t\t((" ++ sname ++ " = 0) | (" ++ sname ++ " = " ++ mname ++ ")) & (!(" ++ i0irdy ++ " & " ++ i1irdy ++ ") & !" ++ mname ++ ") : 2;\n" ++
                            "\t\t\tesac;\n"


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
