{-# LANGUAGE OverloadedStrings #-}

module Verilog2MaDL (verilog2MaDL) where

import Data.Maybe (catMaybes, fromMaybe, isJust)
import qualified Data.Set as Set
import Data.Text.Encoding (decodeUtf8)

import Utils.Text

import BaseLike.CustomPrelude
import BooleanSymbolic.Class (falseC)
import BooleanSymbolic.NetStructure

import Madl.MsgTypes
import Madl.Network

-- | Error function
fileName :: Text
fileName = "Verilog2MaDL"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

data UndirectedComponent =
      SourceSink {undirectedComponentName :: Text} -- Source or Sink
    | Synchronizer {undirectedComponentName :: Text} -- Fork or Join
    | Arbiter {undirectedComponentName :: Text} -- Switch or Merge

type NetworkComponents = ([ComponentOrMacro Channel], [Channel], [(Text, Text)])

type PartialNetwork = ([Component], [UndirectedComponent], [Channel], [(Text, Text)])

getQueueNames :: NETTree ([ByteString], ByteString) -> [Text]
getQueueNames (NETLeaf a _ _) = [getQueueName a]
getQueueNames (NETSync h tl  ) = concatMap getQueueNames (h:tl)
getQueueNames (NETXor lst _ _) = concatMap getQueueNames lst
getQueueNames (NETImpl a b _ _) = concatMap getQueueNames [a,b]

getQueueName :: ([ByteString], ByteString) -> Text
getQueueName (scp,_) = "Queue"<>encodeT scp

encodeT :: Encodable a => a -> Text
encodeT = decodeUtf8 . encode -- TODO(tssb): correct decoding? -> ask @basj

directComponent :: UndirectedComponent -> NetworkComponents -> NetworkComponents
directComponent comp (comps, channels, ports) = case comp of
    _c@SourceSink{} -> case (length inports, length outports) of
        (0, 1) -> (newcomp:comps, channels, ports)
                   where newcomp = C $ Source{componentName = compName, messages = nul}  -- TODO(tssb): messages
        (1, 0) -> (newcomp:comps, channels, ports)
                   where newcomp = C $ Sink{componentName = compName}
        _      -> fatal 116 "Incorrect number of channels"
    _c@Arbiter{} -> case (length inports, length outports) of
        (0, _) -> fatal 120 "Incorrect number of input channels"
        (_, 0) -> fatal 121 "Incorrect number of output channels"
        (1, 1) -> (comps, channels', ports') where
                   channels' = Channel{channelName=compName}:[chan | chan <- channels, getName chan /= inChan, getName chan /= outChan]
                   inChan = fst $ head inports
                   outChan = snd $ head outports
                   ports' = [(if i == outChan then compName else i, if t == inChan then compName else t) | p@(i, t) <- ports, p `notElem` inports, p `notElem` outports]
        (1, 2) -> (newcomp:comps, channels, ports) where
                    newcomp = C $ Switch{componentName = compName, switching = [XTrue, XFalse]} -- TODO(tssb): switching
        (2, 1) -> (newcomp:comps, channels, ports) where
                    newcomp = C $ Merge{componentName = compName}
        (1, n) -> (newcomp:comps, channels, ports) where
                    newcomp = M $ MacroInstance{instanceName = compName, instanceMacro = multiSwitchMacro n}
        (n, 1) -> (newcomp:comps, channels, ports) where
                    newcomp = M $ MacroInstance{instanceName = compName, instanceMacro = multiMergeMacro n}
        _     -> fatal 135 "Incorrect number of channels"
    _c@Synchronizer{} -> case (length inports, length outports) of
        (0, _) -> fatal 137 "Incorrect number of input channels"
        (_, 0) -> fatal 138 "Incorrect number of output channels"
        (1, 1) -> (comps, channels', ports') where
                   channels' = Channel{channelName=compName}:[chan | chan <- channels, getName chan /= inChan, getName chan /= outChan]
                   inChan = fst $ head inports
                   outChan = snd $ head outports
                   ports' = [(if i == outChan then compName else i, if t == inChan then compName else t) | p@(i, t) <- ports, p `notElem` inports, p `notElem` outports]
        (1, 2) -> (newcomp:comps, channels, ports) where
                    newcomp = C $ Fork{componentName = compName}
        (2, 1) -> (newcomp:comps, channels, ports) where
                    newcomp = C $ ControlJoin{componentName = compName} -- TODO(tssb): Join instead of ControlJoin
        (1, n) -> (newcomp:comps, channels, ports) where
                    newcomp = M $ MacroInstance{instanceName = compName, instanceMacro = multiForkMacro n}
        (n, 1) -> (newcomp:comps, channels, ports) where
                    newcomp = M $ MacroInstance{instanceName = compName, instanceMacro = multiJoinMacro n}
        (n, m) -> (newcomp:comps, channels, ports) where
                    newcomp = M $ MacroInstance{instanceName = compName, instanceMacro = multiSynchronizerMacro n m}
    where
        compName = undirectedComponentName comp
        inports = [(i, t) | (i,t) <- ports, t == compName]
        outports = [(i, t) | (i,t) <- ports, i == compName]

multiSwitchMacro :: Int -> Macro Channel
multiSwitchMacro = multiOutputMacro "switch" $ flip Switch [XTrue, XFalse] -- TODO(tssb): switching

multiMergeMacro :: Int -> Macro Channel
multiMergeMacro =  multiInputMacro "merge" Merge

multiForkMacro :: Int -> Macro Channel
multiForkMacro =  multiOutputMacro "fork" Fork

multiJoinMacro :: Int -> Macro Channel
multiJoinMacro =  multiInputMacro "join" ControlJoin -- TODO(tssb): Join instead of ControlJoin

multiSynchronizerMacro :: Int -> Int -> Macro Channel
multiSynchronizerMacro n m =
    Macro{macroInterface=interface, macroName="synchronizer" +++ showT n +++ "-" +++ showT m, macroNetwork=network}
    where
        cs = [M MacroInstance{instanceName="join", instanceMacro=multiJoinMacro n},
                        M MacroInstance{instanceName="fork", instanceMacro = multiForkMacro m}]

        channels = Channel{channelName = "join_fork"}:
                    [Channel{channelName="input"<>showT i} | i <- [0..n-1]] ++
                    [Channel{channelName="output"<>showT i} | i <- [0..m-1]]
        ports = ("join", "join_fork"):("join_fork", "fork"):
                 [("input"<>showT i, "join") | i <- [0..n-1]] ++
                 [("fork", "output"<>showT i) | i <- [0..m-1]]

        network = mkMacroNetwork (NSpec cs channels ports)
        interface = fmap getChanNumber (["input"<>showT i | i <- [0..n-1]] ++ ["output"<>showT i | i <- [0..m-1]])
        getChanNumber = fromMaybe (fatal 168 "Illegal name") . findChannelID network

multiOutputMacro :: Text -> (Text -> Component) -> Int -> Macro Channel
multiOutputMacro name makeComponent n =
    Macro{macroInterface=interface, macroName="multi" +++ name +++ showT n, macroNetwork=network}
    where cs = [C $ makeComponent (name<>showT i) | i <- [0..n-2]]
          channels = Channel{channelName="input"} :
                    [Channel{channelName = "to"<>name<>showT i} | i <- [1..n-2]] ++
                    [Channel{channelName = "output"<>showT i} | i <- [0..n-1]]
          ports = ("input", name<>"0"):(name<>showT (n-2), "output"<>showT (n-1)):
                 [(name<>showT i, "to"<>name<>showT (i+1)) | i <- [0, n-1]] ++
                 [("to"<>name<>showT i, name<>showT i) | i <- [1, n-2]] ++
                 [(name<>showT i, "output"<>showT i) | i <- [0..n-2]]

          network = mkMacroNetwork (NSpec cs channels ports)
          interface = fmap getChanNumber ("input":["output"<>showT i | i <- [0..n-1]])
          getChanNumber = fromMaybe (fatal 168 "Illegal name") . findChannelID network

multiInputMacro :: Text -> (Text -> Component) -> Int -> Macro Channel
multiInputMacro name makeComponent n =
    Macro{macroInterface=interface, macroName="multi" +++ name +++ showT n, macroNetwork=network}
    where cs = [C $ makeComponent (name<>showT i) | i <- [1..n-1]]
          channels = Channel{channelName="output"} :
                    [Channel{channelName = "from"<>name<>showT i} | i <- [1..n-2]] ++
                    [Channel{channelName = "input"<>showT i} | i <- [0..n-1]]
          ports = ("input0", name<>"1"):(name<>showT (n-1), "output"):
                 [("input"<>showT i, name<>showT i) | i <- [1..n-1]] ++
                 [(name<>showT i, "from"<>name<>showT i) | i <- [1, n-2]] ++
                 [("from"<>name<>showT i, name<>showT (i+1)) | i <- [1, n-2]]

          network = mkMacroNetwork (NSpec cs channels ports)
          interface = fmap getChanNumber (["input"<>showT i | i <- [0..n-1]]++["output"])
          getChanNumber = fromMaybe (fatal 168 "Illegal name") . findChannelID network

verilog2MaDL :: [(NETTree ([ByteString],ByteString), Bool)] -> MadlNetwork
verilog2MaDL network = mkNetwork (NSpec cs channels ports)
    where
        -- components = queues ++ otherComps
        uniqueQueueNames = Set.toList . Set.fromList $ mconcat [getQueueNames tr | (tr,_) <- network]
        queues = fmap makeQueue uniqueQueueNames

        (comps, undirectedComps, chans, prts) = mconcat $ mapWithIndex drawtree network
        (cs, channels, ports) = foldr directComponent (queues ++ fmap C comps, chans, prts) undirectedComps

        makeQueue :: Text -> ComponentOrMacro Channel
        makeQueue name = C $ Queue {componentName = name, capacity = 2} -- TODO(tssb): capacity

        drawtree :: Int -> (NETTree ([ByteString], ByteString), Bool) -> PartialNetwork
        drawtree i (NETSync a as,False)
          = ([], [SourceSink {undirectedComponentName="P" +++ showT i}], [], [])
            <> ( drawTreeFromTop i $
                 NETSync (NETLeaf ([],"P"<>pack (show i)) falseC falseC) (a:as) )
        drawtree i (tree,False)
          = ([], [SourceSink {undirectedComponentName="P" +++ showT i}], [], [])
            <> ( drawTreeFromTop i $
                 NETSync (NETLeaf ([],"P"<>pack (show i)) falseC falseC) [tree] )
        drawtree i (tree,True)
          = drawTreeFromTop i tree

        drawTreeFromTop :: Int -> NETTree ([ByteString],ByteString) -> PartialNetwork
        drawTreeFromTop i (NETSync h tl)
          = case giveTwoSides i (h:tl) of
              ([(a,as)],[b]) -> as <> connect False a b -- do not draw top level synchroniser
              (upSide,downSide) -> syncVal
                                   <> mConcatMap (connect True  name) upSide
                                   <> mConcatMap (connect False name) downSide
          where (name,syncVal) = sync [i]
        drawTreeFromTop i e
          = case orient [] i e of
             (Up   (nm,res)) -> connect False nm ("Snk" +++ showT i, res)
             (Down (nm,res)) -> connect True nm ("Src" +++ showT i, res)
             (Both ((nm,res),_)) -> connect False nm ("Snk" +++ showT i, res)

        giveTwoSides :: Int -> [NETTree ([ByteString], ByteString)] -> ([(Text, PartialNetwork)], [(Text, PartialNetwork)])
        giveTwoSides i lst -- balance; add sink/source if needed
          = case splitOver (mapWithIndex (orient [i]) lst) of
              ([],rhs) -> ([(name, source)] ,rhs)
                            where source = ([Source{componentName=name, messages=nul}], [], [], [])
                                  name = "Src" +++ showT i
              (lhs,[]) -> (lhs, [(name, sink)])
                           where sink = ([Sink{componentName=name}], [], [], [])
                                 name = "Snk" +++ showT i
              (lhs,rhs) -> (lhs,rhs)

        splitOver :: [Orientation a] -> ([a], [a])
        splitOver oriented -- attempts to balance its arguments over Down and Up
          = case (ups++extraUps, downs) of
              (lhs,rhs@(_:_)) -> (lhs,rhs)
              (_,[]) -> (case (ups, downs++extraDowns) of
                          ([],_) -> (take 1 extraUps,drop 1 extraDowns)
                          (lhs@(_:_),rhs) -> (lhs,rhs)
                        )
          where ups = [a | Up a <- oriented]
                downs = [a | Down a <- oriented]
                extraUps = [a | Both (a,_) <- oriented]
                extraDowns = [a | Both (_,a) <- oriented]

        sync :: Encodable a => a -> (Text, PartialNetwork) -- Synchronizer (fork / join)
        sync ref = (name, ([], [Synchronizer {undirectedComponentName=name}], [], []))
            where name = encodeT ref

        rout :: Encodable a => a -> (Text, PartialNetwork) -- Arbiter (merge / switch)
        rout ref = (name, ([], [Arbiter {undirectedComponentName=name}], [], []))
            where name = encodeT ref

        orient :: [Int] -> Int -> NETTree ([ByteString], ByteString) -> Orientation (Text, PartialNetwork)
        orient _ _ (NETLeaf ([],v) _ _)
         = Both ((decodeUtf8 v,([], [], [], [])),(decodeUtf8 v,([], [], [], [])))
        orient _ _ (NETLeaf o@(_,v) _ _)
         = if v `elem` ["inputTransfer","increase"]
           then Down (getQueueName o, ([], [], [], []))
           else Up   (getQueueName o, ([], [], [], []))
        orient lst i (NETSync h tl)
         = case splitOver oriented of
             ([],rhs) -> Down (name,syncVal <> mConcatMap (connect False name) rhs)
             (lhs,[]) -> Up   (name,syncVal <> mConcatMap (connect True  name) lhs)
             (lhs,rhs)-> Both ((name,syncVal <> mConcatMap (connect False name) rhs <> mConcatMap (connect True  name) lhs)
                              ,(name,syncVal <> mConcatMap (connect False name) rhs <> mConcatMap (connect True  name) lhs)
                              )
         where (name,syncVal) = sync ref
               oriented = mapWithIndex (orient ref) (h:tl)
               ref = i:lst
        orient lst i (NETImpl h tl _ _)
         = case (oH,oTl) of
             (Up h'       ,dwn           ) -> Up  $ switchFor h' (makeDown ref dwn)
             (Both (_ ,h'),Up   tl'      ) -> Down$ mergeFor h' tl'
             (Both (h',_ ),Down tl'      ) -> Up  $ switchFor h' tl'
             (Both (h1,h2),Both (tl1,tl2)) -> Both (switchFor h1 tl2, mergeFor h2 tl1)
             (Down h'     ,up            ) -> Down$ mergeFor h' (makeUp ref up)
         where (xorName,xorVal) = rout ref
               oH  = orient ref 0 h
               oTl = orient ref 1 tl
               mergeFor  h' tl' = (xorName,xorVal <> connect True  xorName h'  <> connect False xorName tl')
               switchFor h' tl' = (xorName,xorVal <> connect False xorName tl' <> connect True  xorName h' )
               ref = i:lst
        orient lst i (NETXor subs _ _)
         = case (allUp,allDown) of
            (True,False)  -> Up   resUp
            (False,True)  -> Down resDown
            (True,True)   -> Both (resUp,resDown)
            (False,False) -> if length ups > length downs then Up forceUp
                             else if length ups < length downs then Down forceDown
                             else Both (forceUp,forceDown)
         where (xorName,xorVal) = rout ref
               oriented = mapWithIndex (orient ref) subs
               allUp     = and (fmap (isJust . giveUp  ) oriented)
               allDown   = and (fmap (isJust . giveDown) oriented)
               resUp     = (xorName,xorVal <> mConcatMap (connect True  xorName) ups)
               resDown   = (xorName,xorVal <> mConcatMap (connect False xorName) downs)
               forceUp   = (xorName,xorVal <> mConcatMap (connect True  xorName) forceUps)
               forceDown = (xorName,xorVal <> mConcatMap (connect False xorName) forceDowns)
               forceUps,forceDowns :: [(Text,PartialNetwork)]
               forceUps  = mapWithIndex (curry makeUp   ref) oriented
               forceDowns= mapWithIndex (curry makeDown ref) oriented
               ups   = catMaybes (fmap giveUp   oriented)
               downs = catMaybes (fmap giveDown oriented)
               ref = i:lst
               giveUp (Up a) = Just a
               giveUp (Both (a,_)) = Just a
               giveUp (Down _) = Nothing
               giveDown (Up _) = Nothing
               giveDown (Both (_,a)) = Just a
               giveDown (Down a) = Just a

        makeUp :: Encodable b => b -> Orientation (Text, PartialNetwork) -> (Text, PartialNetwork)
        makeUp   _ (Up a) = a
        makeUp   _ (Both (a,_)) = a
        makeUp   r (Down a)
         = (name
           , connect True  ("Snk" +++ r') (name, syncVal<>sink)
           <>connect True  name a
           )
           where (name,syncVal) = sync r
                 r'=  encodeT r
                 sink = ([Sink{componentName="Snk" +++ r'}], [], [], [])

        makeDown :: Encodable b => b -> Orientation (Text, PartialNetwork) -> (Text, PartialNetwork)
        makeDown r (Up a)
         = (name
           , connect False ("Src" +++ r') (name, syncVal<>source)
           <> connect False name a
           )
           where (name,syncVal) = sync r
                 r'=  encodeT r
                 source = ([Source{componentName="Src" +++ r', messages=nul}], [], [], [])
        makeDown _ (Both (_,a)) = a
        makeDown _ (Down a) = a

        connect :: Bool -> Text -> (Text,PartialNetwork) -> PartialNetwork
        connect isReversed fromNm (toNm,(a,b,c,links)) = (a,b,newChannel:c,newLink1:newLink2:links)
            where
             newLink1 = if isReversed then (toNm, newChannelName) else (fromNm, newChannelName)
             newLink2 = if isReversed then (newChannelName, fromNm) else (newChannelName, toNm)
             newChannel = Channel{channelName = newChannelName}
             newChannelName = if isReversed then toNm .> fromNm else fromNm .> toNm

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0..]

mConcatMap :: Monoid c => (a -> c) -> [a] -> c -- can be generalised over foldable structures, which is not needed here and not used as it requires a diferent implementation
mConcatMap f = mconcat . fmap f