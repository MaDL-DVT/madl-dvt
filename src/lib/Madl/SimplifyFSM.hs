module Madl.SimplifyFSM where

import Madl.Base
import Madl.Base.Identifiers
import Madl.Network
import Madl.MsgTypes
import qualified Data.IntMap as IM
import qualified Data.HashMap as HM
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as MB

{- ******* Supplementary functions ******* -}

debugInd :: [a] -> Int -> String -> a
debugInd xs i s = if (L.length xs) <= i
                  then error ("incorrect index: " ++ s)
                  else xs !! i

debugFromJust :: Maybe a -> String -> a
debugFromJust (Just a) _ = a
debugFromJust Nothing s = error ("incorrect from just: " ++ s)

getLeftMatch :: MFunctionBool -> MFunctionDisj
getLeftMatch (XMatch f _) = f
getLeftMatch _ = error "getLeftMatch: Wrong function"

getAllTypes :: ColoredNetwork -> [Color]
getAllTypes net = let chans = getChannelIDs net
                      cols = L.nub $ L.concat $ map (\x -> let (ColorSet col) = getColorSet net x in S.toList col) chans
                  in cols

getInTypes :: ColoredNetwork -> ComponentID -> ChannelID -> [Color]
getInTypes net comp chan = case (getComponent net comp) of
                             (Automaton _ _ _ _ ts _) -> let --cols = getAllTypes net
                                                             ins = getInChannels net comp
                                                             inind = debugFromJust (L.elemIndex chan ins) "getInTypes 1"
                                                             --res = (filter (\x -> eval (makeVArguments (L.replicate (L.length ins) x)) infun) cols')
                                                             ts' = filter (\(AutomatonT _ _ inport _ _ _ _ _) -> inport == inind) ts
                                                             cols = L.nub $ map (\(AutomatonT _ _ _ f _ _ _ _) -> eval (makeVArguments []) (getLeftMatch f)) ts'
                                                         in cols
                             _ -> error "getInTypes: Automaton expected"

getOutTypes :: ColoredNetwork -> ComponentID -> ChannelID -> [Color]
getOutTypes net comp chan = case (getComponent net comp) of
                             (Automaton _ _ _ _ ts _) -> let --cols = getAllTypes net
                                                             outs = getOutChannels net comp
                                                             outind = debugFromJust (L.elemIndex chan outs) "getOutTypes 1"
                                                             --res = (filter (\x -> eval (makeVArguments (L.replicate (L.length ins) x)) infun) cols')
                                                             ts' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> case outport of Nothing -> False; _ -> True) ts
                                                             ts'' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> (debugFromJust outport "getOutTypes 2") == outind) ts'
                                                             cols = L.nub $ map (\(AutomatonT _ _ _ _ _ _ f _) -> eval (makeVArguments []) (debugFromJust f "getOutTypes 3")) ts''
                                                         in cols
                             _ -> error "getInTypes: Automaton expected"

channelIDtoInt :: ChannelID -> Int
channelIDtoInt (ChannelIDImpl i) = i

intToChannelID :: Int -> ChannelID
intToChannelID i = ChannelIDImpl i

componentIDtoInt :: ComponentID -> Int
componentIDtoInt (ComponentIDImpl i) = i

intToComponentID :: Int -> ComponentID
intToComponentID i = ComponentIDImpl i

getCompMap :: ColoredNetwork -> IM.IntMap (ComponentContext (XComponent T.Text))
getCompMap (NetworkImpl x _) = x

getChanMap :: ColoredNetwork -> IM.IntMap (ChannelContext (WithColors (XChannel T.Text)))
getChanMap (NetworkImpl _ x) = x


withoutColors :: ColoredNetwork -> XFlattenedNetwork T.Text
withoutColors net = removeColors net

colorTest :: ColoredNetwork -> ColoredNetwork
colorTest net = channelTypes $ removeColors net

token :: ColorSet
token = ColorSet (S.singleton (Color (T.pack "tok") (Right (Value 0))))

testSpec :: Specification (XComponent T.Text) (XChannel T.Text) T.Text
testSpec = NSpec [Source (T.pack "src") token, LoadBalancer (T.pack "lb"), Queue (T.pack "q") 1, Sink (T.pack "snk"), Sink (T.pack "snk1")]
                 [Channel (T.pack "src_lb"), Channel (T.pack "1"), Channel (T.pack "2"), Channel (T.pack "q_snk")]
                 [(T.pack "src", T.pack "src_lb"), (T.pack "src_lb", T.pack "lb"),
                  (T.pack "q", T.pack "q_snk"), (T.pack "q_snk", T.pack "snk"),
                  (T.pack "lb", T.pack "1"), (T.pack "1", T.pack "snk1"),
                  (T.pack "lb", T.pack "2"), (T.pack "2", T.pack "q")]


getALoadBalancer :: ColoredNetwork -> ComponentID
getALoadBalancer net = debugInd (filter (\x -> case (getComponent net x) of (LoadBalancer _) -> True; _ -> False) (getComponentIDs net)) 0 "getLoadBalancer"


getFSMIDs :: ColoredNetwork -> [ComponentID]
getFSMIDs net = map (\(x,_) -> x) (getAllProcessesWithID net)


getCompName :: ComponentID -> IM.IntMap (ComponentContext (XComponent T.Text)) -> T.Text
getCompName cid cm = let (_,x,_) = cm IM.! (componentIDtoInt cid)
                     in componentName x


getITransColor :: ColoredNetwork -> AutomatonTransition -> ComponentID -> ChannelID -> Color
getITransColor net tr@(AutomatonT _ _ _ infun _ _ _ _) comp chan = let --incols = getAllTypes net
                                                                       cols' = getInTypes net comp chan
                                                                       {-(ColorSet cols) = getColorSet net chan
                                                                       cos' = S.toList cols-}
                                                                       ins = getInChannels net comp
                                                                       res = (filter (\x -> eval (makeVArguments []) (getLeftMatch infun) == x) cols')
                                                                       y = (eval (makeVArguments []) (getLeftMatch infun)) :: Color
                                                                       res' = if res == []
                                                                              then error $ show (y) --("getITransColor: Can not derive the color")
                                                                              else debugInd res 0 "getITransColor"
                                                                   in res'

getOTransColor :: ColoredNetwork -> AutomatonTransition -> Color
getOTransColor net (AutomatonT _ _ _ _ _ _ outfun _) = case outfun of
                                                         (Just fun) -> eval (makeVArguments []) fun
                                                         _ -> error "getOTransColor: Output function is absent"


noRedundantTrans :: ColoredNetwork -> ComponentID -> [AutomatonTransition]
noRedundantTrans net comp = case (getComponent net comp) of
                              (Automaton _ _ _ _ ts _) -> let rind = getRedundantInpID net comp
                                                              res = case rind of
                                                                      (Just rind') -> filter (\(AutomatonT _ _ inp _ _ _ _ _) -> inp /= rind') ts
                                                                      Nothing -> ts
                                                          in res
                              _ -> error "noRedundantTrans: Automaton expected"


netToSpec :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
netToSpec net = let net' = removeColors net
                    compMap = componentMap net'
                    chanMap = channelMap net'
                    comps = L.nub (map (\(_,x,_) -> x) (IM.elems compMap))
                    chans = L.nub (map (\(_,x,_) -> x) (IM.elems chanMap))
                    ports = (map (\(x,y,_) -> (getCompName x compMap, channelName y)) (IM.elems chanMap)) ++ (map (\(_,x,y) -> (channelName x, getCompName y compMap)) (IM.elems chanMap))
                in NSpec comps chans ports

replaceFSM :: ColoredNetwork -> ComponentID -> Int -> ColoredNetwork
replaceFSM net comp fsmind = case (getComponent net comp) of
                               (Automaton fsmname _ _ _ _ _) -> let (NSpec comps chans ports) = netToSpec net
                                                                    rind = getRedundantInpID net comp
                                                                    ins = getInChannels net comp
                                                                    chans' = case rind of
                                                                               Just rind' -> filter (\x -> x /= (fst $ getChannel net (debugInd ins rind' "replaceFSM 1"))) chans
                                                                               Nothing -> chans
                                                                    comps' = case rind of
                                                                               Just rind' -> filter (\x -> ((getName x) /= fsmname) && (x /= (getComponent net (getInitiator net (debugInd ins rind' "replaceFSM 2"))))) comps
                                                                               Nothing -> filter (\x -> (getName x) /= fsmname) comps
                                                                    ports' = case rind of
                                                                               Just rind' -> filter (\(a,b) -> (a /= fsmname) && (b /= fsmname) && (a /= (getName (getComponent net (getInitiator net (debugInd ins rind' "replaceFSM 3"))))) && (b /= (getName (getComponent net (getInitiator net (debugInd ins rind' "replaceFSM 4")))))) ports
                                                                               Nothing -> filter (\(a,b) -> (a /= fsmname) && (b /= fsmname)) ports
                                                                    (NSpec fsmcomps fsmchans fsmports) = translateFSM net comp fsmind
                                                                    spec = (NSpec (comps' ++ fsmcomps) (chans' ++ fsmchans) (ports' ++ fsmports))
                                                                in channelTypes $ Madl.Network.mkNetwork spec
                               comp' -> error "replaceFSM: Automaton expected"


updateNetwork :: ColoredNetwork -> ColoredNetwork
updateNetwork net = updateNetwork' net (getFSMIDs net) 0
  where updateNetwork' :: ColoredNetwork -> [ComponentID] -> Int -> ColoredNetwork
        updateNetwork' net [] _ = net
        updateNetwork' net (x:_) fsmind = let net' = replaceFSM net x fsmind in updateNetwork' net' (getFSMIDs net') (fsmind + 1)



translateFSM :: ColoredNetwork -> ComponentID -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
translateFSM net comp fsmind =
  case (getComponent net comp) of
    (Automaton _ _ _ n ts _) -> let ins' = getInChannels net comp
                                    outs = getOutChannels net comp
                                    rind = getRedundantInpID net comp
                                    ins = case rind of
                                            Just rind' -> let rm = debugInd ins' rind' "translateFSM 1" in filter (\x -> x /= rm) ins'
                                            Nothing -> ins'
                                    t_init = initTemplate net comp fsmind
                                    t_ins = map (\x -> inputTemplate net comp x fsmind) ins
                                    t_outs = map (\x -> outputTemplate net comp x fsmind) outs
                                    t_state = map (\x -> stateTemplate net comp x fsmind) [0..n-1]
                                    t_trans = map (\x -> case x of
                                                           (AutomatonT p q inp _ _ Nothing _ _) -> let chan = debugInd ins inp "translateFSM 2"
                                                                                                       col = getITransColor net x comp chan
                                                                                                   in transitionITemplate net comp chan col p q fsmind
                                                           (AutomatonT p q inp _ _ (Just outp) _ _) -> case rind of
                                                                                                         Just rind' -> if (rind' == inp)
                                                                                                                       then let ochan = debugInd outs outp "translateFSM 3"
                                                                                                                                ocol = getOTransColor net x
                                                                                                                            in transitionOTemplate net comp ochan ocol p q fsmind
                                                                                                                       else let ichan = debugInd ins inp "translateFSM 4"
                                                                                                                                icol = getITransColor net x comp ichan
                                                                                                                                ochan = debugInd outs outp "translateFSM 5"
                                                                                                                                ocol = getOTransColor net x
                                                                                                                            in transitionIOTemplate net comp ichan icol ochan ocol p q fsmind
                                                                                                         Nothing -> let ichan = debugInd ins inp "translateFSM 6"
                                                                                                                        icol = getITransColor net x comp ichan
                                                                                                                        ochan = debugInd outs outp "translateFMS 7"
                                                                                                                        ocol = getOTransColor net x
                                                                                                                    in transitionIOTemplate net comp ichan icol ochan ocol p q fsmind) ts
                                    res = foldr (\(NSpec a b c) (NSpec a' b' c') -> NSpec (a ++ a') (b ++ b') (c ++ c')) (NSpec [] [] []) ([t_init] ++ t_ins ++ t_outs ++ t_state ++ t_trans)
                                in res
    _ -> error "translateFSM: Automaton expected"


makeInputSwitchFuns :: [Color] -> [MFunctionBool]
makeInputSwitchFuns cs = map (\x -> XMatch (color2mfunction x) (XVar 0)) cs


makeInputSwitch :: ColoredNetwork -> ComponentID -> ChannelID -> Int -> (XComponent T.Text)
makeInputSwitch net comp chan fsmind = let --(ColorSet cols) = getColorSet net chan
                                           --cols' = S.toList cols
                                           cols' = getInTypes net comp chan
                                           --fsmind = getFSMIndex net comp
                                           funs = makeInputSwitchFuns cols'
                                       in if (L.length cols' == 1)
                                          then error "makeInputSwitch: a switch can not have one output channel"
                                          else (Switch (inpCompName "sw" fsmind (channelIDtoInt chan) Nothing) funs)


filterInColors :: ColoredNetwork -> ComponentID -> ChannelID -> [Color]
filterInColors net comp chan = case (getComponent net comp) of
                                 (Automaton _ _ _ _ trans _) -> let trans' = filter (\(AutomatonT _ _ inport _ _ _ _ _) -> inport == (channelIDtoInt chan)) trans
                                                                    funs = map (\(AutomatonT _ _ _ fun _ _ _ _) -> fun) trans'
                                                                    funs' = map (\(XMatch x _) -> x) funs
                                                                    cols = map (\x -> eval (makeVArguments []) x) funs'
                                                                in cols
                                 _ -> error "filterColors: Automaton expected"


getRedundantInpID :: ColoredNetwork -> ComponentID -> Maybe Int
getRedundantInpID net comp = case (getComponent net comp) of
                               (Automaton _ _ _ _ _ _) -> let ins = getInChannels net comp
                                                              --res = filter (\x -> (debugInd (T.unpack (getName (getChannel net x))) 0 "getRedundantInpID 1") == 'M') ins
                                                              res = filter (\x -> let (ColorSet cols) = getColorSet net x in if (S.member (eval (makeVArguments []) (XChoice (T.pack "const") (Left (XConcat HM.empty)))) cols) then True else False) ins
                                                          in if (L.length res > 0) then Just (debugFromJust (L.elemIndex (debugInd res 0 "getRedundantInpID 2") ins) "getRedundantID") else Nothing
                               _ -> Nothing

countInpColors :: ColoredNetwork -> ChannelID -> Int
countInpColors net chan = let (ColorSet cols) = getColorSet net chan in S.size cols


countInputTrans :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int
countInputTrans net comp chan col = case (getComponent net comp) of
                                      (Automaton _ _ _ _ trans _) -> let rinp = getRedundantInpID net comp
                                                                         ins = getInChannels net comp
                                                                         trans' = case rinp of
                                                                                    Just rinp' -> filter (\(AutomatonT _ _ inport _ _ _ _ _) -> (inport /= rinp') && (inport == (debugFromJust (L.elemIndex chan ins) "countInputTrans 1"))) trans
                                                                                    Nothing -> filter (\(AutomatonT _ _ inport _ _ _ _ _) -> (inport == (debugFromJust (L.elemIndex chan ins) "countInputTrans 2"))) trans
                                                                         res = filter (\(AutomatonT _ _ _ infun _ _ _ _) -> (eval (makeVArguments []) (getLeftMatch infun) == col)) trans'
                                                                     in L.length res
                                      _ -> error "countInputTrans: Automaton expected"

countIncomingTrans :: ColoredNetwork -> ComponentID -> Int -> Int
countIncomingTrans net comp q = case (getComponent net comp) of
                                  (Automaton _ _ _ _ ts _) -> L.length $ filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') ts
                                  _ -> error "countIncomingTrans: Automaton expected"

countOutgoingTrans :: ColoredNetwork -> ComponentID -> Int -> Int
countOutgoingTrans net comp p = case (getComponent net comp) of
                                  (Automaton _ _ _ _ ts _) -> L.length $ filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') ts
                                  _ -> error "countIncomingTrans: Automaton expected"

getTransInIndex :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> AutomatonTransition -> Int
getTransInIndex net comp chan col t = case (getComponent net comp) of
                                        (Automaton _ _ _ _ trans _) -> let rinp = getRedundantInpID net comp
                                                                           ins = getInChannels net comp
                                                                           trans' = case rinp of
                                                                                      Just rinp' -> filter (\(AutomatonT _ _ inport _ _ _ _ _) -> (inport /= rinp') && (inport == (debugFromJust (L.elemIndex chan ins) "getTransInIndex 1"))) trans
                                                                                      Nothing -> filter (\(AutomatonT _ _ inport _ _ _ _ _) -> (inport == (debugFromJust (L.elemIndex chan ins) "getTransInIndex 2"))) trans
                                                                           res = filter (\(AutomatonT _ _ _ infun _ _ _ _) -> (eval (makeVArguments []) (getLeftMatch infun) == col)) trans'
                                                                       in debugFromJust (L.elemIndex t res) "getTransInIndex 3"
                                        _ -> error "countInputTrans: Automaton expected"

countOutputTrans :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int
countOutputTrans net comp chan col = case (getComponent net comp) of
                                       (Automaton _ _ _ _ trans _) -> let outs = getOutChannels net comp
                                                                          trans' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> outport /= Nothing) trans
                                                                          trans'' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> (debugFromJust outport "countOutputTrans 1") == (debugFromJust (L.elemIndex chan outs) "countOutputTrans 2")) trans'
                                                                          res = filter (\(AutomatonT _ _ _ _ _ _ outfun _) -> (eval (makeVArguments []) (debugFromJust outfun "countOutputTrans 3")) == col) trans''
                                                                      in L.length res
                                       _ -> error "countOutputTrans: Automaton expected"

getTransOutIndex :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> AutomatonTransition -> Int
getTransOutIndex net comp chan col t = case (getComponent net comp) of
                                         (Automaton _ _ _ _ trans _) -> let outs = getOutChannels net comp
                                                                            trans' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> outport /= Nothing) trans
                                                                            trans'' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> (debugFromJust outport "getTransOutIndex 1") == (debugFromJust (L.elemIndex chan outs) "getTransOutIndex 2")) trans'
                                                                            res = filter (\(AutomatonT _ _ _ _ _ _ outfun _) -> (eval (makeVArguments []) (debugFromJust outfun "getTransOutIndex 3")) == col) trans''
                                                                        in debugFromJust (L.elemIndex t res) "getTransOutIndex 4"

existsSelfLoop :: [AutomatonTransition] -> Int -> Bool
existsSelfLoop trans s = let trans' = filter (\(AutomatonT p q _ _ _ _ _ _) -> p == s && p == q) trans
                         in L.length trans' > 0

getFSMIndex :: ColoredNetwork -> ComponentID -> Int
getFSMIndex net comp = case (getComponent net comp) of
                         (Automaton _ _ _ _ _ _) -> debugFromJust (L.elemIndex comp $ getFSMIDs net) "getFSMIndex"
                         _ -> error "getAutomatonIndex: Automaton expected"


getCompChans :: [XComponent T.Text] -> [XChannel T.Text] -> [(XComponent T.Text,[XChannel T.Text])]
getCompChans [] _ = []
getCompChans _ [] = []
getCompChans (x:xs) chans = ((x,take 3 chans):(getCompChans xs (drop 2 chans)))


evens (x:xs) = x:odds xs
evens _ = []

odds (_:xs) = evens xs
odds _ = []

{- **************************** -}

{- ******* Templates ******* -}

inputTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
inputTemplate net comp chan fsmind = case (getComponent net comp) of
                                (Automaton _ _ _ _ _ _) -> if (L.elem chan (getInChannels net comp))
                                                           then let --(ColorSet cols) = getColorSet net chan
                                                                    --cols' = S.toList cols
                                                                    cols' = getInTypes net comp chan
                                                                    --fsmind = getFSMIndex net comp
                                                                    switch = if (L.length cols' > 1)
                                                                             then [makeInputSwitch net comp chan fsmind]
                                                                             else []
                                                                    lbs = map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                     then [(LoadBalancer (inpCompName "lb" fsmind (channelIDtoInt chan) (Just $ debugFromJust (L.elemIndex x cols') "InputTemplate 1")))]
                                                                                     else if (countInputTrans net comp chan x) == 0
                                                                                          then [(DeadSink (inpCompName "ds" fsmind (channelIDtoInt chan) (Just $ debugFromJust (L.elemIndex x cols') "InputTemplate 2")))]
                                                                                          else []) cols'
                                                                    chans = if (L.length cols' > 1)
                                                                            then L.concat (map (\x -> [(Channel (inpChanName "sw" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex x cols') "InputTemplate 3") Nothing))]) cols')
                                                                            else []
                                                                    chans' = L.concat (map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                                  then [(Channel (inpChanName "lb" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex x cols') "InputTemplate 4") (Just i))) | i <- [0..((countInputTrans net comp chan x) - 1)]]
                                                                                                  else []) cols')
                                                                    lbs' = filter (\w -> case w of (DeadSink _) -> False; _ -> True) (L.concat lbs)
                                                                    ports = if (L.length cols' > 1)
                                                                            then [(channelName $ fst $ getChannel net chan,inpCompName "sw" fsmind (channelIDtoInt chan) Nothing)]
                                                                            else if (L.length lbs' > 0)
                                                                                 then [(channelName $ fst $ getChannel net chan,inpCompName "lb" fsmind (channelIDtoInt chan) (Just 0))]
                                                                                 else []
                                                                    ports' = if (L.length cols' > 1)
                                                                             then L.concat (map (\x -> [(inpCompName "sw" fsmind (channelIDtoInt chan) Nothing,inpChanName "sw" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex x cols') "InputTemplate 5") Nothing)]) cols')
                                                                             else []
                                                                    ports'' = L.concat (map (\x -> if (L.length cols' > 1) && (countInputTrans net comp chan x) > 1
                                                                                                   then [(inpChanName "sw" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex x cols') "InputTemplate 6") Nothing,inpCompName "lb" fsmind (channelIDtoInt chan) (Just $ debugFromJust (L.elemIndex x cols') "InputTemplate 7"))]
                                                                                                   else if (L.length cols' > 1) && (countInputTrans net comp chan x) == 0
                                                                                                        then [(inpChanName "sw" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex x cols') "InputTemplate 8") Nothing,inpCompName "ds" fsmind (channelIDtoInt chan) (Just $ debugFromJust (L.elemIndex x cols') "InputTemplate 9"))]
                                                                                                        else []) cols')
                                                                    ports''' = L.concat (map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                                    then [(inpCompName "lb" fsmind (channelIDtoInt chan) (Just $ debugFromJust (L.elemIndex x cols') "InputTemplate 10"),inpChanName "lb" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex x cols') "InputTemplate 11") (Just i)) | i <- [0..((countInputTrans net comp chan x) - 1)]]
                                                                                                    else []) cols')
                                                                in NSpec (switch ++ (L.concat lbs)) (chans ++ chans') (ports ++ ports' ++ ports'' ++ ports''')
                                                           else error "inputTemplate: The given channel is not an input channel of the given automaton"
                                _ -> error "inputTemplate: Automaton expected"


transitionITemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
transitionITemplate net comp chan col p q fsmind = case (getComponent net comp) of
                                              (Automaton _ _ _ _ t _) -> let --fsmind = getFSMIndex net comp
                                                                             --(ColorSet cols) = getColorSet net chan
                                                                             --cols' = S.toList cols
                                                                             cols' = getInTypes net comp chan
                                                                             ins = getInChannels net comp
                                                                             t' = debugInd (filter (\(AutomatonT p' q' inport infun _ outport _ _) -> outport == Nothing && p == p' && q == q' && ((debugInd ins inport "transitionITemplate 1") == chan) && (eval (makeVArguments []) (getLeftMatch infun) == col)) t) 0 "transitionITemplate 2"
                                                                             t''' = if (filter (\(AutomatonT p' q' inport infun _ outport _ _) -> ((debugInd ins inport "transitionITemplate 3") == chan) &&
                                                                                                                                            (eval (makeVArguments []) (getLeftMatch infun)) == col) t) == []
                                                                                    then error "transitionIOTemplate: Error while computing t'''"
                                                                                    else (filter (\(AutomatonT p' q' inport infun _ _ _ _) -> ((debugInd ins inport "transitionITemplate 4") == chan) && (eval (makeVArguments []) (getLeftMatch infun) == col)) t)
                                                                             ind = debugFromJust (L.elemIndex t' t''') "transitionITemplate 1"
                                                                             outs = getInputTemplateOuts net comp chan col fsmind
                                                                             o = debugInd outs ind "transitionITemplate 5"
                                                                             incoming = filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') t
                                                                             inind = debugFromJust (L.elemIndex t' incoming) "transitionITemplate 2"
                                                                             outgoing = filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') t
                                                                             outind = debugFromJust (L.elemIndex t' outgoing) "transitionITemplate 3"
                                                                             sins = getStateTemplateIns net comp q fsmind
                                                                             souts = getStateTemplateOuts net comp p fsmind
                                                                             comps = [ControlJoin (transCompName "jn" fsmind p q (Just (channelIDtoInt chan,debugFromJust (L.elemIndex col cols') "transitionITemplate 4")) Nothing)]
                                                                             ports = [(debugInd souts outind "transitionITemplate 6",transCompName "jn" fsmind p q (Just (channelIDtoInt chan,debugFromJust (L.elemIndex col cols') "transitionITemplate 6")) Nothing),(o,transCompName "jn" fsmind p q (Just (channelIDtoInt chan,debugFromJust (L.elemIndex col cols') "transitionITemplate 7")) Nothing),(transCompName "jn" fsmind p q (Just (channelIDtoInt chan,debugFromJust (L.elemIndex col cols') "transitionITemplate 8")) Nothing,debugInd sins inind "transitionITemplate 7")]
                                                                             in {-if (channelIDtoInt chan == 9)
                                                                                then error $ show (outs,t''',col)
                                                                                else-} NSpec comps [] ports
                                              _ -> error "transitionITemplate: Automaton expected"


outputTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
outputTemplate net comp chan fsmind = case (getComponent net comp) of
                                 (Automaton _ _ _ _ _ _) -> if (L.elem chan (getOutChannels net comp))
                                                            then let --fsmind = getFSMIndex net comp
                                                                     --(ColorSet cols) = getColorSet net chan
                                                                     --cols' = S.toList cols
                                                                     cols' = getOutTypes net comp chan
                                                                     nins = foldr (\a b -> a + b) 0 (map (\x -> countOutputTrans net comp chan x) cols')
                                                                     comps = if nins > 1
                                                                             then [Merge (outCompName "mrg" fsmind (channelIDtoInt chan) i) | i <- [0..(nins-2)]]
                                                                             else []
                                                                     chans = if nins > 1
                                                                             then [Channel (outChanName "mrg" fsmind (channelIDtoInt chan) i) | i <- [0..(((L.length comps) * 2) - 1)]]
                                                                             else []
                                                                     chans' = (fst (getChannel net chan):chans)
                                                                     compchans = getCompChans comps chans'
                                                                     --ports = L.concat (map (\(x,ys) -> [((getName (ys !! 0)),(getName x)),((getName x),(getName (ys !! 1))),((getName x),(getName (ys !! 2)))]) compchans)
                                                                     ports = L.concat (map (\(x,ys) -> [(getName (debugInd ys 1 "outputTemplate 1"),getName x),(getName (debugInd ys 2 "outputTemplate 2"),getName x),(getName x,getName (debugInd ys 0 "outputTemplate 3"))]) compchans)
                                                                 in NSpec comps chans ports
                                                            else error "outputTemplate: The given channel is not an output channel of the given automaton"
                                 _ -> error "outputTemplate: Automaton expected"


{-
countOutputTrans :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int
countOutputTrans net comp chan col = case (getComponent net comp) of
                                       (Automaton _ _ _ _ trans _) -> let outs = getOutChannels net comp
                                                                          trans' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> outport /= Nothing) trans
                                                                          trans'' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> (MB.fromJust outport) == (MB.fromJust $ L.elemIndex chan outs)) trans'
                                                                          res = filter (\(AutomatonT _ _ _ _ _ _ outfun _) -> (eval (makeVArguments []) (MB.fromJust outfun)) == col) trans''
                                                                      in L.length res
                                       _ -> error "countOutputTrans: Automaton expected"
                                       -}
transitionIOTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> ChannelID -> Color -> Int -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
transitionIOTemplate net comp ichan icol ochan ocol p q fsmind =
  case (getComponent net comp) of
    (Automaton _ _ _ _ t _) -> let --fsmind = getFSMIndex net comp
                                   --(ColorSet icols) = getColorSet net ichan
                                   --icols' = S.toList icols
                                   icols' = getInTypes net comp ichan
                                   --(ColorSet ocols) = getColorSet net ochan
                                   --ocols' = S.toList ocols
                                   ocols' = getOutTypes net comp ochan
                                   inds = map (\x -> countOutputTrans net comp ochan x) ocols'
                                   {-t' = (filter (\(AutomatonT p' q' _ _ _ outport outfun _) -> p == p' &&
                                                                                               q == q' &&
                                                                                               (case outport of Just outport' -> (outputs !! outport') == ochan; _ -> True) &&
                                                                                               ((eval (makeVArguments []) (MB.fromJust outfun)) == ocol)) t) !! 0-}
                                   ind = debugFromJust (L.elemIndex t'' t_out) "transitionIOTemplate 1"
                                   colind = debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 2"
                                   inputs = getInChannels net comp
                                   outputs = getOutChannels net comp
                                   ins = getOutputTemplateIns net comp ochan fsmind
                                   i = debugInd ins ((foldr (\a b -> a + b) 0 (L.take colind inds)) + ind){-(ind * (L.length ocols') + colind)-} ("transitionIOTemplate 1" ++ "," ++ show (colind * (L.length ocols') + (inds !! colind)) ++ "," ++ show colind ++ "," ++ show ins ++ "," ++ show ocols' ++ "," ++ show inds)
                                   t'' = if (filter (\(AutomatonT p' q' inport infun _ outport outfun _) -> p == p' && --transitions from p to q that involve x(d)
                                                                                                            q == q' &&
                                                                                                            (case outport of Just outport' -> (debugInd outputs outport' "transitionIOTemplate 2") == ochan; _ -> False) &&
                                                                                                            ((eval (makeVArguments []) (debugFromJust outfun "transitionIOTemplate 3")) == ocol) &&
                                                                                                            ((debugInd inputs inport "transitionIOTemplate 3") == ichan) &&
                                                                                                            (eval (makeVArguments []) (getLeftMatch infun)) == icol) t) == []
                                         then error "transitionIOTemplate: Error while computing t''"
                                         else debugInd (filter (\(AutomatonT p' q' inport infun _ outport outfun _) -> p == p' &&
                                                                                                              q == q' &&
                                                                                                              (case outport of Just outport' -> (debugInd outputs outport' "transitionIOTemplate 4") == ochan; _ -> False) &&
                                                                                                              ((eval (makeVArguments []) (debugFromJust outfun "transitionIOTemplate 4")) == ocol) &&
                                                                                                              ((debugInd inputs inport "transitionIOTemplate 5") == ichan) &&
                                                                                                              (eval (makeVArguments []) (getLeftMatch infun)) == icol) t) 0 "transitionIOTemplate 6"
                                   t_in = if (filter (\(AutomatonT p' q' inport infun _ outport outfun _) -> ((debugInd inputs inport "transitionIOTemplate 7") == ichan) &&
                                                                                                             --(case outport of Just outport' -> (outputs !! outport') == ochan; _ -> True) &&
                                                                                                             --((eval (makeVArguments []) (MB.fromJust outfun)) == ocol) &&
                                                                                                             (eval (makeVArguments []) (getLeftMatch infun)) == icol) t) == []
                                          then error "transitionIOTemplate: Error while computing t_in"
                                          else (filter (\(AutomatonT p' q' inport infun _ outport outfun _) -> ((debugInd inputs inport "transitionIOTemplate 8") == ichan) &&
                                                                                                               --(case outport of Just outport' -> (outputs !! outport') == ochan; _ -> True) &&
                                                                                                               --((eval (makeVArguments []) (MB.fromJust outfun)) == ocol) &&
                                                                                                               (eval (makeVArguments []) (getLeftMatch infun)) == icol) t)
                                   t_out = if (filter (\(AutomatonT p' q' inport infun _ outport outfun _) -> --((inputs !! inport) == ichan) &&
                                                                                                              (case outport of Just outport' -> (debugInd outputs outport' "transitionIOTemplate 9") == ochan; _ -> False) &&
                                                                                                              ((eval (makeVArguments []) (debugFromJust outfun "transitionIOTemplate 5")) == ocol) {-&&
                                                                                                              (eval (makeVArguments (L.replicate (L.length inputs) icol)) infun)-}) t) == []
                                           then error "transitionIOTemplate: Error while computing t_out"
                                           else (filter (\(AutomatonT p' q' inport infun _ outport outfun _) -> --((inputs !! inport) == ichan) &&
                                                                                                                (case outport of Just outport' -> (debugInd outputs outport' "transitionIOTemplate 10") == ochan; _ -> False) &&
                                                                                                                ((eval (makeVArguments []) (debugFromJust outfun "transitionIOTemplate 6")) == ocol) {-&&
                                                                                                                (eval (makeVArguments (L.replicate (L.length inputs) icol)) infun)-}) t)
                                   ind' = debugFromJust (L.elemIndex t'' t_in) "transitionIOTemplate 7"
                                   outs' = getInputTemplateOuts net comp ichan icol fsmind
                                   o = debugInd outs' ind' "transitionIOTemplate 11" --input of the output template
                                   incoming = filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') t
                                   inind = debugFromJust (L.elemIndex t'' incoming) "transitionIOTemplate 8"
                                   outgoing = filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') t
                                   outind = debugFromJust (L.elemIndex t'' outgoing) "transitionIOTemplate 9"
                                   sins = getStateTemplateIns net comp q fsmind--input of the next state
                                   souts = getStateTemplateOuts net comp p fsmind --output of the previous state
                                   comps = [Fork (transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 10")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 11"))),
                                            Function (transCompName "fun" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 12")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 13"))) (color2mfunction ocol) (ColorSet (S.singleton ocol)),
                                            ControlJoin (transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 14")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 15")))]
                                   chans = [Channel (transChanName "frk_fun" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 16")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 17"))),
                                            Channel (transChanName "jn_frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))))]
                                   ports = [
                                            (debugInd souts outind "transitionIOTemplate 12",transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 18")) (Just (channelIDtoInt ochan,debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 19"))),
                                            (o,transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 20")) (Just (channelIDtoInt ochan,debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 21"))),
                                            (transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 22")) (Just (channelIDtoInt ochan,debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 23")),transChanName "jn_frk" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 24")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 25"))),
                                            (transChanName "jn_frk" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 26")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 27")),transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 28")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 29"))),
                                            (transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 30")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 31")), debugInd sins inind "transitionIOTemplate 14"),
                                            (transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 32")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 33")), transChanName "frk_fun" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 34")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 35"))),

                                            (transChanName "frk_fun" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 36")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 37")),transCompName "fun" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 38")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 39"))),
                                            (transCompName "fun" fsmind p q (Just (channelIDtoInt ichan, debugFromJust (L.elemIndex icol icols') "transitionIOTemplate 40")) (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionIOTemplate 41")),i)]
                               in if (L.elemIndex ocol ocols') == Nothing
                                  then error $ show (ocol,ocols')
                                  else NSpec comps chans ports
    _ -> error "transitionOTemplate: Automaton expected"


transitionOTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
transitionOTemplate net comp ochan ocol p q fsmind =
  case (getComponent net comp) of
    (Automaton _ _ _ _ t _) -> let --fsmind = getFSMIndex net comp
                                   --(ColorSet ocols) = getColorSet net ochan
                                   --ocols' = S.toList ocols
                                   ocols' = getOutTypes net comp ochan
                                   outputs = getOutChannels net comp
                                   t' = debugInd (filter (\(AutomatonT p' q' _ _ _ outport outfun _) -> p == p' &&
                                                                                              q == q' &&
                                                                                              (case outport of Just outport' -> (debugInd outputs outport' "transitionOTemplate 1") == ochan; _ -> False) &&
                                                                                              ((eval (makeVArguments []) (debugFromJust outfun "transitionOTemplate 1")) == ocol)) t) 0 "transitionOTemplate 2"
                                   t_out = if (filter (\(AutomatonT p' q' _ _ _ outport outfun _) -> --((inputs !! inport) == ichan) &&
                                                                                                     (case outport of Just outport' -> (debugInd outputs outport' "transitionOTemplate 3") == ochan; _ -> False) &&
                                                                                                     ((eval (makeVArguments []) (debugFromJust outfun "transitionOTemplate 2")) == ocol)) t) == []
                                           then error "transitionOTemplate: Error while computing t_out"
                                           else (filter (\(AutomatonT p' q' _ _ _ outport outfun _) -> --((inputs !! inport) == ichan) &&
                                                                                                       (case outport of Just outport' -> (debugInd outputs outport' "transitionOTemplate 4") == ochan; _ -> False) &&
                                                                                                       ((eval (makeVArguments []) (debugFromJust outfun "transitionOTemplate 3")) == ocol)) t)
                                   ind = debugFromJust (L.elemIndex t' t_out) "transitionOTemplate 4"
                                   colind = debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 5"
                                   ins = getOutputTemplateIns net comp ochan fsmind
                                   inds = map (\x -> countOutputTrans net comp ochan x) ocols'
                                   i = debugInd ins ((foldr (\a b -> a + b) 0 (L.take colind inds)) + ind) "transitionOTemplate 5"
                                   incoming = filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') t
                                   inind = debugFromJust (L.elemIndex t' incoming) "transitionOTemplate 6"
                                   outgoing = filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') t
                                   outind = debugFromJust (L.elemIndex t' outgoing) "transitionOTemplate 7"
                                   sins = getStateTemplateIns net comp q fsmind
                                   souts = getStateTemplateOuts net comp p fsmind
                                   comps = [Fork (transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemaplte 8"))),
                                            Function (transCompName "fun" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust(L.elemIndex ocol ocols') "transitionOTemplate 9"))) (color2mfunction ocol) (ColorSet (S.singleton ocol))]
                                   chans = [Channel (transChanName "frk_fun" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 10")))]
                                   ports = [
                                            (debugInd souts outind "transitionOTemplate 6", transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 11"))),
                                            (transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 12")), debugInd sins inind "transitionOTemplate 7"),
                                            (transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 13")), transChanName "frk_fun" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 14"))),
                                            (transChanName "frk_fun" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 15")),transCompName "fun" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 16"))),
                                            (transCompName "fun" fsmind p q Nothing (Just (channelIDtoInt ochan, debugFromJust (L.elemIndex ocol ocols') "transitionOTemplate 17")),i)]
                               in NSpec comps chans ports
    _ -> error "transitionOTemplate: Automaton expected"


initTemplate :: ColoredNetwork -> ComponentID -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
initTemplate net comp fsmind = case (getComponent net comp) of
                          (Automaton _ _ _ _ _ _) -> let --fsmind = getFSMIndex net comp
                                                         sins = getStateTemplateIns net comp 0 fsmind
                                                         comps = [
                                                                  PatientSource (initCompName "src" fsmind) token,
                                                                  Fork (initCompName "frk" fsmind),
                                                                  Queue (initCompName "q" fsmind) 1,
                                                                  DeadSink (initCompName "snk" fsmind)
                                                                  ]
                                                         chans = [
                                                                  Channel (initChanName "src_frk" fsmind),
                                                                  Channel (initChanName "frk_q" fsmind),
                                                                  Channel (initChanName "q_snk" fsmind)
                                                                  ]
                                                         ports = [
                                                                  (initCompName "src" fsmind,initChanName "src_frk" fsmind),
                                                                  (initChanName "src_frk" fsmind,initCompName "frk" fsmind),
                                                                  (initCompName "frk" fsmind,initChanName "frk_q" fsmind),
                                                                  (initCompName "frk" fsmind,L.last sins),
                                                                  (initChanName "frk_q" fsmind,initCompName "q" fsmind),
                                                                  (initCompName "q" fsmind,initChanName "q_snk" fsmind),
                                                                  (initChanName "q_snk" fsmind,initCompName "snk" fsmind)
                                                                  ]
                                                     in NSpec comps chans ports
                          _ -> error "initTemplate: Automaton expected"

--getCompChans :: [XComponent T.Text] -> [XChannel T.Text] -> [(XComponent T.Text,[XChannel T.Text])]
stateTemplate :: ColoredNetwork -> ComponentID -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
stateTemplate net comp p fsmind = case (getComponent net comp) of
                             (Automaton _ _ _ _ ts _) -> let --fsmind = getFSMIndex net comp
                                                             sl = existsSelfLoop ts p
                                                             k = if sl then 2 else 1
                                                             ot = countOutgoingTrans net comp p
                                                             it = if p == 0
                                                                  then (countIncomingTrans net comp p) + 1
                                                                  else (countIncomingTrans net comp p)
                                                             comps = [Queue (stateCompName "q" fsmind p Nothing) k]
                                                             comps_lb = if ot > 1
                                                                        then [LoadBalancer (stateCompName "lb" fsmind p Nothing)]
                                                                        else []
                                                             comps_mrg = if it > 1
                                                                         then [Merge (stateCompName "mrg" fsmind p (Just i)) | i <- [0..it-2]]
                                                                         else []
                                                             chans = if ot > 1
                                                                     then (Channel (stateChanName "q_lb" fsmind p Nothing):[Channel (stateChanName "lb" fsmind p (Just i)) | i <- [0..ot-1]])
                                                                     else [Channel (stateChanName "q_out" fsmind p Nothing)]
                                                             chans' = if it > 1
                                                                      then [Channel (stateChanName "mrg" fsmind p (Just i)) | i <- [0..((L.length comps_mrg) * 2)]]
                                                                      else [Channel (stateChanName "q_in" fsmind p Nothing)]
                                                             compchans = getCompChans comps_mrg chans'
                                                             ports = if ot > 1
                                                                     then [
                                                                           (getName (debugInd comps 0 "stateTemplate 1"),getName (debugInd chans 0 "stateTemplate 2")),
                                                                           (getName (debugInd chans 0 "stateTemplate 3"),getName (debugInd comps_lb 0 "stateTemplate 4"))
                                                                           ] ++
                                                                           [(stateCompName "lb" fsmind p Nothing,stateChanName "lb" fsmind p (Just i)) | i <- [0..ot-1]]
                                                                     else [(getName (debugInd comps 0 "stateTemplate 5"),getName (debugInd chans 0 "stateTemplate 6"))]
                                                             ports' = if it > 1
                                                                      then ((stateChanName "mrg" fsmind p (Just 0),stateCompName "q" fsmind p Nothing):(L.concat (map (\(x,ys) -> [(getName (debugInd ys 1 "stateTemplate 7"),getName x),(getName (debugInd ys 2 "stateTemplate 8"),getName x),(getName x,getName (debugInd ys 0 "stateTemplate 9"))]) compchans)))
                                                                      else [(stateChanName "q_in" fsmind p Nothing,stateCompName "q" fsmind p Nothing)]
                                                         in NSpec (comps ++ comps_lb ++ comps_mrg) (chans ++ chans') (ports ++ ports')
                             _ -> error "stateTemplate: Automaton expected"

{- **************************** -}

{- ******* Component and channel naming functions ******* -}

--takes component type as a string and three indices
inpCompName :: String -> Int -> Int -> Maybe Int -> T.Text
inpCompName comptype fsmind chanind colind = case colind of
                                               Nothing -> T.pack (comptype ++ "_inp_" ++ show fsmind ++ "_" ++ show chanind)
                                               Just ind -> T.pack (comptype ++ "_inp_" ++ show fsmind ++ "_" ++ show chanind ++ "_" ++ show ind)

--takes a name frefix as a string, three indices and one optional index
inpChanName :: String -> Int -> Int -> Int -> Maybe Int -> T.Text
inpChanName nameprefix fsmind chanind colind ind = case ind of
                                                     Nothing -> T.pack ("chan_" ++ nameprefix ++ "_inp_" ++ show fsmind ++ "_" ++ show chanind ++ "_" ++ show colind)
                                                     Just ind' -> T.pack ("chan_" ++ nameprefix ++ "_inp_" ++ show fsmind ++ "_" ++ show chanind ++ "_" ++ show colind ++ "_" ++ show ind')

outCompName :: String -> Int -> Int -> Int -> T.Text
outCompName comptype fsmind chanind ind = T.pack (comptype ++ "_" ++ show fsmind ++ "_out_" ++ show chanind ++ "_" ++ show ind)

outChanName :: String -> Int -> Int -> Int -> T.Text
outChanName nameprefix fsmind chanind ind = T.pack ("chan_" ++ nameprefix ++ "_out_" ++ show fsmind ++ "_" ++ show chanind ++ "_" ++ show ind)

transCompName :: String -> Int -> Int -> Int -> Maybe (Int, Int) -> Maybe (Int, Int) -> T.Text
transCompName comptype fsmind p q Nothing Nothing = error "transCompName: Both input and output channel and color data is absent"
transCompName comptype fsmind p q (Just (chan,col)) Nothing = T.pack (comptype ++ "_trans_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show q ++ "_" ++ show chan ++ "_" ++ show col ++ "__")
transCompName comptype fsmind p q Nothing (Just (chan',col')) = T.pack (comptype ++ "_trans_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show q ++ "__" ++ show chan' ++ "_" ++ show col')
transCompName comptype fsmind p q (Just (chan,col)) (Just (chan',col')) = T.pack (comptype ++ "_trans_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show q ++ "_" ++ show chan ++ "_" ++ show col ++ "_" ++ show chan' ++ "_" ++ show col')

transChanName :: String -> Int -> Int -> Int -> Maybe (Int, Int) -> Maybe (Int, Int) -> T.Text
transChanName nameprefix fsmind p q Nothing Nothing = error "transChanName: Both input and output channel and color data is absent"
transChanName nameprefix fsmind p q (Just (chan,col)) Nothing = T.pack ("chan_" ++ nameprefix ++ "_trans_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show q ++ "_" ++ show chan ++ "_" ++ show col ++ "__")
transChanName nameprefix fsmind p q Nothing (Just (chan',col')) = T.pack ("chan_" ++ nameprefix ++ "_trans_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show q ++ "__" ++ show chan' ++ "_" ++ show col')
transChanName nameprefix fsmind p q (Just (chan,col)) (Just (chan',col')) = T.pack ("chan_" ++ nameprefix ++ "_trans_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show q ++ "_" ++ show chan ++ "_" ++ show col ++ "_" ++ show chan' ++ "_" ++ show col')

initCompName :: String -> Int -> T.Text
initCompName comptype fsmind = T.pack (comptype ++ "_" ++ show fsmind ++ "_init")

initChanName :: String -> Int -> T.Text
initChanName nameprefix fsmind = T.pack ("chan_" ++ nameprefix ++ "_" ++ show fsmind ++ "_init")

stateCompName :: String -> Int -> Int -> Maybe Int -> T.Text
stateCompName comptype fsmind p Nothing = T.pack (comptype ++ "_state_" ++ show fsmind ++ "_" ++ show p)
stateCompName comptype fsmind p (Just i) = T.pack (comptype ++ "_state_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show i)

stateChanName :: String -> Int -> Int -> Maybe Int -> T.Text
stateChanName nameprefix fsmind p Nothing = T.pack ("chan_" ++ nameprefix ++ "_state_" ++ show fsmind ++ "_" ++ show p)
stateChanName nameprefix fsmind p (Just i) = T.pack ("chan_" ++ nameprefix ++ "_state_" ++ show fsmind ++ "_" ++ show p ++ "_" ++ show i)
{- **************************** -}

{- ******* Inputs and outputs of templates ******* -}

getInputTemplateOuts :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int -> [T.Text]
getInputTemplateOuts net comp chan col fsmind = let --(ColorSet cols) = getColorSet net chan
                                                    --cols' = S.toList cols
                                                    cols' = getInTypes net comp chan
                                                    trans = countInputTrans net comp chan col
                                                    --fsmind = getFSMIndex net comp
                                                    res = if ((L.length cols') == 1) && (trans == 1)
                                                          then [(channelName $ fst $ getChannel net chan)]
                                                          else if trans > 1
                                                               then [inpChanName "lb" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex col cols') "getInputTemplateOuts 1") (Just i) | i <- [0..trans-1]]
                                                               else [inpChanName "sw" fsmind (channelIDtoInt chan) (debugFromJust (L.elemIndex col cols') "getInputTemplateOuts 2") Nothing]
                                                in res


getOutputTemplateIns :: ColoredNetwork -> ComponentID -> ChannelID -> Int -> [T.Text]
getOutputTemplateIns net comp chan fsmind = case (getComponent net comp) of
                                       (Automaton _ _ _ _ t _) -> let --fsmind = getFSMIndex net comp
                                                                      --(ColorSet cols) = getColorSet net chan
                                                                      --cols' = S.toList cols
                                                                      cols' = getOutTypes net comp chan
                                                                      nins = foldr (\a b -> a + b) 0 (map (\x -> countOutputTrans net comp chan x) cols')
                                                                      comps = if nins > 1
                                                                              then [Merge (outCompName "mrg" fsmind (channelIDtoInt chan) i)| i <- [0..(nins-2)]]
                                                                              else []
                                                                      chans = if nins > 1
                                                                              then [Channel (outChanName "mrg" fsmind (channelIDtoInt chan) i) | i <- [0..(((L.length comps) * 2) - 1)]]
                                                                              else [fst $ (getChannel net chan)]
                                                                      chans' = if (L.length chans) > 1
                                                                               then L.nub ((evens chans) ++ [L.last chans])
                                                                               else chans
                                                                  in map (\x -> getName x) chans'
                                       _ -> error "getOutputTemplateIns: Automaton expected"

getStateTemplateIns :: ColoredNetwork -> ComponentID -> Int -> Int -> [T.Text]
getStateTemplateIns net comp p fsmind = case (getComponent net comp) of
                                   (Automaton _ _ _ _ _ _) -> let --fsmind = getFSMIndex net comp
                                                                  it = if p == 0
                                                                       then (countIncomingTrans net comp p) + 1
                                                                       else (countIncomingTrans net comp p)
                                                                  chans = if it > 1
                                                                          then [stateChanName "mrg" fsmind p (Just i) | i <- [0..((it - 1) * 2)]]
                                                                          else [stateChanName "q_in" fsmind p Nothing]
                                                              in (odds chans) ++ [L.last chans]
                                   _ -> error "getStateTemplateIns: Automaton expected"

getStateTemplateOuts :: ColoredNetwork -> ComponentID -> Int -> Int -> [T.Text]
getStateTemplateOuts net comp p fsmind = case (getComponent net comp) of
                                    (Automaton _ _ _ _ _ _) -> let --fsmind = getFSMIndex net comp
                                                                   ot = countOutgoingTrans net comp p
                                                                   chans = if ot > 1
                                                                           then [stateChanName "lb" fsmind p (Just i) | i <- [0..ot-1]]
                                                                           else [stateChanName "q_out" fsmind p Nothing]
                                                               in chans
                                    _ -> error "getStateTemplateOuts: Automaton expected"

{- **************************** -}

{- ******* Testing Functions ******* -}

testInpTemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testInpTemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                          inp = (getInChannels net fsm) !! 0
                      in inputTemplate net fsm inp 0

testTransITemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testTransITemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                             inp = (getInChannels net fsm) !! 0
                             (ColorSet cols) = getColorSet net inp
                             col = (S.toList cols) !! 1
                         in transitionITemplate net fsm inp col 0 1 0


testTransIOTemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testTransIOTemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                              inp = (getInChannels net fsm) !! 0
                              (ColorSet cols) = getColorSet net inp
                              col = (S.toList cols) !! 1
                              out = (getOutChannels net fsm) !! 0
                              (ColorSet cols') = getColorSet net out
                              col' = (S.toList cols') !! 0
                          in transitionIOTemplate net fsm inp col out col' 0 1 0


testOutTemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testOutTemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                          out = (getOutChannels net fsm) !! 0
                      in outputTemplate net fsm out 0

testOutTemplateIns :: ColoredNetwork -> [T.Text]
testOutTemplateIns net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                             out = (getOutChannels net fsm) !! 0
                         in getOutputTemplateIns net fsm out 0

testTranslateFSM :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testTranslateFSM net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                       in translateFSM net fsm 0

testReplaceFSM :: ColoredNetwork -> ColoredNetwork
testReplaceFSM net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                     in replaceFSM net fsm 0

testNet :: ColoredNetwork
testNet = channelTypes $ Madl.Network.mkNetwork testSpec


testOutOrder :: ColoredNetwork -> [ChannelID]
testOutOrder net = getOutChannels net (getALoadBalancer net)


test :: String
test = "hey!"

simplifyFSM :: ColoredNetwork -> ColoredNetwork
simplifyFSM x = x

testFSMFuns :: ColoredNetwork -> Color
testFSMFuns net = let fsm = (getAllProcesses net) !! 0
                      trans = (transitions fsm) !! 1
                  in (eval (makeVArguments []) (MB.fromJust $ phi trans))

testFSMFuns1 :: ColoredNetwork -> Bool
testFSMFuns1 net = let fsm = (getAllProcesses net) !! 0
                       trans = (transitions fsm) !! 0
                   in (eval (makeVArguments []) (epsilon trans))

{- **************************** -}
