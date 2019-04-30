module Madl.SimplifyFSM where

import Madl.Base
import Madl.Base.Identifiers
import Madl.Network
import Madl.MsgTypes
import qualified Data.IntMap as IM
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as MB

{- ******* Supplementary functions ******* -}

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
getALoadBalancer net = (filter (\x -> case (getComponent net x) of (LoadBalancer _) -> True; _ -> False) (getComponentIDs net)) !! 0


getFSMIDs :: ColoredNetwork -> [ComponentID]
getFSMIDs net = map (\(x,_) -> x) (getAllProcessesWithID net)


getCompName :: ComponentID -> IM.IntMap (ComponentContext (XComponent T.Text)) -> T.Text
getCompName cid cm = let (_,x,_) = cm IM.! (componentIDtoInt cid)
                     in componentName x


getITransColor :: ColoredNetwork -> AutomatonTransition -> ChannelID -> Color
getITransColor net (AutomatonT _ _ _ infun _ _ _ _) chan = let (ColorSet cols) = getColorSet net chan
                                                               cols' = S.toList cols
                                                               res = (filter (\x -> eval (makeVArguments [x]) infun) cols')
                                                               res' = if res == []
                                                                      then error "getITransColor: Can not derive the color"
                                                                      else res !! 0
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

replaceFSM :: ColoredNetwork -> ComponentID -> ColoredNetwork
replaceFSM net comp = case (getComponent net comp) of
                        (Automaton fsmname _ _ _ _ _) -> let (NSpec comps chans ports) = netToSpec net
                                                             rind = getRedundantInpID net comp
                                                             ins = getInChannels net comp
                                                             chans' = case rind of
                                                                        Just rind' -> filter (\x -> x /= (fst $ getChannel net (ins !! rind'))) chans
                                                                        Nothing -> chans
                                                             comps' = case rind of
                                                                        Just rind' -> filter (\x -> ((getName x) /= fsmname) && (x /= (getComponent net (getInitiator net (ins !! rind'))))) comps
                                                                        Nothing -> filter (\x -> (getName x) /= fsmname) comps
                                                             ports' = case rind of
                                                                        Just rind' -> filter (\(a,b) -> (a /= fsmname) && (b /= fsmname) && (a /= (getName (getComponent net (getInitiator net (ins !! rind'))))) && (b /= (getName (getComponent net (getInitiator net (ins !! rind')))))) ports
                                                                        Nothing -> filter (\(a,b) -> (a /= fsmname) && (b /= fsmname)) ports
                                                             (NSpec fsmcomps fsmchans fsmports) = translateFSM net comp
                                                             spec = (NSpec (comps' ++ fsmcomps) (chans' ++ fsmchans) (ports' ++ fsmports))
                                                         in error $ show spec --channelTypes $ Madl.Network.mkNetwork spec
                        _ -> error "replaceFSM: Automaton expected"


updateNetwork :: ColoredNetwork -> ColoredNetwork
updateNetwork net = updateNetwork' net (getFSMIDs net)
  where updateNetwork' :: ColoredNetwork -> [ComponentID] -> ColoredNetwork
        updateNetwork' net [] = net
        updateNetwork' net (x:xs) = updateNetwork' (replaceFSM net x) xs



translateFSM :: ColoredNetwork -> ComponentID -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
translateFSM net comp =
  case (getComponent net comp) of
    (Automaton _ _ _ n ts _) -> let ins' = getInChannels net comp
                                    outs = getOutChannels net comp
                                    rind = getRedundantInpID net comp
                                    ins = case rind of
                                            Just rind' -> filter (\x -> (ins' !! rind') /= x) ins'
                                            Nothing -> ins'
                                    t_init = initTemplate net comp
                                    t_ins = map (\x -> inputTemplate net comp x) ins
                                    t_outs = map (\x -> outputTemplate net comp x) outs
                                    t_state = map (\x -> stateTemplate net comp x) [0..n-1]
                                    t_trans = map (\x -> case x of
                                                           (AutomatonT p q inp _ _ Nothing _ _) -> let chan = ins !! inp
                                                                                                       col = getITransColor net x chan
                                                                                                   in transitionITemplate net comp chan col p q
                                                           (AutomatonT p q inp _ _ (Just outp) _ _) -> case rind of
                                                                                                         Just rind' -> if (rind' == inp)
                                                                                                                       then let ochan = outs !! outp
                                                                                                                                ocol = getOTransColor net x
                                                                                                                            in transitionOTemplate net comp ochan ocol p q
                                                                                                                       else let ichan = ins !! inp
                                                                                                                                icol = getITransColor net x ichan
                                                                                                                                ochan = outs !! outp
                                                                                                                                ocol = getOTransColor net x
                                                                                                                            in transitionIOTemplate net comp ichan icol ochan ocol p q
                                                                                                         Nothing -> let ichan = ins !! inp
                                                                                                                        icol = getITransColor net x ichan
                                                                                                                        ochan = outs !! outp
                                                                                                                        ocol = getOTransColor net x
                                                                                                                    in transitionIOTemplate net comp ichan icol ochan ocol p q) ts
                                    res = foldr (\(NSpec a b c) (NSpec a' b' c') -> NSpec (a ++ a') (b ++ b') (c ++ c')) (NSpec [] [] []) ([t_init] ++ t_ins ++ t_outs ++ t_state ++ t_trans)
                                in res
    _ -> error "translateFSM: Automaton expected"


makeInputSwitchFuns :: [Color] -> [MFunctionBool]
makeInputSwitchFuns cs = map (\x -> XMatch (color2mfunction x) (XVar 0)) cs


makeInputSwitch :: ColoredNetwork -> ComponentID -> ChannelID -> (XComponent T.Text)
makeInputSwitch net comp chan = let (ColorSet cols) = getColorSet net chan
                                    cols' = S.toList cols
                                    fsmind = getFSMIndex net comp
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
                                                              res = filter (\x -> ((T.unpack (getName (getChannel net x))) !! 0) == 'M') ins
                                                          in if (L.length res > 0) then Just (MB.fromJust (L.elemIndex (res !! 0) ins)) else Nothing
                               _ -> Nothing

countInpColors :: ColoredNetwork -> ChannelID -> Int
countInpColors net chan = let (ColorSet cols) = getColorSet net chan in S.size cols


countInputTrans :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int
countInputTrans net comp chan col = case (getComponent net comp) of
                                      (Automaton _ _ _ _ trans _) -> let rinp = getRedundantInpID net comp
                                                                         ins = getInChannels net comp
                                                                         trans' = case rinp of
                                                                                    Just rinp' -> filter (\(AutomatonT _ _ inport _ _ _ _ _) -> (inport /= rinp') && (inport == (MB.fromJust $ L.elemIndex chan ins))) trans
                                                                                    Nothing -> trans
                                                                         res = filter (\(AutomatonT _ _ _ infun _ _ _ _) -> (eval (makeVArguments [col]) infun)) trans'
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
                                                                                      Just rinp' -> filter (\(AutomatonT _ _ inport _ _ _ _ _) -> (inport /= rinp') && (inport == (MB.fromJust $ L.elemIndex chan ins))) trans
                                                                                      Nothing -> trans
                                                                           res = filter (\(AutomatonT _ _ _ infun _ _ _ _) -> (eval (makeVArguments [col]) infun)) trans'
                                                                       in MB.fromJust $ L.elemIndex t res
                                        _ -> error "countInputTrans: Automaton expected"

countOutputTrans :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int
countOutputTrans net comp chan col = case (getComponent net comp) of
                                       (Automaton _ _ _ _ trans _) -> let outs = getOutChannels net comp
                                                                          trans' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> outport /= Nothing) trans
                                                                          trans'' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> (MB.fromJust outport) == (MB.fromJust $ L.elemIndex chan outs)) trans'
                                                                          res = filter (\(AutomatonT _ _ _ _ _ _ outfun _) -> (eval (makeVArguments []) (MB.fromJust outfun)) == col) trans''
                                                                      in L.length res
                                       _ -> error "countOutputTrans: Automaton expected"

getTransOutIndex :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> AutomatonTransition -> Int
getTransOutIndex net comp chan col t = case (getComponent net comp) of
                                         (Automaton _ _ _ _ trans _) -> let outs = getOutChannels net comp
                                                                            trans' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> outport /= Nothing) trans
                                                                            trans'' = filter (\(AutomatonT _ _ _ _ _ outport _ _) -> (MB.fromJust outport) == (MB.fromJust $ L.elemIndex chan outs)) trans'
                                                                            res = filter (\(AutomatonT _ _ _ _ _ _ outfun _) -> (eval (makeVArguments []) (MB.fromJust outfun)) == col) trans''
                                                                        in MB.fromJust $ L.elemIndex t res

existsSelfLoop :: [AutomatonTransition] -> Int -> Bool
existsSelfLoop trans s = let trans' = filter (\(AutomatonT p q _ _ _ _ _ _) -> p == s && p == q) trans
                         in L.length trans' > 0

getFSMIndex :: ColoredNetwork -> ComponentID -> Int
getFSMIndex net comp = case (getComponent net comp) of
                         (Automaton _ _ _ _ _ _) -> MB.fromJust $ L.elemIndex comp $ getFSMIDs net
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

inputTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
inputTemplate net comp chan = case (getComponent net comp) of
                                (Automaton _ _ _ _ _ _) -> if (L.elem chan (getInChannels net comp))
                                                           then let (ColorSet cols) = getColorSet net chan
                                                                    cols' = S.toList cols
                                                                    fsmind = getFSMIndex net comp
                                                                    switch = if (L.length cols' > 1)
                                                                             then [makeInputSwitch net comp chan]
                                                                             else []
                                                                    lbs = map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                     then [(LoadBalancer (inpCompName "lb" fsmind (channelIDtoInt chan) (Just $ MB.fromJust (L.elemIndex x cols'))))]
                                                                                     else if (countInputTrans net comp chan x) == 0
                                                                                          then [(DeadSink (inpCompName "ds" fsmind (channelIDtoInt chan) (Just $ MB.fromJust (L.elemIndex x cols'))))]
                                                                                          else []) cols'
                                                                    chans = if (L.length cols' > 1)
                                                                            then L.concat (map (\x -> [(Channel (inpChanName "sw" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex x cols')) Nothing))]) cols')
                                                                            else []
                                                                    chans' = L.concat (map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                                  then [(Channel (inpChanName "lb" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex x cols')) (Just i))) | i <- [0..((L.length cols') - 1)]]
                                                                                                  else []) cols')
                                                                    lbs' = filter (\w -> case w of (DeadSink _) -> False; _ -> True) (L.concat lbs)
                                                                    ports = if (L.length cols > 1)
                                                                            then [(channelName $ fst $ getChannel net chan,inpCompName "sw" fsmind (channelIDtoInt chan) Nothing)]
                                                                            else if (L.length lbs' > 0)
                                                                                 then [(channelName $ fst $ getChannel net chan,inpCompName "lb" fsmind (channelIDtoInt chan) (Just 0))]
                                                                                 else []
                                                                    ports' = if (L.length cols > 1)
                                                                             then L.concat (map (\x -> [(inpCompName "sw" fsmind (channelIDtoInt chan) Nothing,inpChanName "sw" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex x cols')) Nothing)]) cols')
                                                                             else []
                                                                    ports'' = L.concat (map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                                   then [(inpChanName "sw" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex x cols')) Nothing,inpCompName "lb" fsmind (channelIDtoInt chan) (Just $ MB.fromJust (L.elemIndex x cols')))]
                                                                                                   else if (countInputTrans net comp chan x) == 0
                                                                                                        then [(inpChanName "sw" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex x cols')) Nothing,inpCompName "ds" fsmind (channelIDtoInt chan) (Just $ MB.fromJust (L.elemIndex x cols')))]
                                                                                                        else []) cols')
                                                                    ports''' = L.concat (map (\x -> if (countInputTrans net comp chan x) > 1
                                                                                                    then [(inpCompName "lb" fsmind (channelIDtoInt chan) (Just $ MB.fromJust (L.elemIndex x cols')),inpChanName "lb" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex x cols')) (Just i)) | i <- [0..((L.length cols') - 1)]]
                                                                                                    else []) cols')
                                                                in NSpec (switch ++ (L.concat lbs)) (chans ++ chans') (ports ++ ports' ++ ports'' ++ ports''')
                                                           else error "inputTemplate: The given channel is not an input channel of the given automaton"
                                _ -> error "inputTemplate: Automaton expected"


transitionITemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
transitionITemplate net comp chan col p q = case (getComponent net comp) of
                                              (Automaton _ _ _ _ t _) -> let fsmind = getFSMIndex net comp
                                                                             (ColorSet cols) = getColorSet net chan
                                                                             cols' = S.toList cols
                                                                             t' = (filter (\(AutomatonT p' q' inport infun _ _ _ _) -> p == p' && q == q' && (eval (makeVArguments [col]) infun)) t) !! 0
                                                                             ind = MB.fromJust $ L.elemIndex t' t
                                                                             outs = getInputTemplateOuts net comp chan col
                                                                             o = outs !! ind
                                                                             incoming = filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') t
                                                                             inind = MB.fromJust $ L.elemIndex t' incoming
                                                                             outgoing = filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') t
                                                                             outind = MB.fromJust $ L.elemIndex t' outgoing
                                                                             sins = getStateTemplateIns net comp p
                                                                             souts = getStateTemplateOuts net comp p
                                                                             comps = [ControlJoin (transCompName "jn" fsmind p q (Just (channelIDtoInt chan,MB.fromJust (L.elemIndex col cols'))) Nothing)]
                                                                             ports = [(souts !! outind,transCompName "jn" fsmind p q (Just (channelIDtoInt chan,MB.fromJust (L.elemIndex col cols'))) Nothing),(o,transCompName "jn" fsmind p q (Just (channelIDtoInt chan,MB.fromJust (L.elemIndex col cols'))) Nothing),(transCompName "jn" fsmind p q (Just (channelIDtoInt chan,MB.fromJust (L.elemIndex col cols'))) Nothing,sins !! inind)]
                                                                             in NSpec comps [] ports
                                              _ -> error "transitionITemplate: Automaton expected"


outputTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
outputTemplate net comp chan = case (getComponent net comp) of
                                 (Automaton _ _ _ _ _ _) -> if (L.elem chan (getOutChannels net comp))
                                                            then let fsmind = getFSMIndex net comp
                                                                     (ColorSet cols) = getColorSet net chan
                                                                     cols' = S.toList cols
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
                                                                     ports = L.concat (map (\(x,ys) -> [(getName (ys !! 1),getName x),(getName (ys !! 2),getName x),(getName x,getName (ys !! 0))]) compchans)
                                                                 in NSpec comps chans ports
                                                            else error "outputTemplate: The given channel is not an output channel of the given automaton"
                                 _ -> error "outputTemplate: Automaton expected"


                                           {-
                                           data AutomatonTransition = AutomatonT {
                                               startState :: Int, -- ^ start-state
                                               endState :: Int, -- ^ end-state
                                               inPort :: Int, -- ^ input port
                                               epsilon :: MFunctionBool,
                                               eventFunction :: Int -> Color -> Bool, -- ^ port-sensitive event
                                               outPort :: Maybe Int,
                                               phi :: Maybe (MFunctionDisj),
                                               packetTransformationFunction :: Int -> Color -> Maybe (Int, Color) -- ^ port-sensitive packet transformation
                                           }
                                           -}
transitionIOTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> ChannelID -> Color -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
transitionIOTemplate net comp ichan icol ochan ocol p q =
  case (getComponent net comp) of
    (Automaton _ _ _ _ t _) -> let fsmind = getFSMIndex net comp
                                   (ColorSet icols) = getColorSet net ichan
                                   icols' = S.toList icols
                                   (ColorSet ocols) = getColorSet net ochan
                                   ocols' = S.toList ocols
                                   t' = (filter (\(AutomatonT p' q' _ _ _ _ outfun _) -> p == p' && q == q' && ((eval (makeVArguments []) (MB.fromJust outfun)) == ocol)) t) !! 0
                                   ind = MB.fromJust $ L.elemIndex t' t
                                   colind = MB.fromJust $ L.elemIndex ocol ocols'
                                   ins = getOutputTemplateIns net comp ochan
                                   i = ins !! (ind * (L.length ocols') + colind)
                                   t'' = if (filter (\(AutomatonT p' q' inport infun _ _ _ _) -> p == p' && q == q' && (eval (makeVArguments [icol]) infun)) t) == []
                                         then error "transitionIOTemplate: Error while computing t''"
                                         else (filter (\(AutomatonT p' q' inport infun _ _ _ _) -> p == p' && q == q' && (eval (makeVArguments [icol]) infun)) t) !! 0
                                   ind' = MB.fromJust $ L.elemIndex t'' t
                                   outs' = getInputTemplateOuts net comp ichan icol
                                   o = outs' !! ind'
                                   incoming = filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') t
                                   inind = MB.fromJust $ L.elemIndex t' incoming
                                   outgoing = filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') t
                                   outind = MB.fromJust $ L.elemIndex t' outgoing
                                   sins = getStateTemplateIns net comp p
                                   souts = getStateTemplateOuts net comp p
                                   comps = [Fork (transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            Function (transCompName "fun" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))) (color2mfunction ocol) (ColorSet (S.singleton ocol)),
                                            ControlJoin (transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan,MB.fromJust (L.elemIndex ocol ocols'))))]
                                   chans = [Channel (transChanName "frk_fun" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            Channel (transChanName "jn_frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))))]
                                   ports = [
                                            (souts !! outind,transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan,MB.fromJust (L.elemIndex ocol ocols')))),
                                            (o,transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan,MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transCompName "jn" fsmind p q (Just (channelIDtoInt ichan,MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan,MB.fromJust (L.elemIndex ocol ocols'))),transChanName "jn_frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transChanName "jn_frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))),transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))), sins !! inind),
                                            (transCompName "frk" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))), transChanName "frk_fun" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),

                                            (transChanName "frk_fun" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))),transCompName "fun" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transCompName "fun" fsmind p q (Just (channelIDtoInt ichan, MB.fromJust (L.elemIndex icol icols'))) (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))),i)]
                               in NSpec comps chans ports
    _ -> error "transitionOTemplate: Automaton expected"


transitionOTemplate :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> Int -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
transitionOTemplate net comp ochan ocol p q =
  case (getComponent net comp) of
    (Automaton _ _ _ _ t _) -> let fsmind = getFSMIndex net comp
                                   (ColorSet ocols) = getColorSet net ochan
                                   ocols' = S.toList ocols
                                   t' = (filter (\(AutomatonT p' q' _ _ _ _ outfun _) -> p == p' && q == q' && ((eval (makeVArguments []) (MB.fromJust outfun)) == ocol)) t) !! 0
                                   ind = MB.fromJust $ L.elemIndex t' t
                                   colind = MB.fromJust $ L.elemIndex ocol ocols'
                                   ins = getOutputTemplateIns net comp ochan
                                   i = ins !! (ind * (L.length ocols') + colind)
                                   incoming = filter (\(AutomatonT _ q' _ _ _ _ _ _) -> q == q') t
                                   inind = MB.fromJust $ L.elemIndex t' incoming
                                   outgoing = filter (\(AutomatonT p' _ _ _ _ _ _ _) -> p == p') t
                                   outind = MB.fromJust $ L.elemIndex t' outgoing
                                   sins = getStateTemplateIns net comp p
                                   souts = getStateTemplateOuts net comp p
                                   comps = [Fork (transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            Function (transCompName "fun" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))) (color2mfunction ocol) (ColorSet (S.singleton ocol))]
                                   chans = [Channel (transChanName "frk_fun" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))))]
                                   ports = [
                                            (souts !! outind, transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))), sins !! inind),
                                            (transCompName "frk" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))), transChanName "frk_fun" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transChanName "frk_fun" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))),transCompName "fun" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols')))),
                                            (transCompName "fun" fsmind p q Nothing (Just (channelIDtoInt ochan, MB.fromJust (L.elemIndex ocol ocols'))),i)]
                               in NSpec comps chans ports
    _ -> error "transitionOTemplate: Automaton expected"


initTemplate :: ColoredNetwork -> ComponentID -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
initTemplate net comp = case (getComponent net comp) of
                          (Automaton _ _ _ _ _ _) -> let fsmind = getFSMIndex net comp
                                                         sins = getStateTemplateIns net comp 0
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
stateTemplate :: ColoredNetwork -> ComponentID -> Int -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
stateTemplate net comp p = case (getComponent net comp) of
                             (Automaton _ _ _ _ ts _) -> let fsmind = getFSMIndex net comp
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
                                                                           (getName (comps !! 0),getName (chans !! 0)),
                                                                           (getName (chans !! 0),getName (comps_lb !! 0))
                                                                           ] ++
                                                                           [(stateCompName "lb" fsmind p Nothing,stateChanName "lb" fsmind p (Just i)) | i <- [0..ot-1]]
                                                                     else [(getName (comps !! 0),getName (chans !! 0))]
                                                             ports' = if it > 1
                                                                      then ((stateChanName "mrg" fsmind p (Just 0),stateCompName "q" fsmind p Nothing):(L.concat (map (\(x,ys) -> [(getName (ys !! 1),getName x),(getName (ys !! 2),getName x),(getName x,getName (ys !! 0))]) compchans)))
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

getInputTemplateOuts :: ColoredNetwork -> ComponentID -> ChannelID -> Color -> [T.Text]
getInputTemplateOuts net comp chan col = let (ColorSet cols) = getColorSet net chan
                                             cols' = S.toList cols
                                             trans = countInputTrans net comp chan col
                                             fsmind = getFSMIndex net comp
                                             res = if ((L.length cols') == 1) && (trans == 1)
                                                   then [(channelName $ fst $ getChannel net chan)]
                                                   else if trans > 1
                                                        then [inpChanName "lb" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex col cols')) (Just i) | i <- [0..trans]]
                                                        else [inpChanName "sw" fsmind (channelIDtoInt chan) (MB.fromJust (L.elemIndex col cols')) Nothing]
                                         in res


getOutputTemplateIns :: ColoredNetwork -> ComponentID -> ChannelID -> [T.Text]
getOutputTemplateIns net comp chan = case (getComponent net comp) of
                                       (Automaton _ _ _ _ _ _) -> let fsmind = getFSMIndex net comp
                                                                      (ColorSet cols) = getColorSet net chan
                                                                      cols' = S.toList cols
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

getStateTemplateIns :: ColoredNetwork -> ComponentID -> Int -> [T.Text]
getStateTemplateIns net comp p = case (getComponent net comp) of
                                   (Automaton _ _ _ _ _ _) -> let fsmind = getFSMIndex net comp
                                                                  it = if p == 0
                                                                       then (countIncomingTrans net comp p) + 1
                                                                       else (countIncomingTrans net comp p)
                                                                  chans = if it > 1
                                                                          then [stateChanName "mrg" fsmind p (Just i) | i <- [0..((it - 1) * 2)]]
                                                                          else [stateChanName "q_in" fsmind p Nothing]
                                                              in (odds chans) ++ [L.last chans]
                                   _ -> error "getStateTemplateIns: Automaton expected"

getStateTemplateOuts :: ColoredNetwork -> ComponentID -> Int -> [T.Text]
getStateTemplateOuts net comp p = case (getComponent net comp) of
                                    (Automaton _ _ _ _ _ _) -> let fsmind = getFSMIndex net comp
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
                      in inputTemplate net fsm inp

testTransITemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testTransITemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                             inp = (getInChannels net fsm) !! 0
                             (ColorSet cols) = getColorSet net inp
                             col = (S.toList cols) !! 1
                         in transitionITemplate net fsm inp col 0 1


testTransIOTemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testTransIOTemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                              inp = (getInChannels net fsm) !! 0
                              (ColorSet cols) = getColorSet net inp
                              col = (S.toList cols) !! 1
                              out = (getOutChannels net fsm) !! 0
                              (ColorSet cols') = getColorSet net out
                              col' = (S.toList cols') !! 0
                          in transitionIOTemplate net fsm inp col out col' 0 1


testOutTemplate :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testOutTemplate net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                          out = (getOutChannels net fsm) !! 0
                      in outputTemplate net fsm out

testOutTemplateIns :: ColoredNetwork -> [T.Text]
testOutTemplateIns net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                             out = (getOutChannels net fsm) !! 0
                         in getOutputTemplateIns net fsm out

testTranslateFSM :: ColoredNetwork -> Specification (XComponent T.Text) (XChannel T.Text) T.Text
testTranslateFSM net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                       in translateFSM net fsm

testReplaceFSM :: ColoredNetwork -> ColoredNetwork
testReplaceFSM net = let fsm = fst ((getAllProcessesWithID net) !! 0)
                     in replaceFSM net fsm

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
