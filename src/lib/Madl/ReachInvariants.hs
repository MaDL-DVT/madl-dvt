{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}

{-

Module      : Madl.ReachInvariants
Description : Generates backward reachability invariants for a madl network.
Copyright   : (c) Alexander Fedotov 2020

-}
module Madl.ReachInvariants where


import qualified Data.IntMap as IM
import qualified Data.Bimap as BM
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Data.Maybe (catMaybes, isJust, mapMaybe, fromMaybe)
import qualified Data.Partition as P
import Data.Ratio(denominator)
import qualified Data.Set as Set
import qualified Data.Text as T

import Utils.Map
import Utils.Text

import Madl.Base
import Madl.MsgTypes
import Madl.Network

import Madl.Deadlock.InvarFormulas
import Madl.Deadlock.SMT


getOutColor :: AutomatonTransition -> Int -> ColorSet -> Color
getOutColor (AutomatonT _ _ _ _ _ _ _ f) p cols = let (ColorSet cs) = cols
                                                      cs' = Set.toList cs
                                                      res = filter (\x -> case x of (Just (port,_)) -> p==port; _ -> False) (map (\c -> f p c) cs')
                                                      res' = map (\x -> let (Just (_,col)) = x in col) res
                                                  in if (length res') > 0 then res' !! 0 else error "getOutColor: No output data"


getTransInCol :: AutomatonTransition -> Int -> [Color] -> Maybe Color
getTransInCol _ _ [] = Nothing
getTransInCol t i (c:cs) = if (eventFunction t) i c
                           then Just c
                           else getTransInCol t i cs


getTransOutCol :: AutomatonTransition -> Int -> Int -> [Color] -> [Color] -> Maybe Color
getTransOutCol _ _ 0 [] _ = Nothing
getTransOutCol t o nr [] cols = getTransOutCol t o (nr-1) cols cols
getTransOutCol t o nr (c:cs) cols = case (packetTransformationFunction t) nr c of
                                      Just (o',c') -> if o==o'
                                                      then Just c'
                                                      else getTransOutCol t o nr cs cols
                                      Nothing -> getTransOutCol t o nr cs cols


getReadTrans :: [AutomatonTransition] -> Int -> [Color] -> [(Int,Color)]
getReadTrans ts i cs = let ts' = filter (\x -> (inPort x) == i) ts
                           r = map (\x -> (fromJust $ elemIndex x ts,getTransInCol x i cs)) ts'
                           r' = filter (\(_,x) -> case x of (Just _) -> True; _ -> False) r
                           r'' = map (\(x,y) -> (x,fromJust y)) r'
                       in r''


getWriteTrans :: [AutomatonTransition] -> Int -> Int -> [Color] -> [(Int,Color)]
getWriteTrans ts o nr cs = let ts' = filter (\x -> case (outPort x) of (Just o') -> o == o'; _ -> False) ts
                               r = map (\x -> (fromJust $ elemIndex x ts,getTransOutCol x o nr cs cs)) ts'
                               r' = filter (\(_,x) -> case x of (Just _) -> True; _ -> False) r
                               r'' = map (\(x,y) -> (x,fromJust y)) r'
                           in r''


makeSignals :: ColoredNetwork -> ComponentID -> Int -> InvarFormula
makeSignals net cid step = case (getComponent net cid) of
                              Source _ _ -> TRUE
                              Queue _ k -> let i = (getInChannels net cid) !! 0
                                               o = (getOutChannels net cid) !! 0
                                               itrdy = makeBiimpl (BVAR $ Trdy i step) (NEG $ EQUALS (IVAR $ QOccupancy cid step) (INT k))
                                               oirdy = makeBiimpl (BVAR $ Irdy o step) (NEG $ EQUALS (IVAR $ QOccupancy cid step) (INT 0))
                                               odata = makeImpl (GREATER (IVAR $ QOccupancy cid step) (INT 0)) (EQUALS (IVAR $ Data o step) (IVAR $ QCell cid (k-1) step))
                                           in makeConj [itrdy,oirdy,odata]
                              Function _ fun _ -> let i = (getInChannels net cid) !! 0
                                                      o = (getOutChannels net cid) !! 0
                                                      (ColorSet cols) = getColorSet net i
                                                      cols' = Set.toList cols
                                                      tm = typeMap net
                                                      oirdy = makeBiimpl (BVAR $ Irdy o step) (BVAR $ Irdy i step)
                                                      itrdy = makeBiimpl (BVAR $ Trdy i step) (BVAR $ Trdy o step)
                                                      (colmap :: [(Color,Color)]) = map (\x -> (x,eval (makeVArguments [x]) fun)) cols'
                                                      odata = makeConj $ map (\(x,y) -> makeImpl (EQUALS (IVAR $ Data i step) (INT (tm BM.! x))) (EQUALS (IVAR $ Data o step) (INT (tm BM.! y)))) colmap
                                                  in makeConj [oirdy,itrdy,odata]
                              Fork _ -> let i = (getInChannels net cid) !! 0
                                            o0 = (getOutChannels net cid) !! 0
                                            o1 = (getOutChannels net cid) !! 1
                                            o0irdy = makeBiimpl (BVAR $ Irdy o0 step) (CONJ (BVAR $ Irdy i step) (BVAR $ Trdy o1 step))
                                            o1irdy = makeBiimpl (BVAR $ Irdy o1 step) (CONJ (BVAR $ Irdy i step) (BVAR $ Trdy o0 step))
                                            itrdy = makeBiimpl (BVAR $ Trdy i step) (CONJ (BVAR $ Trdy o0 step) (BVAR $ Trdy o1 step))
                                            o0data = EQUALS (IVAR $ Data o0 step) (IVAR $ Data i step)
                                            o1data = EQUALS (IVAR $ Data o1 step) (IVAR $ Data i step)
                                        in makeConj [o0irdy,o1irdy,o0data,o1data,itrdy]
                              ControlJoin _ -> let i0 = (getInChannels net cid) !! 0
                                                   i1 = (getInChannels net cid) !! 1
                                                   o = (getOutChannels net cid) !! 0
                                                   oirdy = makeBiimpl (BVAR $ Irdy o step) (CONJ (BVAR $ Irdy i0 step) (BVAR $ Irdy i1 step))
                                                   i0trdy = makeBiimpl (BVAR $ Trdy i0 step) (CONJ (BVAR $ Irdy i1 step) (BVAR $ Trdy o step))
                                                   i1trdy = makeBiimpl (BVAR $ Trdy i1 step) (CONJ (BVAR $ Irdy i0 step) (BVAR $ Trdy o step))
                                                   odata = EQUALS (IVAR $ Data o step) (IVAR $ Data i0 step)
                                               in makeConj [oirdy,i0trdy,i1trdy,odata]
                              Switch _ funs -> let i = (getInChannels net cid) !! 0
                                                   o0 = (getOutChannels net cid) !! 0
                                                   o1 = (getOutChannels net cid) !! 1
                                                   tm = typeMap net
                                                   (ColorSet cols) = getColorSet net i
                                                   cols' = Set.toList cols
                                                   (cols1 :: [(Int,Bool)]) = map (\x -> (tm BM.! x,eval (makeVArguments [x]) (funs !! 0))) cols'
                                                   cols1' = map (\(y,_) -> y) (filter (\(_,x) -> x) cols1)
                                                   disj1 = makeDisj $ map (\x -> (EQUALS (IVAR $ Data i step) (INT x))) cols1'
                                                   (cols2 :: [(Int,Bool)]) = map (\x -> (tm BM.! x,eval (makeVArguments [x]) (funs !! 1))) cols'
                                                   cols2' = map (\(y,_) -> y) (filter (\(_,x) -> x) cols2)
                                                   disj2 = makeDisj $ map (\x -> (EQUALS (IVAR $ Data i step) (INT x))) cols2'
                                                   o0irdy = makeBiimpl (BVAR $ Irdy o0 step) (CONJ disj1 (BVAR $ Irdy i step))--makeConj $ map (\x -> makeImpl (EQUALS (IVAR $ Data i step) (INT x)) (CONJ (makeBiimpl (BVAR $ Irdy o0 step) (BVAR $ Irdy i step)) (EQUALS (IVAR $ Data o0 step) (IVAR $ Data i step)))) cols1'
                                                   o1irdy = makeBiimpl (BVAR $ Irdy o1 step) (CONJ disj2 (BVAR $ Irdy i step))--makeConj $ map (\x -> makeImpl (EQUALS (IVAR $ Data i step) (INT x)) (CONJ (makeBiimpl (BVAR $ Irdy o1 step) (BVAR $ Irdy i step)) (EQUALS (IVAR $ Data o1 step) (IVAR $ Data i step)))) cols2'
                                                   itrdy = makeBiimpl (BVAR $ Trdy i step) (DISJ (CONJ (BVAR $ Irdy o0 step) (BVAR $ Trdy o0 step)) (CONJ (BVAR $ Irdy o1 step) (BVAR $ Trdy o1 step)))
                                                   --o0data = EQUALS (IVAR $ Data o0 step) (IVAR $ Data i step)
                                                   --o1data = EQUALS (IVAR $ Data o1 step) (IVAR $ Data i step)
                                               in makeConj [o0irdy,o1irdy,itrdy{-,o0data,o1data-}]
                              Merge _ -> let i0 = (getInChannels net cid) !! 0
                                             i1 = (getInChannels net cid) !! 1
                                             o = (getOutChannels net cid) !! 0
                                             oirdy = makeBiimpl (BVAR $ Irdy o step) (DISJ (CONJ (EQUALS (IVAR $ Sel cid step) (INT 0)) (BVAR $ Irdy i0 step)) (CONJ (EQUALS (IVAR $ Sel cid step) (INT $ 1)) (BVAR $ Irdy i1 step)))
                                             i0trdy = makeBiimpl (BVAR $ Trdy i0 step) (makeConj [EQUALS (IVAR $ Sel cid step) (INT 0),BVAR $ Trdy o step,BVAR $ Irdy i0 step])
                                             i1trdy = makeBiimpl (BVAR $ Trdy i1 step) (makeConj [EQUALS (IVAR $ Sel cid step) (INT 1),BVAR $ Trdy o step,BVAR $ Irdy i1 step])
                                             odata = CONJ (makeImpl (CONJ (EQUALS (IVAR $ Sel cid step) (INT 0)) (BVAR $ Irdy i0 step)) (EQUALS (IVAR $ Data o step) (IVAR $ Data i0 step))) (makeImpl (CONJ (EQUALS (IVAR $ Sel cid step) (INT 1)) (BVAR $ Irdy i1 step)) (EQUALS (IVAR $ Data o step) (IVAR $ Data i1 step)))
                                         in makeConj [oirdy,i0trdy,i1trdy,odata]
                              Automaton _ _ _ _ tr _  -> let ins = getInChannels net cid
                                                             outs = getOutChannels net cid
                                                             tm = typeMap net
                                                             f = \x -> let (ColorSet cols) = getColorSet net x
                                                                           rtrs = getReadTrans tr (fromJust $ elemIndex x ins) (Set.toList cols)
                                                                       in if Set.null cols then TRUE else makeBiimpl (BVAR $ Trdy x step) (makeDisj (map (\(i,_) -> {-CONJ-} (EQUALS (IVAR $ Sel cid step) (INT (i+1))) {-(EQUALS (IVAR $ Data x step) (INT $ (tm BM.! c)))-}) rtrs))
                                                             f' = \x -> let (ColorSet cols) = getColorSet net x in if Set.null cols then TRUE else makeBiimpl (BVAR $ Irdy x step) (makeDisj (map (\(i,_) -> {-CONJ-} (EQUALS (IVAR $ Sel cid step) (INT (i+1))) {-(EQUALS (IVAR $ Data x step) (INT $ (tm BM.! c)))-}) (getWriteTrans tr (fromJust $ elemIndex x outs) (length ins) (Set.toList cols))))
                                                             f'' = \x -> let --(ColorSet cols) = getColorSet net (ins !! (inPort x))
                                                                             icol = getTransInCol x (inPort x) (let (ColorSet cols) = getColorSet net (ins !! (inPort x)) in Set.toList cols)
                                                                         in if (icol == Nothing) then TRUE else
                                                                         let curs = EQUALS (IVAR $ Cur cid step) (INT $ startState x)
                                                                             idata = EQUALS (IVAR $ Data (ins !! (inPort x)) step) (INT $ (tm BM.! (fromJust icol)))
                                                                             odata = case (outPort x) of
                                                                                        (Just o) -> EQUALS (IVAR $ Data (outs !! o) step) (INT $ (tm BM.! (fromJust $ getTransOutCol x o (length outs) (let (ColorSet cols) = getColorSet net (outs !! o) in Set.toList cols) (let (ColorSet cols) = getColorSet net (outs !! o) in Set.toList cols))))
                                                                                        _ -> TRUE
                                                                             iirdy = (BVAR $ Irdy (ins !! (inPort x)) step)
                                                                             otrdy = case (outPort x) of
                                                                                        (Just o) -> (BVAR $ Trdy (outs !! o) step)
                                                                                        _ -> TRUE
                                                                         in makeImpl (EQUALS (IVAR $ Sel cid step) (INT ((fromJust $ elemIndex x tr)+1))) (makeConj [curs,idata,odata,iirdy,otrdy])
                                                         in makeConj ((map (\x -> f x) ins) ++ (map (\x -> f' x) outs) ++ (map (\x -> f'' x) tr))
                              _ -> TRUE


getQueueSize :: ColoredNetwork -> ComponentID -> Int
getQueueSize net cid = case (getComponent net cid) of
                          Queue _ k -> k
                          _ -> error "getQueueSize: Wrong component type"


colorSetToColors :: ColorSet -> [Color]
colorSetToColors cs = let (ColorSet cs') = cs
                      in Set.toList cs'


makeColorAssertion :: ColoredNetwork -> ChannelID -> [Color] -> Int -> String
makeColorAssertion net cid cs i = let tm = typeMap net
                                      r = map (\x -> "(= " ++ (show $ IVAR $ Data cid i) ++ " " ++ (show $ tm BM.! x) ++ ")") cs
                                      r' = if length r > 1
                                           then "(assert (or " ++ (foldr (\x y -> if y /= "" then x ++ " " ++ y else x ++ y) "" r) ++ "))"
                                           else if length r > 0 then "(assert " ++ (r !! 0) ++ ")" else "(assert true)"
                                  in r'


makeInit :: ColoredNetwork -> Int -> InvarFormula
makeInit net step = let qs = Madl.Network.getAllQueueIDs net
                        as = Madl.Network.getAllProcessIDs net
                        f = map (\x -> EQUALS (IVAR (QOccupancy x step)) (INT 0)) qs
                        f' = map (\x -> EQUALS (IVAR (Cur x step)) (INT 0)) as
                    in makeConj (f ++ f')


makeImpl :: InvarFormula -> InvarFormula -> InvarFormula
makeImpl a b = IMPL a b {-DISJ (NEG a) b-}


makeBiimpl :: InvarFormula -> InvarFormula -> InvarFormula
makeBiimpl a b = BIIMPL a b --CONJ (makeImpl a b) (makeImpl b a)


notSeen :: ColoredNetwork -> Int -> Int -> Bool -> InvarFormula
notSeen net step bound ri = if step < bound
                            then let qs = Madl.Network.getAllQueueIDs net
                                     as = Madl.Network.getAllProcessIDs net
                                     f = \z -> (map (\(x,y) -> (NEG $ EQUALS (IVAR $ QCell x y step) (IVAR $ QCell x y z))) [(a,b) | a <- qs, b <- [0..((getQueueSize net a)-1)]])
                                     f' = \z -> (map (\x -> (NEG $ EQUALS (IVAR $ Cur x step) (IVAR $ Cur x z))) as)
                                     f'' = makeConj (map (\x -> makeDisj ((f x) ++ (f' x))) [(step+1)..bound])
                                 in if ri then TRUE else f''
                            else error "notSeen: step is requited to be less than bound"


queueSame :: ColoredNetwork -> ComponentID -> Int -> InvarFormula
queueSame net cid step = case (getComponent net cid) of
                            Queue _ _ -> let f = makeConj (map (\x -> EQUALS (IVAR $ QCell cid x (step-1)) (IVAR $ QCell cid x step)) [0..((getQueueSize net cid)-1)])
                                         in CONJ f (EQUALS (IVAR $ QOccupancy cid (step-1)) (IVAR $ QOccupancy cid (step)))
                            _ -> error "queueSame: unexpected component type"


queueDeq :: ColoredNetwork -> ComponentID -> Int -> InvarFormula
queueDeq net cid step = case (getComponent net cid) of
                           Queue _ k -> let f = \y -> makeConj (map (\x -> EQUALS (IVAR $ QCell cid (x-1) (step-1)) (IVAR $ QCell cid x step)) [(k-y)..(k-1)])
                                            f' = \y -> makeConj (map (\x -> EQUALS (IVAR $ QCell cid x step) (INT 0)) (init [0..(k-y)]))
                                            f'' = \x -> makeImpl (EQUALS (IVAR $ QOccupancy cid step) (INT x)) (makeConj [f x,f' x])
                                            f''' = EQUALS (IVAR $ QOccupancy cid (step-1)) (PLUS (IVAR $ QOccupancy cid step) (INT 1))
                                        in CONJ (makeConj $ map (\x -> f'' x) [0..k-1]) f'''
                           _ -> error "queueDeq: unexpected component type"


queueEnq :: ColoredNetwork -> ComponentID -> Int -> InvarFormula
queueEnq net cid step = case (getComponent net cid) of
                           Queue _ k -> let i = ((getInChannels net cid) !! 0)
                                            f = \y -> EQUALS (IVAR $ QCell cid (k-y) step) (IVAR $ Data i (step-1))
                                            f' = \y -> if ((k-y)+1)<k
                                                       then makeConj (map (\x -> EQUALS (IVAR $ QCell cid x (step-1)) (IVAR $ QCell cid x step)) [((k-y)+1)..(k-1)])
                                                       else TRUE
                                            f'' = \y -> if (k-y)>0
                                                        then makeConj (map (\x -> EQUALS (IVAR $ QCell cid x step) (INT 0)) (init [0..(k-y)]))
                                                        else TRUE
                                            f''' = \x -> makeImpl (EQUALS (IVAR $ QOccupancy cid step) (INT x)) (makeConj [f x,f' x,f'' x])
                                            f'''' = EQUALS (IVAR $ QOccupancy cid (step-1)) (MINUS (IVAR $ QOccupancy cid step) (INT 1))
                                        in CONJ (makeConj $ map (\x -> f''' x) [1..k]) f''''
                           _ -> error "queueDeq: unexpected component type"


queueDeqEnq :: ColoredNetwork -> ComponentID -> Int -> InvarFormula
queueDeqEnq net cid step = case (getComponent net cid) of
                              Queue _ k -> let i = ((getInChannels net cid) !! 0)
                                               f = \y -> EQUALS (IVAR $ QCell cid (k-y) step) (IVAR $ Data i (step-1))
                                               f' = \y -> if ((k-y)+1)<k
                                                          then makeConj (map (\x -> EQUALS (IVAR $ QCell cid (x-1) (step-1)) (IVAR $ QCell cid x step)) [((k-y)+1)..(k-1)])
                                                          else TRUE
                                               f'' = \y -> if (k-y)>0
                                                           then makeConj (map (\x -> EQUALS (IVAR $ QCell cid x step) (INT 0)) (init [0..(k-y)]))
                                                           else TRUE
                                               f''' = \x -> makeImpl (EQUALS (IVAR $ QOccupancy cid step) (INT x)) (makeConj [f x,f' x,f'' x])
                                               f'''' = EQUALS (IVAR $ QOccupancy cid (step-1)) (IVAR $ QOccupancy cid step)
                                           in CONJ (makeConj $ map (\x -> f''' x) [1..k]) f''''
                              _ -> error "queueDeq: unexpected component type"


localStep :: ColoredNetwork -> ComponentID -> Int -> InvarFormula
localStep net cid step = case (getComponent net cid) of
                            Source _ _ -> let o = ((getOutChannels net cid) !! 0)
                                              f = makeConj [BVAR (Irdy o (step-1)),NEG (BVAR (Trdy o (step-1)))]
                                              f' = makeConj [BVAR (Irdy o step), EQUALS (IVAR $ Data o (step-1)) (IVAR $ Data o step)]
                                          in makeImpl f f'
                            Sink _ -> let i = ((getInChannels net cid) !! 0)
                                          f = makeConj [BVAR (Trdy i (step-1)),NEG (BVAR (Irdy i (step-1)))]
                                          f' = BVAR (Trdy i step)
                                      in makeImpl f f'
                            Queue _ _ -> let i = ((getInChannels net cid) !! 0)
                                             o = ((getOutChannels net cid) !! 0)
                                             iirdy = BVAR $ Irdy i (step-1)
                                             itrdy = BVAR $ Trdy i (step-1)
                                             oirdy = BVAR $ Irdy o (step-1)
                                             otrdy = BVAR $ Trdy o (step-1)
                                             same = makeImpl (CONJ (NEG (CONJ iirdy itrdy)) (NEG (CONJ oirdy otrdy))) (queueSame net cid step)
                                             deq = makeImpl (CONJ (NEG (CONJ iirdy itrdy)) (CONJ oirdy otrdy)) (queueDeq net cid step)
                                             enq = makeImpl (CONJ (CONJ iirdy itrdy) (NEG (CONJ oirdy otrdy))) (queueEnq net cid step)
                                             deqenq = makeImpl (CONJ (CONJ iirdy itrdy) (CONJ oirdy otrdy)) (queueDeqEnq net cid step)
                                         in makeConj [same,deq,enq,deqenq]
                            Automaton _ _ _ _ tr _ -> let f = \x -> makeImpl (EQUALS (IVAR $ Sel cid (step-1)) (INT (x+1))) (EQUALS (IVAR $ Cur cid step) (INT (endState (tr !! x))))
                                                          f' = makeImpl (EQUALS (IVAR $ Sel cid (step-1)) (INT 0)) (EQUALS (IVAR $ Cur cid (step-1)) (IVAR $ Cur cid step))
                                                      in makeConj (f':(map (\x -> f x) [0..((length tr)-1)]))
                            _ -> TRUE


relateStates :: ColoredNetwork -> Int -> InvarFormula
relateStates net bound = let as = getAllProcessIDs net
                             qs = getAllQueueIDs net
                             qs' = filter (\x -> (length (colorSetToColors (getColorSet net ((getInChannels net x) !! 0)))) > 1) qs
                             tm = typeMap net
                             f = map (\x -> EQUALS (CUSTOMIVAR (smt_automaton_state net x)) (IVAR $ Cur x bound)) as
                             f' = \x y -> let k = getQueueSize net x
                                          in EQUALS (CUSTOMIVAR (smt_queue_packet net x (tm BM.!> y) showColorNoSpaces)) (makeSum $ map (\z -> ITE (EQUALS (IVAR $ QCell x z bound) (INT y)) (INT 1) (INT 0)) [0..k-1])
                             f'' = map (\(a,b) -> f' b (tm BM.! a)) [(c,q) | q <- qs', c <- (colorSetToColors (getColorSet net ((getInChannels net q) !! 0)))]
                             m = \x -> let k = getQueueSize net x
                                          in EQUALS (CUSTOMIVAR (smt_queue net x )) (makeSum $ map (\z -> ITE (NEG (EQUALS (IVAR $ QCell x z bound) (INT 0))) (INT 1) (INT 0)) [0..k-1])
                             m' = map (\x -> m x) qs
                             m'' = map (\x -> EQUALS (CUSTOMIVAR (smt_queue net x )) (IVAR $ QOccupancy x bound)) qs
                         in makeConj (f ++ f'' ++ m' ++ m'')


makeInvar :: ColoredNetwork -> Int -> Int -> Bool -> InvarFormula
makeInvar _ 0 _ _ = TRUE
makeInvar net k bound ri = let invar' = makeInvar net (k-1) bound ri
                               state = makeConj $ map (\x -> makeSignals net x k) (getComponentIDs net)
                               notseen = notSeen net (k-1) bound ri
                               step = makeConj $ map (\x -> localStep net x k) (getComponentIDs net)
                               initial = makeInit net k
                           in DISJ (makeConj [invar',state,notseen,step]) initial


makeInvar' :: ColoredNetwork -> Int -> Int -> String
makeInvar' _ 0 _ = "true"
makeInvar' net k bound = let invar' = makeInvar' net (k-1) bound
                             notseen = "not_seen_" ++ (show (k-1))
                             step = "global_step_" ++ (show k)
                             initial = "initial_" ++ (show k)
                         in "(or (and " ++ invar' ++ " " ++ notseen ++ " " ++ step ++ ") " ++ initial ++ ")"


makeInvar'' :: ColoredNetwork -> Int -> Int -> String
makeInvar'' _ 0 _ = "initial_0"
makeInvar'' net k bound = let invar' = makeInvar'' net (k-1) bound
                             --state = "global_state_" ++ (show k)
                              notseen = "not_seen_" ++ (show (k-1))
                              step = "global_step_" ++ (show k)
                              --initial = "initial_" ++ (show k)
                          in "(and " ++ invar' ++ " " ++ {-state ++ " " ++ -} notseen ++ " " ++ step ++ ")"


makeSignals' :: ColoredNetwork -> Int -> String
makeSignals' net bound = let f = makeConj $ map (\x -> makeSignals net x bound) (getComponentIDs net)
                         in "(assert (= global_state_" ++ (show bound) ++ " " ++ (show f) ++ "))"


makeSteps' :: ColoredNetwork -> Int -> String
makeSteps' net bound = let f = makeConj $ map (\x -> localStep net x bound) (getComponentIDs net)
                       in "(assert (= global_step_" ++ (show bound) ++ " " ++ (show f) ++ "))"


makeFormulas :: ColoredNetwork -> Int -> Bool -> String
makeFormulas net bound ri = let state = foldr (\x y -> x ++ "\n\n" ++ y) "" (map (\x -> makeSignals' net x) [0..bound])
                                notseen = \k -> "(assert (= not_seen" ++ "_" ++ (show k) ++ " " ++ (show $ notSeen net k bound ri) ++ "))"
                                notseen' = foldr (\x y -> x ++ "\n\n" ++ y) "" (map (\x -> notseen x) [0..(bound-1)])
                                step = foldr (\x y -> x ++ "\n\n" ++ y) "" (map (\x -> makeSteps' net x) [1..bound])
                                initial = \k -> "(assert (= initial" ++ "_" ++ (show k) ++ " " ++ (show (makeInit net k)) ++ "))"
                                initial' = foldr (\x y -> x ++ "\n\n" ++ y) "" (map (\x -> initial x) [0..bound])
                            in state ++ notseen' ++ step ++ initial'


makeConsistentStates :: Int -> String
makeConsistentStates bound = let r = map (\x -> "(= global_state_" ++ (show x) ++ " true)") [0..bound]
                                 r' = foldr (\x y -> if y /= "" then x ++ " " ++ y else x ++ y) "" r
                             in "(assert (and " ++ r' ++ "))"


makeVars :: ColoredNetwork -> Int -> String
makeVars net bound = let chans = getChannelIDs net
                         qs = getAllQueueIDs net
                         as = getAllProcessIDs net
                         mrgs = getAllMergeIDs net
                         irdyVars = map (\(x,y) -> "(declare-fun " ++ (show $ BVAR $ Irdy y x) ++ " () Bool)") [(s,c) | s <- [0..bound], c <- chans]
                         trdyVars = map (\(x,y) -> "(declare-fun " ++ (show $ BVAR $ Trdy y x) ++ " () Bool)") [(s,c) | s <- [0..bound], c <- chans]
                         dataVars = map (\(x,y) -> "(declare-fun " ++ (show $ IVAR $ Data y x) ++ " () Int) " ++ (makeColorAssertion net y (colorSetToColors $ getColorSet net y) x)) [(s,c) | s <- [0..bound], c <- chans]
                         qcelVars = map (\(a,b,c) -> "(declare-fun " ++ (show $ IVAR $ QCell a b c) ++ " () Int) (assert (>= " ++ (show $ IVAR $ QCell a b c) ++ " 0)) (assert (<= " ++ (show $ IVAR $ QCell a b c) ++ " " ++ (show ((BM.size (typeMap net))+1)) ++ "))") [(q,i,s) | q <- qs, i <- [0..(getQueueSize net q)-1], s <- [0..bound]]
                         qocVars = map (\(a,b) -> "(declare-fun " ++ (show $ IVAR $ QOccupancy a b) ++ " () Int) (assert (>= " ++ (show $ IVAR $ QOccupancy a b) ++ " 0)) (assert (<= " ++ (show $ IVAR $ QOccupancy a b) ++ " " ++ (show ((getQueueSize net a))) ++ "))") [(q,s) | q <- qs, s <- [0..bound]]
                         stateVars = map (\(a,b) -> "(declare-fun " ++ (show $ IVAR $ Cur a b) ++ " () Int) (assert (>= " ++ (show $ IVAR $ Cur a b) ++ " 0)) (assert (<= " ++ (show $ IVAR $ Cur a b) ++ " " ++ (show ((nrOfStates $ getComponent net a)-1)) ++ "))") [(p,s) | p <- as, s <- [0..bound]]
                         transVars = map (\(a,b) -> "(declare-fun " ++ (show $ IVAR $ Sel a b) ++ " () Int) (assert (>= " ++ (show $ IVAR $ Sel a b) ++ " 0)) (assert (<= " ++ (show $ IVAR $ Sel a b) ++ " " ++ (show ((length $ transitions $ getComponent net a))) ++ "))") [(p,s) | p <- as, s <- [0..bound]]
                         mrgVars = map (\(a,b) -> "(declare-fun " ++ (show $ IVAR $ Sel a b) ++ " () Int) (assert (>= " ++ (show $ IVAR $ Sel a b) ++ " 0)) (assert (<= " ++ (show $ IVAR $ Sel a b) ++ " 1))") [(p,s) | p <- mrgs, s <- [0..bound]]
                         gsvars = map (\x -> "(declare-fun global_state_" ++ (show x) ++ " () Bool)") [0..bound]
                         nsvars = map (\x -> "(declare-fun not_seen_" ++ (show x) ++ " () Bool)") [0..bound-1]
                         svars = map (\x -> "(declare-fun global_step_" ++ (show x) ++ " () Bool)") [1..bound]
                         ivars = map (\x -> "(declare-fun initial_" ++ (show x) ++ " () Bool)") [0..bound]
                         dlf = ["(declare-fun fls () Bool)"]
                     in foldr (\x y -> x ++ "\n" ++ y) "" (dlf ++ irdyVars ++ trdyVars ++ dataVars ++ qcelVars ++ qocVars ++ stateVars ++ transVars ++ mrgVars ++ gsvars ++ nsvars ++ svars ++ ivars)


invarToSMT :: ColoredNetwork -> Int -> Bool -> Bool -> String
invarToSMT net bound ri nl = let vars = makeVars net bound
                                 f = relateStates net bound
                                 f' = makeFormulas net bound ri
                                 f'' = makeConsistentStates bound
                                 f''' = if nl
                                        then makeInvar'' net bound bound
                                        else makeInvar' net bound bound
                                 reachInit = foldr (\x y -> if y /= "" then x ++ " " ++ y else x ++ y) "" (map (\x -> "(= initial_" ++ (show x) ++ " true)") [0..bound])
                                 reachInit' = if bound > 0 then "(assert (= (or " ++ reachInit ++ ") true))" else ""
                                 fri = if ri
                                       then reachInit'
                                       else ""
                             in vars ++ "\n\n" ++ "(assert (= " ++ show f ++ " true))" ++ "\n\n" ++ f' ++ "\n\n" ++ f'' ++ "\n\n" ++ fri ++ "\n\n" ++ "(assert (= " ++ f''' ++ " true))" ++ "\n\n(assert dlf)\n\n"
