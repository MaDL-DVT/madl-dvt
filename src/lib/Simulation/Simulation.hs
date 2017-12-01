{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Main
Desciption  : Main module for simulation tool
Copyright   : (c) Eindhoven University of Technology 2016 2017 
Authors     : Ruud van Vijfeijken 2017, Alexander Fedotov 2017, Julien Schmaltz 2017 

This is the main module of the simulation tool.
-}

module Simulation.Simulation
where

import Madl.Network
import Madl.Automata
import Madl.Islands
import Madl.MsgTypes

import Data.List
import qualified Data.Set as Set 
import System.Random -- needed to get a random element from a list

import Debug.Trace

-- Functions to deal with randomness and actions

-- Given a list and a seed, select a random element in the list
pickRandom :: (RandomGen a) => [b] -> a -> b
pickRandom lst seed = lst!!n
  where n = fst $ randomR (0::Int, length lst - 1) seed

-- Select one action of a source
getRndSrcActionFromState::(RandomGen a) => ColoredNetwork -> ComponentID -> SourceState -> a -> SourceActWithID
getRndSrcActionFromState net comp_id src_st seed = 
  case src_st of   
    Free -> pickRandom (getSourceActions net comp_id) seed; 
    Next c -> (comp_id, Inject c)

-- For each source of the network, select one source action.
-- The returned list is therefore the list of source action for the current
-- simulation cycle. 
getSourceActions_bis :: (RandomGen a) => ColoredNetwork -> [(ComponentID, SourceState )] -> a ->[SourceActWithID]
getSourceActions_bis _ [] _ = []
getSourceActions_bis net ((x_id,x_st):xs) seed = let newseed = snd $ randomR(1::Int,40000) seed
                                                 in [x_st']++(getSourceActions_bis net xs newseed)
  where x_st' = getRndSrcActionFromState net x_id x_st seed

-- select one sink action
-- note that we need to know which color is at the sink. 
-- We do not check for this now, so we might get impossible actions. 

-- TODO (JS) create a new seed at teach recursive step
getRndSnkAction :: (RandomGen a) => ColoredNetwork -> ComponentID -> a -> SinkActWithID
getRndSnkAction net comp_id seed = pickRandom (getSinkActions net comp_id) seed

getSnkActions_bis :: (RandomGen a) => ColoredNetwork -> a -> [SinkActWithID]
getSnkActions_bis net seed = let snk_ids = (map (fst) (getAllSinksWithID net)) 
                             in sinkRandom net snk_ids seed
  where sinkRandom ::(RandomGen a) => ColoredNetwork -> [ComponentID] -> a -> [SinkActWithID]
        sinkRandom _ [] _ = []
        sinkRandom net' id' seed' = let newseed = snd $ randomR(1::Int,30000) seed'
                                        act = getRndSnkAction net' (head id') seed'
                                    in act:sinkRandom net' (tail id') newseed

-- select one merge action
-- here again, the action should depend on the state
getRndMrgAction :: (RandomGen a) => ColoredNetwork -> ComponentID -> a -> MergeActWithID
getRndMrgAction net comp_id seed = pickRandom (getMergeActions net comp_id) seed

getMergeActions_bis :: (RandomGen a) => ColoredNetwork -> a -> [MergeActWithID]
getMergeActions_bis net seed = let mrg_ids = (map (fst) (getAllMergesWithID net))
                               in mergeRandom net mrg_ids seed
  where mergeRandom :: (RandomGen a) => ColoredNetwork -> [ComponentID] -> a -> [MergeActWithID]
        mergeRandom _ [] _ = []
        mergeRandom net' id' seed' = let newseed = snd $ randomR (1:: Int,20000) seed'
                                         act = getRndMrgAction net' (head id') seed'
                                     in act:mergeRandom net' (tail id') newseed



-----------------------list of Actions---------------------------

--data SinkAction = Reject | Consume Color deriving (Show,Ord,Eq)

--type SinkActWithID = (ComponentID,SinkAction)

--data SourceAction = Idle | Inject Color deriving (Show,Ord,Eq)

--type SourceActWithID = (ComponentID,SourceAction)

--type MergeAction = ChannelID

--type MergeActWithID = (ComponentID,MergeAction)

--type Action = ([SourceActWithID], [SinkActWithID], [MergeActWithID])

-----------------------------------------------------------------

-- setup used for source ratio is [sources] [ratios] with length of these lists is equal.

-- simulate network using the initial state of said network
simulateInitNetwork :: (RandomGen a) => ColoredNetwork -> Int -> a -> ([Action],[State])
simulateInitNetwork net n seed = ((map fst simulate),(map snd simulate)) 
   where simulate = trace ("calling simulate at step "++(show n)) $ simulateSteps net (initialState net) n seed

-- simulate network with a starting state of choice
simulateChoiceNetwork :: (RandomGen a) => ColoredNetwork -> Int -> a -> State -> ([Action],[State])
simulateChoiceNetwork net n seed s = ((map fst simulate'),(s:map snd simulate')) 
   where simulate' = simulateSteps net (s) n seed
{-
simulateSteps :: (RandomGen a) => ColoredNetwork -> State -> Int -> a -> [(Action,State)]-> [(Action,State)] 
simulateSteps _ st 0 _ acc      = acc++[(([],[],[]),st)] --  (State q_st src_st))]
simulateSteps net (State q_st src_st) n seed acc = 
   simulateSteps net st' (n-1) newseed (acc++[(newaction,(State q_st src_st))])
  where
    newseed          = snd $ randomR (1:: Int, 6) seed 
    snk_act_seed     = snd $ randomR (1:: Int, 8) seed
    mrg_act_seed     = snd $ randomR (1:: Int, 9) seed 
    newSourceActions = {-# SCC "getSourceActions" #-} getSourceActions_bis net src_st seed -- src_act_seed
    newSinkActions   = {-# SCC "getSinkActions" #-}   getSnkActions_bis net snk_act_seed
    newMrgActions    = {-# SCC "getMergeActions" #-}  getMergeActions_bis net mrg_act_seed
    legalActx        = {-# SCC "legalAction" #-} legalAction net (State q_st src_st) newaction
    newaction        = --trace ("Creating next action with source actions"++(show newSourceActions)++"and sink actions"++(show newSinkActions)++"and merge actions"++(show newMrgActions)) $ 
                       (newSourceActions, newSinkActions, newMrgActions) -- newMrgActions)
    nxt_st           =  if (legalActx) 
                        then {-# SCC "ComputeNextState" #-} getNextSim net newaction (State q_st src_st)
                        else error "illegal action"
    st'              = case nxt_st of Nothing -> error "no next states"; Just st -> st; 
-}


{-
-- | replayTrace replays a trace, that is, a list of actions, from a given state.
replayTrace :: ColoredNetwork -> State -> [Action] -> [(Action,State)]
replayTrace net st [] = []
replayTrace net st tr = 
  let 
    newaction = head tr 
    nxt_st    = getNextSim net newaction st
    st'       = case nxt_st of 
                  Nothing -> error "replayTrace 132: no next state";
                  Just st -> st;
    nxt_st'   = if (length st' == 1) then st' else error "replayTrace 134: non-deterministic trace"
  in
    (newaction,st) : replayTrace net nxt_st (tail tr)
-}

-- function that takes a starting state, an amount of steps n and a Madl
-- network and makes an action list for it ----no legal check---
simulateSteps :: (RandomGen a) => ColoredNetwork -> State -> Int -> a -> [(Action,State)] 
simulateSteps _ _ 0 _ = []
simulateSteps net (State q_st src_st) n seed = let newaction = trace("calling action determine function...") $ chooseAction net seed 
                                                   secseed   = randomR (1:: Int,10) seed
                                                   nxt_st    = getNextSim net newaction (State q_st src_st)
                                                   st'       = case nxt_st of Nothing -> error "no next states"; Just st -> st; 
                                               in (newaction,(State q_st src_st)): simulateSteps net st' (n-1) (snd secseed)
    where  chooseAction :: (RandomGen a) => ColoredNetwork -> a -> Action
           chooseAction net' seed' = let newseed          = snd $ randomR (1:: Int, 6) seed' 
                                         snk_act_seed     = snd $ randomR (1:: Int, 8) seed'
                                         mrg_act_seed     = snd $ randomR (1:: Int, 9) seed'
                                         newSourceActions = {-# SCC "getSourceActions" #-} getSourceActions_bis net' src_st seed' -- src_act_seed
                                         newSinkActions   = {-# SCC "getSinkActions" #-}   getSnkActions_bis net' snk_act_seed
                                         newMrgActions    = {-# SCC "getMergeActions" #-}  getMergeActions_bis net' mrg_act_seed
                                         newaction'       = (newSourceActions, newSinkActions, newMrgActions)
                                       {-  sources          = zip (map (fst) (getAllSourcesWithID net')) (ratioToBool (replicate (length $ getAllSourcesWithID net') ((0.5)::Float)) seed')
                                         sinks            = zip (map (fst) (getAllSinksWithID net')) (ratioToBool (replicate (length $ getAllSinksWithID net') ((0.5)::Float)) snk_act_seed)
                                         merges           = map fst (getAllMergesWithID net)
                                         newaction'       = buildAction net' sources sinks merges newseed -}
                                         legalActx        = legalAction net' (State q_st src_st) newaction'
                                     in if legalActx then trace("action found") $ newaction' else chooseAction net newseed 

testAction :: (RandomGen a) => ColoredNetwork -> State -> a -> Int -> [Action]
testAction _ _ _ 0 = []
testAction net (State q_st src_st) seed num = let newseed          = snd $ randomR (1:: Int, 6) seed
                                                  snk_act_seed     = snd $ randomR (1:: Int, 8) seed
                                                  mrg_act_seed     = snd $ randomR (1:: Int, 9) seed
                                                  newSourceActions = {-# SCC "getSourceActions" #-} getSourceActions_bis net src_st seed -- src_act_seed
                                                  newSinkActions   = {-# SCC "getSinkActions" #-}   getSnkActions_bis net snk_act_seed
                                                  newMrgActions    = {-# SCC "getMergeActions" #-}  getMergeActions_bis net mrg_act_seed
                                                  newaction       = (newSourceActions, newSinkActions, newMrgActions)
                                              in newaction: testAction net (State q_st src_st) newseed (num-1)

-- simulate network using the initial state of said network and ratios
simulateInitNetworkR :: (RandomGen a) => ColoredNetwork -> Int -> [Float] -> [Float] -> a -> ([Action],[State])
simulateInitNetworkR net n src snk seed = ((map fst simulate),(map snd simulate)) 
   where simulate = simulateStepsFR net (initialState net) n src snk seed 

-- simulate network with a starting state of choice and ratios
simulateChoiceNetworkR :: (RandomGen a) => ColoredNetwork -> Int -> [Float] -> [Float] -> a -> State -> ([Action],[State])
simulateChoiceNetworkR net n src snk seed s = ((map fst simulate'),(s:map snd simulate')) 
   where simulate' = simulateStepsR net (s) n src snk seed 

-- Simulatesteps with ratios for sources when generating an execution trace, uses filters on all possible actions
simulateStepsR :: (RandomGen a) => ColoredNetwork -> State -> Int -> [Float] -> [Float] -> a -> [(Action,State)] 
simulateStepsR _ _ 0 _ _ _ = []
simulateStepsR net s n src snk seed = let newaction = chooseActionR net s (getActions net)
                                          newseed   = randomR (1:: Int,6) seed
                                          newstate  = getNext net newaction s
                                      in (newaction,s): simulateStepsR net (if length newstate > 1 then newstate!!(fst $ randomR(0,(length newstate-1)) seed) else head $ newstate) (n-1) src snk (snd newseed)
   where  chooseActionR :: ColoredNetwork -> State -> [Action] -> Action
          chooseActionR net' s' act' = let src_ratio  = zip (map (fst) (getAllSourcesWithID net')) src
                                           snk_ratio  = zip (map (fst) (getAllSinksWithID net')) snk
                                           v          = map (cond s') src_ratio
                                           sourceBool = ratioToBool (map snd v) seed
                                           sink_seed  = snd $ randomR (1:: Int,10) seed --this is added because when ratios of source and sink are the same, ratioToBool will return the same boolean list
                                           sinkBool   = ratioToBool (map snd snk_ratio) sink_seed
                                           filter_src = filterActionSource (map fst src_ratio) act' sourceBool
                                           filter_snk = filterActionSink (map fst snk_ratio) filter_src sinkBool
                                           legal      = checkActionR net' s' filter_snk
                                           baselegal  = checkActionR net' s' act'
                                       in case drop (fst $ randomR(0,length legal-1) seed) legal of
                                           x:_ -> x
                                           []  -> case drop (fst $ randomR(0, length baselegal-1) seed) baselegal of
                                                           x:_ -> x
                                                           []  -> error "no legal actions"
                                        -- y!!(fst $ randomR (0,length y-1) seed)
          checkActionR :: ColoredNetwork -> State -> [Action] -> [Action]
          checkActionR net'' s'' act'' = filter (legalAction net'' s'') act''
          cond :: State -> (ComponentID, Float) -> (ComponentID, Float)
          cond ss s_r = if (fst s_r) `elem` (sourceStateNext ss)
                           then (fst s_r,1)
                           else s_r

simulateInitNetworkNC :: (RandomGen a) => ColoredNetwork -> Int -> [Float] -> [Float] -> a -> ([Action],[State])
simulateInitNetworkNC net n r b seed = ((map fst simulate),(map snd simulate)) 
   where simulate = let zipped = zipAll net r b 
                    in simulateStepsNC net (initialState net) n 0 zipped seed
         zipAll :: ColoredNetwork -> [Float] -> [Float] -> [(ComponentID,Float,Float,Float)]
         zipAll net' r' b' = let sourceIDs = map (fst) (getAllSourcesWithID net')
                                 nulls     = replicate (length sourceIDs) 0
                             in zip4 sourceIDs r' b' nulls

simulateStepsNC :: (RandomGen a) => ColoredNetwork -> State -> Int -> Int -> [(ComponentID,Float,Float,Float)] -> a -> [(Action,State)]
simulateStepsNC _ _ 0 _ _ _ = []
simulateStepsNC net state n t form seed = let newaction = chooseActionNC net state form t
                                              newseed   = randomR (1:: Int,20) seed
                                              newstate  = chooseStateNC net newaction state
                                              boolform  = zip form $ determNC form t
                                              newform   = map (\x -> checkForm net state x) boolform
                                          in  (newaction,state): simulateStepsNC net newstate (n-1) (t+1) newform (snd newseed)
    where chooseActionNC :: ColoredNetwork -> State -> [(ComponentID,Float,Float,Float)] -> Int -> Action
          chooseActionNC net' s form' currt = let possactions  = getActions net'  
                                                  legalactions = filter (\x -> legalAction net' s x) possactions
                                                  srcinject    = determNC form' currt
                                                  srclist      = map get1st4 form'
                                                  filltactions = filterActionSource srclist legalactions srcinject
                                              in case drop (fst $ randomR(0,length filltactions-1) seed) filltactions of
                                                  x:_ -> x
                                                  []  -> case drop (fst $ randomR(0, length legalactions-1) seed) legalactions of
                                                           x:_ -> x
                                                           []  -> error "no legal actions"   
          determNC :: [(ComponentID,Float,Float,Float)] -> Int -> [Bool]
          determNC [] _ = []
          determNC (x:xs) tt = resNC x tt:determNC xs tt
          resNC :: (ComponentID,Float,Float,Float) -> Int -> Bool
          resNC (_,r,b,sum') ttt = if ((sum'+1) <= (r*(fromIntegral ttt)+b)) then True else False
          chooseStateNC :: ColoredNetwork -> Action -> State -> State
          chooseStateNC net''' act''' s''' = let newstates = getNext net''' act''' s'''
                                             in case drop (fst $ randomR(0, length newstates-1) seed) newstates of
                                                 x:_ -> x
                                                 []  -> error"no available states"
          checkForm :: ColoredNetwork -> State -> ((ComponentID,Float,Float,Float),Bool) -> (ComponentID,Float,Float,Float)
          checkForm netx' sx' ((ids,rr,bb,i),bl) = let srcIsland  = getSourceIsl (netToIslands netx') netx' ids
                                                       nextComp   = getOuts srcIsland net
                                                   in if bl && (and $ map (\x -> checkQueueState x sx') nextComp) then (ids,rr,bb,i+1) else (ids,rr,bb,i)

-- Function Based on ratios that builds the action instead of filtering possible actions 
simulateStepsFR :: (RandomGen a) => ColoredNetwork -> State -> Int -> [Float] -> [Float] -> a -> [(Action,State)]
simulateStepsFR _ _ 0 _ _ _ = []
simulateStepsFR net s n srcrat snkrat seed = let newact   = generateAction net srcrat snkrat seed
                                                 newseed  = snd $ randomR (1:: Int,20) seed 
                                                 newstate = chooseState net newact s
                                             in (newact,s):simulateStepsFR net newstate (n-1) srcrat snkrat newseed
                                         --    in if legalAction net s newact then (newact,newstate):simulateStepsFR net newstate (n-1) srcrat snkrat snkseed 
                                         --    else error "generated action not legal"
   where generateAction ::(RandomGen a) => ColoredNetwork -> [Float] -> [Float] -> a -> Action -- infinite looop here possibly
         generateAction net' src snk sd = let xtraseed = snd $ randomR (1:: Int, 14) sd 
                                              sources  = map (fst) (getAllSourcesWithID net')
                                              sourceB  = zip sources (ratioToBool src sd)
                                              sinks    = map (fst) (getAllSinksWithID net)
                                              sinkB    = zip sinks (ratioToBool snk xtraseed)
                                              merges   = map fst (getAllMergesWithID net)
                                              newact   = buildAction net sourceB sinkB merges seed
                                           in if legalAction net' s newact then newact else generateAction net' src snk xtraseed 
         chooseState :: ColoredNetwork -> Action -> State -> State
         chooseState net''' act''' s''' = let newstates = getNext net''' act''' s'''
                                          in case drop (fst $ randomR(0, length newstates-1) seed) newstates of
                                              x:_ -> x
                                              []  -> error"no available states"
{--
-- Function based on Network calculus that builds the action instead of filtering possible actions
simulateStepsNC :: (RandomGen a) => ColoredNetwork -> State -> Int -> Int -> [(ComponentID,Float,Float,Float)] -> [(ComponentID,Float,Float,Float)] -> a -> [(Action,State)]
simulateStepsNC _ _ 0 _ _ _ = []
simulateStepsNC net state n t arrive serve seed let sourceB = 
--}

buildAction ::(RandomGen a) => ColoredNetwork -> [(ComponentID,Bool)] -> [(ComponentID,Bool)] -> [ComponentID] -> a -> Action
buildAction net source sink merge seed = let sourceactions = map (\(x,y) -> if ((length $ getSourceActions net x) > 1)
                                                                            then if y == False 
                                                                                 then (head' $ getSourceActions net x) 
                                                                                 else (head' $ tail $ getSourceActions net x)
                                                                            else head' $ getSourceActions net x) source
                                             sinkactions   = map (\(x,y) -> if ((length $ getSinkActions net x) > 1)
                                                                            then if y == False 
                                                                                 then (head'' $ getSinkActions net x) 
                                                                                 else (head'' $ tail $ getSinkActions net x)
                                                                            else head'' $ getSinkActions net x) sink
                                             mergeactions  = if length merge > 0 
                                                             then (map (\y -> case drop (fst $ randomR (0, (length (getMergeActions net y)-1)) seed) (getMergeActions net y) of
                                                                                x:_ -> x
                                                                                []  -> error "merge has no actions" ) merge)
                                                             else []
                                         in (sourceactions,sinkactions,mergeactions)
   where head' :: [a] -> a
         head' [] = error "buildaction source error"
         head' (x:_) = x
         head'' :: [a] -> a
         head'' [] = error "buildaction sink error"
         head'' (x:_) = x 
 
-- Function that filters a list of possible actions using a list of sources and a list of bools which indicate injection or not. False => Idle while True => Inject
filterActionSource :: [ComponentID] -> [Action] -> [Bool] -> [Action]
filterActionSource _ act [] = act
filterActionSource sources act ratio = let source     = head sources
                                           curr_ratio = head ratio
                                           idle       = filter (\y -> or $ map (\x -> fst x == source && snd x /= Idle) (get1st y)) act
                                           inject     = filter (\y -> or $ map (\x -> fst x == source && snd x == Idle) (get1st y)) act
                                       in if curr_ratio == False then 
                                               filterActionSource (tail sources) idle (tail ratio)
                                          else filterActionSource (tail sources) inject (tail ratio)

-- Function that filters a list of possible actions using a list of sinks and a list of bools which indicate consumption or not. False => Rejct while True => Consume
filterActionSink :: [ComponentID] -> [Action] -> [Bool] -> [Action]
filterActionSink _ act [] = act
filterActionSink sinks act ratio = let sink       = head sinks
                                       curr_ratio = head ratio
                                       reject     = filter (\y -> or $ map (\x -> fst x == sink && snd x /= Reject) (get2nd y)) act
                                       consume    = filter (\y -> or $ map (\x -> fst x == sink && snd x == Reject) (get2nd y)) act
                                    in if curr_ratio == False then 
                                            filterActionSink (tail sinks) reject (tail ratio)
                                       else filterActionSink (tail sinks) consume (tail ratio) 
                                
-- function that determines what action sources or sinks do. False indicates Idle/Reject while True indicates an Inject/Consume
-- JS: This seems overly complex to me. Idle and Reject are part of the list of 
-- possible actions for sources and sinks. So, we can randomly pick from this
-- list and then there is no need for this ratio to bool function. 
ratioToBool :: (RandomGen a) => [Float] -> a -> [Bool]
ratioToBool [] _ = []
ratioToBool ratios seed = let tempseed = randomR (0:: Float,1) seed
                          in if (head ratios) < (fst tempseed) then True: ratioToBool (tail ratios) (snd tempseed)
                             else False: ratioToBool (tail ratios) (snd tempseed)  

-- check next states of source and filters sources in the free state out of the list
sourceStateNext :: State -> [ComponentID]
sourceStateNext (State _ s) = map fst (filter (not.(\(_,y) -> y == Free))s)

-- function that combines legalAct and legalAct'
legalAction :: ColoredNetwork -> State -> Action -> Bool
legalAction net s act = {-# SCC "legalAct" #-} (legalAct act s) && {-# SCC "legalAct'" #-} (legalAct' net act s)

-- this function combines the list of actions and states into a list of strings. This setup is
-- current state => action. the next line is then next state => action.
combineActState :: [Action] -> [State] -> [String] 
combineActState act s = combineActState' (zip act s) (length act) 0
   where combineActState' :: [(Action,State)] -> Int -> Int -> [String]
         combineActState' _ 0 _ = []
         combineActState' actS l pos = actStateToString (actS!!pos) : combineActState' actS (l-1) (pos+1)
         actStateToString :: (Action,State) -> String
         actStateToString actS' = (show $ snd actS') ++ " => " ++ (show $ fst actS')

--makes a list of strings from a list of actions and states
simulOrd :: [Action] -> [State] -> [String]
simulOrd act s = let sact = stringAct act
                     ss   = stringState s
                 in merge ss sact
   where merge :: [a] -> [a] -> [a]
         merge xs     []     = xs
         merge []     ys     = ys
         merge (x:xs) (y:ys) = x : y : merge xs ys

-- converts list of states to list of strings
stringState :: [State] -> [String]
stringState []     = error "list of states is empty"
stringState [s]    = [show s]
stringState (s:sx) = show s:stringState sx

-- converts lists of actions to list of strings
stringAct :: [Action] -> [String]
stringAct []         = error "list of actions is empty"
stringAct [act]      = [show act]
stringAct (act:actx) = show act:stringAct actx 

-- function to get the set of islands of the madl network
netToIslands :: forall a. Show a => Network Component a -> [Island a]
netToIslands net = islSetToList $ transferIslands net

-- filter to get the island the input is part of
getSourceIsl :: [Island a] -> ColoredNetwork -> ComponentID -> (Island a)
getSourceIsl isl net comp = head $ filter (\x -> comp `elem` (getIns x net)) isl

-- filter to get the island the output is part of
getSinkIsl :: [Island a] -> ColoredNetwork -> ComponentID -> (Island a)
getSinkIsl isl net comp = head $ filter (\x -> comp `elem` (getOuts x net)) isl

-- function that gets the outputchannels of a component
getOutSrc :: ColoredNetwork -> ComponentID -> [ChannelID]
getOutSrc net comp = getOutChannels net comp
 
-- function that propagates the packet according to the given source and network. All states are needed for the determination of the queue spot in the nextComponent queue
getSourceTrans :: ColoredNetwork -> ComponentID -> Action -> [State] -> ([(ChannelID,Color)],Int)
getSourceTrans net src act s = let allIslands    = netToIslands net
                                   islsrc        = getSourceIsl allIslands net src
                                   srcchann      = head $ getOutSrc net src
                                   (Just c)      = extractColorMby (snd $ head $ get1st $ act)
                                   nextComponent = head $ getOuts islsrc net --mby random?
                                   (Just queNxt) = getQueueState nextComponent (head $ tail s)
                               in (computeOuts (srcchann,(c)) net islsrc,length $ fst queNxt)

-- Function to extract the color from a sourceaction
extractColorMby :: SourceAction -> Maybe Color
extractColorMby (Inject c) = Just c
extractColorMby _ = Nothing

{--
--test function with a fixed source (the first of all sources of a madl network) and given action
sourceTrans :: ColoredNetwork -> Action -> [(ChannelID,Color)]
sourceTrans net act = if (snd $ head $ get1st act) == Idle then error "no injection"
                      else getSourceTrans net (fst $ head $ getAllSourcesWithID net) act
--}

--function to trace a packet from beginning to end, assume injection in the first action, initial injection
traceColorStart :: ColoredNetwork -> [Action] -> [State] -> [([(ChannelID,Color)],Int,State)]
traceColorStart net act s = let chkInject   = (snd $ head $ get1st $ head act) /= Idle
                                getsource   = fst $ head $ getAllSourcesWithID net
                                source      = getSourceTrans net getsource (head act) s
                                sourceChann = fst source 
                                queueLength = snd source
                                 --add check for queues full when injecting
                            in if chkInject == False then traceColorStart net (tail act) (tail s)
                               else (sourceChann,queueLength,(head s)): traceColor (sourceChann, queueLength,(head s)) net (tail act) (tail s) queueLength

-- variant of tracecolor which also checks the next components for full queues
-- function to trace a packet from beginning to end, assume injection in the first action given a specific source
-- f_inj tracks the amount of false injects that are encountered during trace starting
traceColorStartR :: ColoredNetwork -> ComponentID -> [Action] -> [State] -> Int -> ([([(ChannelID,Color)],Int,State)],Int)
traceColorStartR net src act s f_inj = let srcAct     = get1st (head act)
                                           chkInject  = srcInjectCheck src srcAct
                                           srcIsland  = getSourceIsl (netToIslands net) net src
                                           --mergechk   = mergeCheck net (head act) srcIsland
                                           nextComp   = getOuts srcIsland net 
                                           source     = getOutSrc net src
                                           (Just c)   = extractColorMby (snd $ head $ get1st $ head $ act)    -- these 5 lines check for propagation(filter out switch problems)
                                           propagated = map fst (computeOuts((head $ source),c) net srcIsland) -- list of channels it propagates to
                                           channComp  = map (\x -> getInChannels net x) nextComp
                                           checkChann = map (\x -> or $ map (\y -> y `elem` propagated) x) channComp -- list of bools for each component
                                           compCh     = filter(\(_,y) -> y == True) (zip nextComp checkChann) -- filters out the components that are not in the possible propagations
                                           checkQueue  = and $ map (\x -> checkQueueState x (head s)) (map (fst) compCh)
                                           sourceTr    = getSourceTrans net src (head act) s
                                           sourceChann = fst sourceTr 
                                           queueLength = snd sourceTr
                                       in if chkInject == False 
                                          then traceColorStartR net src (tail act) (tail s) f_inj
                                          else if checkQueue == True -- && mergechk == True 
                                               then ((sourceChann,queueLength,(head s)): traceColor (sourceChann, queueLength,(head s)) net (tail act) (tail s) queueLength,f_inj)
                                               else traceColorStartR net src (tail act) (tail s) (f_inj + 1)
    where srcInjectCheck :: ComponentID -> [SourceActWithID] -> Bool
          srcInjectCheck src' act' = if length (filter(\(x,y) -> x == src' && y /= Idle) act') > 0 then True else False
          --mergeCheck :: ColoredNetwork -> Action -> (Island a) -> Bool
          --mergeCheck net' act'' (Island c x) = if (length $ getMergesFromIsland net' (Island c x)) > 0
                                          --then or $ map (\k -> k `elem` c) (map (snd) (get3rd $ act''))
                                         -- else True

checkQueueState :: ComponentID -> State -> Bool
checkQueueState queue s' = let (Just currQueueState) = getQueueState queue s'
                           in if (length $ fst $ currQueueState) == (snd currQueueState) then False 
                              else True 

-- function that traces a packet after the initial inject
traceColor :: ([(ChannelID,Color)],Int,State) -> ColoredNetwork -> [Action] -> [State] -> Int -> [([(ChannelID,Color)],Int,State)]
traceColor curr net act s queuespot = let currComponent     = get3rd $ getChannelContext net (fst $ head $ get1st curr)
                                          allIslands        = netToIslands net 
                                          nextIsland        = getSourceIsl allIslands net currComponent
                                          -- gets next component by propagating, determining the target of the resulting channel
                                          nextComponent     = getTarget net $ head $ map (fst) (propagateNext ((head $ getOutSrc net currComponent),(snd $ last $ get1st curr)) net nextIsland) 
                                          allSinks          = map (fst) (getAllSinksWithID net)
                                          sinkNext          = snd $ head $ get2nd $ head act
                                          (Just queueState) = getQueueState nextComponent (head s)
                                          (Just queueStNxt) = getQueueState nextComponent (head $ tail s)
                                          nextstep          = ((propagateNext ((head $ getOutSrc net currComponent),(snd $ last $ get1st curr)) net nextIsland),queuespot,(head s))
                                          final             = ((propagateNext ((head $ getOutSrc net currComponent),(snd $ last $ get1st curr)) net nextIsland),(-20),(head s))
                                      in if nextComponent `elem` allSinks
                                         then if sinkNext /= Reject
                                              then if queuespot == 1
                                                   then final:[]
                                                   else waitTraceStep (queuespot - 1)
                                              else waitTraceStep queuespot
                                         else if (length $ fst queueState) /= snd queueState
                                              then if queuespot == 1
                                                   then nextstep:traceColor nextstep net (tail act) (tail s) (length $ fst queueStNxt)
                                                   else waitTraceStep (queuespot - 1)
                                              else waitTraceStep queuespot 
   where waitTraceStep :: Int -> [([(ChannelID,Color)],Int,State)]
         waitTraceStep updatedSpot = ((get1st curr),updatedSpot,head s):traceColor ((get1st curr),updatedSpot,head s) net (tail act) (tail s) updatedSpot
         propagateNext :: Show a => (ChannelID, Color) -> ColoredNetwork -> (Island a) -> [(ChannelID, Color)]
         propagateNext curr' net' isl = computeOuts curr' net' isl

-- function that that tracks multiple packets for a given action/state trace
trackPackets :: ColoredNetwork -> [Action] -> [State] -> Int -> [[([(ChannelID,Color)],Int,State)]]
trackPackets _ _ _ 0 = []
trackPackets net act s packets = let (Just firstInject) = findIndex (\x -> (snd $ head $ get1st x) /= Idle) act
                                     corrInject         = firstInject + 1
                                     splitAction        = snd $ splitAt corrInject act
                                     splitStates        = snd $ splitAt corrInject s
                                 in traceColorStart net act s: trackPackets net splitAction splitStates (packets-1)

-- function that that tracks multiple packets for a given action/state trace and for every source
trackPacketsR :: ColoredNetwork -> [Action] -> [State] -> Int -> [[[([(ChannelID,Color)],Int,State)]]]
trackPacketsR _ _ _ 0 = []
trackPacketsR net act s packets = let allSources = map (fst) (getAllSourcesWithID net)
                                  in map (\x -> trackPacketsSRC net x act s packets 0) allSources

-- function that tracks packets of a specific source
trackPacketsSRC :: ColoredNetwork -> ComponentID -> [Action] -> [State] -> Int -> Int -> [[([(ChannelID,Color)],Int,State)]]
trackPacketsSRC _ _ _ _ 0 _ = []
trackPacketsSRC net src act s packets skip_inj = let (Just firstInject) = findIndex (\x -> (snd $ head $ get1st x) /= Idle) act
                                                     corrInject         = firstInject + 1
                                                     splitAction        = snd $ splitAt corrInject act
                                                     splitStates        = snd $ splitAt corrInject s
                                                     tracking_result    = fst $ traceColorStartR net src act s 0
                                                     new_skip_inj       = snd $ traceColorStartR net src act s 0
                                                 in if skip_inj > 0 then trackPacketsSRC net src splitAction splitStates packets (skip_inj-1) --first is a dummy state
                                                    else tracking_result: trackPacketsSRC net src splitAction splitStates (packets-1) new_skip_inj

-- function that compiles results and outputs them (average cycle count, worst case cycle count)
simulBasic :: ColoredNetwork -> [Action] -> [State] -> Int -> (Float,Int)
simulBasic net act s packets = let results   = trackPackets net act s packets
                                   allCycles = map (length) results
                                   average   = (fromIntegral $ sum allCycles)/(fromIntegral $ length allCycles)
                                   worstcase = maximum allCycles
                               in (average,worstcase)                


--replacement function for getInputs without redundancy
getActions :: ColoredNetwork -> [Action]
getActions net = let sourceacts = map (\x -> getSourceActions net x) $ map (fst) $ getAllSourcesWithID net
                     allsrcacts = sequence sourceacts
                     sinkacts   = map (\x -> getSinkActions net x) $ map (fst) $ getAllSinksWithID net 
                     allsnkacts = sequence sinkacts
                     mergeacts  = map (\x -> getMergeActions net x) $ map (fst) $ getAllMergesWithID net
                     allmrgacts = sequence mergeacts
                 in [(x,y,z) | x<-allsrcacts, y<-allsnkacts, z<-allmrgacts]

----------triple tuple selection functions----------
get1st :: (a,b,c) -> a
get1st (a,_,_) = a

get2nd :: (a,b,c) -> b
get2nd (_,b,_) = b

get3rd :: (a,b,c) -> c
get3rd (_,_,c) = c
----------------------------------------------------

get1st4 :: (a,b,c,d) -> a
get1st4 (a,_,_,_) = a

-----------------------------------------Island versions of ISLE functions--------------------------------------------
---these are duplicated because otherwise all code here needed to be rewritten----------------------------------------

getMergesFromIsland :: Show a => ColoredNetwork -> (Island a) -> [ComponentID]
getMergesFromIsland net isl = let chans = islToChanIDs isl in Set.toList (Set.fromList (sort (getMergeIDs net chans)))
  where getMergeIDs :: ColoredNetwork -> [ChannelID] -> [ComponentID]
        getMergeIDs _ [] = []
        getMergeIDs n (x:xs) = let i = getComponent n $ getInitiator n x
                                   o = getComponent n $ getTarget n x
                               in case i of
                                    Merge _ -> case o of
                                                 Merge _ -> getInitiator n x: getTarget n x: getMergeIDs n xs
                                                 _ -> getInitiator n x: getMergeIDs n xs
                                    _ -> case o of
                                           Merge _ -> getTarget n x: getMergeIDs n xs
                                           _ -> getMergeIDs n xs
