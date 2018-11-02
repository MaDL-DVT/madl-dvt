{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

{-|
Module      : Madl.Deadlock.DeadlockDetection
Description : Calculates deadlock and idle equations.
Copyright   : (c) Freek Verbeek, Sanne Wouda 2015-2016, Tessa Belder 2015-2016

This module calculates deadlock and idle equations.
-}
module Madl.Deadlock.DeadlockDetection (
    BlockVariables(..),
    unfold_formula
) where

-- import Debug.Trace

import Data.Foldable (toList)
import Data.List (delete, partition)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import qualified Data.Graph as G
import qualified Data.List as L
import qualified Data.Array as A
import qualified Data.Bimap as BM

import Utils.Map
import Utils.Text

import Madl.Deadlock.Formulas

import Madl.Network
import Madl.MsgTypes


-- Error function
fileName :: Text
fileName = "DeadlockDetection"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | Returns true if the given list is not empty, and all elements of the list are equal
allTheSame :: (Foldable t, Eq a) => t a -> Bool
allTheSame xs = (not $ null xs) && all ((==) x) xs where
    x = head (toList xs)

-- | Unfold a given formula to a map of block and idle literals and their corresponding formula
--   Typical formulas are BlockSource, BlockAny, or IdleAll, or combinations thereof.
unfold_formula :: (Show c) => XColoredNetwork c -> BlockVariables -> Formula -> Map Literal Formula
unfold_formula net vars = -- unfold_formulas .
    unfold_formula' net vars Set.empty . literals


unfold_formula' :: Show c => XColoredNetwork c -> BlockVariables -> Set Literal -> [Literal]
    -> Map Literal Formula
unfold_formula' _ _ _ [] = Map.empty
unfold_formula' net vars done (l:ls) =
    if Set.member l done then unfold_formula' net vars done ls
    else case f of
        Nothing -> unfold_formula' net vars done ls
        Just f' -> Map.insert l f' lm where
            lm = unfold_formula' net vars (Set.insert l done) (ls ++ literals f')
        where
            f = expand_literal net vars l

literals :: Formula -> [Literal]
literals (OR fs) = concatMap literals (Set.toList fs)
literals (AND fs) = concatMap literals (Set.toList fs)
literals (NOT f) = literals f
literals T = []
literals F = []
literals (Lit l) = [l]

_unfold_formulas :: Map Literal Formula -> Map Literal Formula
_unfold_formulas fm' = Map.foldlWithKey unfold_formulas' fm' fm' where
    unfold_formulas' :: Map Literal Formula -> Literal -> Formula -> Map Literal Formula
    unfold_formulas' fm  lit f   = fmap expand fm where
        expand (OR fs) = OR (Set.map expand fs)
        expand (AND fs) = AND (Set.map expand fs)
        expand (NOT f') = NOT (expand f')
        expand T = T
        expand F = F
        expand (Lit l) = if l == lit then f else (Lit l)

-- | Compute the formula corresponding to the literal.
expand_literal :: Show c => XColoredNetwork c -> BlockVariables -> Literal -> Maybe Formula
expand_literal net _vars (BlockSource cID) = Just $
    let [o] = getOutChannels net cID in
    case getComponent net cID of
        Source _ msg -> blockLiteral' (src 58) net o msg
        _ -> fatal 56 "BlockSource can only be used for source component"
-- expand_literal net vars (BlockAny xID colors) = Just $
--     block_any (src 96) net xID colors vars
-- expand_literal net vars (IdleAll xID colors) = Just $
--     idle_all (src 98) net xID colors varsqgd
expand_literal net vars (BlockAny loc xID colors) = Just $
    block_firstcall' loc net xID colors vars
expand_literal net vars (IdleAll loc xID colors) = Just $
    idle_firstcall' loc net xID colors vars
expand_literal _ _ (Is_Full{}) = Nothing
expand_literal _ _ (Is_Not_Full{}) = Nothing
expand_literal _ _ (ContainsNone{}) = Nothing
expand_literal _ _ (Any_At_Head{}) = Nothing
expand_literal _ _ (All_Not_At_Head{}) = Nothing
expand_literal _ _ (Select{}) = Nothing
expand_literal _ _ (MSelect{}) = Nothing
expand_literal _ _ (InState{}) = Nothing
expand_literal _ _ (TSelect{}) = Nothing
expand_literal _ _ (Sum_Compare{}) = Nothing

-- | Additional information that is used in the calculation of the block and
--   idle equations
data BlockVariables = BlockVars {
    liveX :: Seq ComponentID, -- ^ Live sources / queues? Not used currently
    nfqsX :: [ComponentID] -- ^ Queues that can never be full
}

procTrans :: [ChannelID] -> [ChannelID] -> AutomatonTransition -> (Int,Int,[ChannelID],[ChannelID])
procTrans ins outs (AutomatonT s e inid _ _ outid _ _) = (s, e, [ins !! inid], outs')
  where outs' = case outid of
                  Just o -> [outs !! o]
                  _ -> []

procAut :: (Show c) => XColoredNetwork c -> ComponentID -> [(Int,Int,[ChannelID],[ChannelID])]
procAut net comp = case getComponent net comp of
                      (Automaton _ _ _ _ ts _) -> map (\t -> procTrans ins outs t) ts
                      _ -> error "procTrans: Wrong component type"
  where ins = getInChannels net comp
        outs = getOutChannels net comp

allStates :: [(Int,Int,[ChannelID],[ChannelID])] -> [Int]
allStates tr = let i = map (\(x,_,_,_) -> x) tr
                   t = map (\(_,x,_,_) -> x) tr
                   res = L.nub (i ++ t)
               in res

removeTrans :: ChannelID -> [(Int,Int,[ChannelID],[ChannelID])] -> [(Int,Int,[ChannelID],[ChannelID])]
removeTrans cid ts = filter (\(_,_,i,o) -> not (elem cid i) && not (elem cid o)) ts

getBounds :: [(Int,Int)] -> (Int,Int)
getBounds xs = let lb = map (\(l,_) -> l) xs
                   rb = map (\(_,r) -> r) xs
                   b = L.nub $ lb ++ rb
               in (minimum b, maximum b)


autToSCC :: [(Int,Int,[ChannelID],[ChannelID])] -> [(Int,Int,[Int])]
autToSCC ts = let ts' = map (\(i,o,_,_) -> (i,o)) ts
                  g = A.assocs $ G.buildG (getBounds ts') ts'
                  g' = map (\(x,xs) -> (x,x,xs)) g
              in g'

getSCC :: [(Int,Int,[Int])] -> [[Int]]
getSCC ts = map (\t -> G.flattenSCC t) $ G.stronglyConnComp ts

removeTrivial :: [(Int,Int,[Int])] -> [[Int]] -> [[Int]]
removeTrivial ts scc = filter (\x -> if length x == 1 then check ts x else True) scc

check :: [(Int,Int,[Int])] -> [Int] -> Bool
check ts t = let t' = head t
                 x = filter (\(a,_,_) -> a == t') ts
                 x' = head (map (\(_,_,y) -> y) x)
                 res = (x' /= []) && ((L.intersect x' t) /= [])
             in res

sccWithout :: (Show c) => XColoredNetwork c -> ComponentID -> ChannelID -> [[Int]]
sccWithout net comp chan = let aut = procAut net comp
                               aut' = removeTrans chan aut
                               aut'' = autToSCC aut'
                               scc = getSCC $ autToSCC aut'
                               res = removeTrivial aut'' scc
                           in res

sccFormula :: (Show c) => XColoredNetwork c -> ComponentID -> ChannelID -> [Int] -> [Int] -> BM.Bimap (Int,Int) ([ChannelID],[ChannelID]) -> [AutomatonTransition] -> Formula
sccFormula net comp chan scc states tm ts = let
                                                f = concat (map (\x -> map (\y -> let (chani,chano) = tm BM.! (x,y)
                                                                                      incol = map (\a -> let (ColorSet b) = getColorSet net a in b) chani
                                                                                      outcol = map (\a -> let (ColorSet b) = getColorSet net a in b) chano
                                                                                      incol' = if incol /= [] then Set.toList (head incol) else []
                                                                                      outcol' = if outcol /= [] then Set.toList (head outcol) else []
                                                                                      funs = filter (\(AutomatonT a b _ _ _ _ _ _) -> a == x && b == y) ts
                                                                                      iport = let (AutomatonT _ _ i _ _ _ _ _) = (head funs) in i
                                                                                      oport = let (AutomatonT _ _ _ _ _ o _ _) = (head funs) in o
                                                                                      funs' = map (\a -> eventFunction a) funs
                                                                                      incol'' = filter (\a -> foldr (\k l -> k || l) False (map (\b -> b iport a) funs')) incol'
                                                                                      outcol'' = filter (\a -> foldr (\k l -> k || l) False (map (\b -> b (fromJust oport) a) funs')) outcol'
                                                                                  in if (elem y scc) || (not $ elem (x,y) (BM.keys tm)) then T else makeDead (tm BM.! (x,y)) (incol'',outcol'')) states) scc)
                                                f' = AND (Set.fromList f)
                                            in AND (Set.fromList ([OR (Set.fromList (map (\x -> Lit $ InState comp x) states))] ++ [f']))
    where makeDead :: ([ChannelID],[ChannelID]) -> ([Color],[Color]) ->  Formula
          makeDead ([],[]) _ = error "makeDead: both input and output channels are absent"
          makeDead (x,[]) (m,_) = Lit $ IdleAll (src 188) (head x) (Just $ ColorSet (Set.fromList m))
          makeDead ([],x) (_,m) = Lit $ BlockAny (src 189) (head x) (Just $ ColorSet (Set.fromList m))
          makeDead (x,y) (m,m') = OR (Set.fromList ([Lit $ IdleAll (src 188) (head x) (Just $ ColorSet (Set.fromList m))] ++ [Lit $ BlockAny (src 189) (head y) (Just $ ColorSet (Set.fromList m'))]))

-- | Given an automaton, produces a formula that evaluates to `True` iff this
--   automaton is deadlocked
automatonDead :: (Show c) => XColoredNetwork c -> ComponentID -> BlockVariables -> Formula
automatonDead net cID _vars = case getComponent net cID of
    -- An automaton is deadlocked if it has a deadstate
    a@(Automaton _ ins _ n ts _) -> OR (Set.fromList ([exists [0..n-1] deadState] ++ f'))  where
        -- A deadstate is a state such that
        -- 1. The automaton is currently in this state
        -- 2. All outgoing transition of this state are dead
        deadState s = conjunct (Lit $ InState cID s) (forall (filter (\AutomatonT{startState=t}  -> t == s) ts) transitionDead)
        -- A transition if dead if it is dead for all possible incoming colors
        -- from all incoming channels of the automata
        transitionDead :: AutomatonTransition -> Formula
        transitionDead t = forall [0..ins-1] (\i -> forallMaybe (inColors i) (transitionDeadFor t i))
        -- A transition is dead for a certain incoming color `c` from a certain channel `x` iff
        -- either 'x' is idle for 'c'
        --    or if this transition produces a message of color 'd' on channel 'o', and 'o' is blocked for 'd'
        -- If this transition cannot be triggered by color 'c' on channel 'x', then this equation is not applicable
        transitionDeadFor AutomatonT{eventFunction=e,packetTransformationFunction=f} i color = if not $ e i color then Nothing else
            Just $ disjunct (idleLiteral' (src 100) net (inChan i) color) outputBlocked where
                outputBlocked :: Formula
                outputBlocked = case f i color of
                    Nothing -> F
                    Just (o, c) -> blockLiteral' (src 101) net (outChan o) c
    _ -> fatal 94 "AutomatonDead should only be called on automata."
    where
        outChan = lookupM' (src 105) $ getOutChannels net cID
        inChan  = lookupM' (src 106) $ getInChannels net cID
        inColors = getColors . snd . getChannel net . inChan
        ins = getInChannels net cID
        outs = getOutChannels net cID
        aut = L.nub $ procAut net cID
        states = allStates aut
        transMap = BM.fromList (map (\(a,b,c,d) -> ((a,b),(c,d))) aut)
        chanscc = map (\x -> (x,sccWithout net cID x)) (ins ++ outs)
        f = map (\(c,sccs) -> (c, OR (Set.fromList (if sccs == [] then [F] else map (\scc -> sccFormula net cID c scc states transMap (transitions (getComponent net cID))) sccs)))) chanscc
        f' = (map (\(_,x) -> x) f)

{-
automatonDead :: XColoredNetwork c -> ComponentID -> BlockVariables -> Formula
automatonDead net cID _vars = case getComponent net cID of
    -- An automaton is deadlocked if it has a deadstate
    (Automaton _ ins _ n ts _) -> exists [0..n-1] deadState where
        -- A deadstate is a state such that
        -- 1. The automaton is currently in this state
        -- 2. All outgoing transition of this state are dead
        deadState s = conjunct (Lit $ InState cID s) (forall (filter (\AutomatonT{startState=t}  -> t == s) ts) transitionDead)
        -- A transition if dead if it is dead for all possible incoming colors
        -- from all incoming channels of the automata
        transitionDead :: AutomatonTransition -> Formula
        transitionDead t = forall [0..ins-1] (\i -> forallMaybe (inColors i) (transitionDeadFor t i))
        -- A transition is dead for a certain incoming color `c` from a certain channel `x` iff
        -- either 'x' is idle for 'c'
        --    or if this transition produces a message of color 'd' on channel 'o', and 'o' is blocked for 'd'
        -- If this transition cannot be triggered by color 'c' on channel 'x', then this equation is not applicable
        transitionDeadFor AutomatonT{eventFunction=e,packetTransformationFunction=f} i color = if not $ e i color then Nothing else
            Just $ disjunct (idleLiteral' (src 100) net (inChan i) color) outputBlocked where
                outputBlocked :: Formula
                outputBlocked = case f i color of
                    Nothing -> F
                    Just (o, c) -> blockLiteral' (src 101) net (outChan o) c
    _ -> fatal 94 "AutomatonDead should only be called on automata."
    where
        outChan = lookupM' (src 105) $ getOutChannels net cID
        inChan  = lookupM' (src 106) $ getInChannels net cID
        inColors = getColors . snd . getChannel net . inChan
-}

-- | Produces a block equation for the target component of a channel.
block_firstcall' :: (Show c) => Source -> XColoredNetwork c -> ChannelID -> Maybe ColorSet -> BlockVariables -> Formula
block_firstcall' loc net xID colors vars = -- mkLit (BlockAny xID currColorSet) $
    case getComponent net cID of
        Queue{} -> if cID `elem` (nfqsX vars)
            -- If the queue is never full it is never blocked
            then F
            -- Queue is full and any packet is blocked
            else conjunct (Lit $ Is_Full cID) $
            if allTheSame fs
            -- then the queue is blocked iff this formula is true and if any of the given colors is at the head of the queue)
            then conjunct (head fs) (Lit $ atHeadLiteral net cID colors')
            -- Otherwise we check if there is a single color such that its block formula is true, and this color is at the head of the queue.
            else exists (zip currColors fs) irdy_and_blocked where
                irdy_and_blocked (c, f) = conjunct (Lit $ atHeadLiteral net cID c) f
                fs :: [Formula]
                fs = map block_one_color currColors
                block_one_color :: Color -> Formula
                block_one_color c = blockLiteral' (src 118) net (outchan) c
        -- An automaton is blocked for some color from a certain incoming channel if either
        --   the automaton doesn't contain a transition that accepts this color from this channel, or
        --   the automaton is dead
        -- todo(tssb): This doesn't cover the situation where some transition does accept the given color from the given channel,
        --               but this transition can never be triggered. Possible unsoundness?
        Automaton _ _ _ _ ts _ -> conjunct (negation (idleLiteral' loc net xID currColors)) (disjunct (fromBool $ any colorNeverExcepted currColors) f) where
            f = automatonDead net cID vars
            colorNeverExcepted color = all (\AutomatonT{eventFunction=event} -> not $ event port color) ts
        _ -> block_any loc net xID colors vars
    where
        (cID, port) = getTargetWithPort net xID
        outchan = head $ getOutChannels net cID
        currColors = getColors colors'
        colors' = case colors of Nothing -> snd (getChannel net xID); Just cs -> cs

blockLiteral' :: IsColorSet a => Source -> XColoredNetwork c -> ChannelID -> a -> Formula
blockLiteral' loc net xID = Lit . blockLiteral loc net xID . toColorSet

-- | Produces a block equation for the given channel with the given set of
-- colors. Given a channel x, and a colorset C,
--     block_any(x, C) <=> exists c in C : G!trdy(x, c)
block_any :: IsColorSet a => Source -> XColoredNetwork c -> ChannelID ->
    Maybe a -> BlockVariables -> Formula
block_any source net xID colors vars =
    -- When the target component is live (i.e. never blocked) this channel is
    -- not blocked (Currently not used)
    if cID `elem` (liveX vars) then F
    -- If the set of given colors is empty, the block equation is False.
    else if empty colors' then F
    -- Precondition: the given set of colors is a subset of the colors that can
    -- reach this channel.
    else if not (colors' `subTypeOf` colorset xID) then fatal 93 $
        "Illegal call to block arsing from " +++showT source +++ ": colorset "
        +++ showT (toColorSet colors') +++ " is not a subtype of "
        +++ showT (colorset xID)
    -- Calculate block equation based on the target component of the given
    -- channel:
    else case getComponent net cID of
        Queue{} -> Lit $ BlockAny (src 197) xID Nothing
        -- For a vars component we just check whether any of the given colors is
        -- blocked on the outgoing channel of this component.
        Vars{} -> blockLiteral' (src 200) net (outChan 0) colors'
        -- Cut similar to vars
        Cut{} -> blockLiteral' (src 200) net (outChan 0) colors'
        -- Some outgoing channel is blocked
        Fork{} -> exists outChans (\x -> blockLiteral' (src 138) net x colors')
        -- Output blocked or any input other than p is idle
        ControlJoin{} -> disjunct outputBlocked (existsMaybe inChans inputIdle)
            where
            outputBlocked = if empty $ outColorset 0
                then T
                else blockLiteral' (src 140) net (outChan 0) blockedcolors
            blockedcolors = if port == 0
                then (toColorSet colors')
                else (outColorset 0)
            inputIdle i = if i == xID
                then Nothing
                else Just $ idleLiteral' (src 142) net i (colorset i)
        FControlJoin _ f -> disjunct
            -- The other incoming channel is idle
            (idleLiteral' (src 143) net (inChan other) (inColorset other))
            (exists (inColors other) irdy_and_blocked) where
             -- Some color on other channel irdy and blocked
            irdy_and_blocked c = conjunct
                (irdy_any (src 145) net (inChan other) c vars)
                (disjunct block_c block_match) where
                block_c = if null no_match
                    then F
                    else blockLiteral' (src 146) net (outChan 0) c
                block_match = blockLiteral' (src 147) net (outChan 0) match
                (match, no_match) = partition pCond currColors
                pCond = if port == 0
                    then flip (matched f) c
                    else not . matched f c
            other = if port == 0 then 1 else 0
        Switch{} -> exists outChans blocked where -- Any output blocked
            blocked x = blockLiteral' (src 158) net x $ typeIntersection (colorset x) colors'
        Merge{} -> disjunct curr_selected other_selected where
            -- Current input selected, and output blocked
            curr_selected = conjunct
                (Lit $ Select cID port)
                -- TODO(snnw) replace by a blockLiteral (currently triggers bug)
                (block_any (src 160) net (outChan 0) (Just colors') vars)
            -- Other input selected and irdy, and output blocked
            other_selected = existsMaybe inPorts selected_and_blocked
            selected_and_blocked p = if p == port then Nothing else
                Just $ conjunct (Lit $ Select cID p) (exists (inColors p) (irdy_and_blocked p))
            irdy_and_blocked :: Int -> Color -> Formula
            irdy_and_blocked p c = conjunct
                (irdy_any (src 164) net (inChan p) c vars)
                (Lit $ BlockAny (src 164) (outChan 0) Nothing)  -- XXX: why Nothing instead of Just c?
        -- Sink is fair, so never G!trdy
        Sink{} -> F
        -- Dead sink is always !trdy
        DeadSink{} -> T
        -- Output blocked for result of function
        Function _ f _ -> blockLiteral' (src 167) net (outChan 0) ((resultingTypeStrict (makeArguments [colors']) f)::ColorSet)
        Source{} -> fatal 114 "block should not be called on Source"
        PatientSource{} -> fatal 115 "block should not be called on Source"
        Match _ f -> if port == 0 then --match input: all matching colors of some color idle, or irdy and blocked
            disjunct (exists currColors all_matching_idle) (exists (inColors 1) irdy_and_blocked_d)
            else --data input: match input channel idle, or irdy and blocked
            disjunct (idleLiteral' (src 173) net (inChan 0) (inColorset 0)) (exists (inColors 0) irdy_and_blocked_m) where
                all_matching_idle mColor = idleLiteral' (src 174) net (inChan 1) matchingColors where
                    matchingColors = filter (flip (matched f) mColor) (inColors 1)
                irdy_and_blocked_d dColor = conjunct (irdy_any (src 176) net (inChan 1)  dColor vars) $ disjunct
                    (if any (matched f dColor) currColors then blockLiteral' (src 177) net (outChan 0) dColor else F)
                    (if any (not . matched f dColor) currColors then blockLiteral' (src 178) net (outChan 1) dColor else F)
                irdy_and_blocked_m mColor = conjunct (irdy_any (src 179) net (inChan 0) mColor vars) $ disjunct
                    (blockLiteral' (src 180) net (outChan 0) (filter (flip (matched f) mColor) currColors))
                    (Lit $ BlockAny (src 181) (outChan 1) Nothing) -- XXX: I can't believe this actually works
        MultiMatch _ f -> if port < length outChans
            -- match input: all matching colors of some color idle, or selection
            -- is made and blocked
            then disjunct (exists currColors all_matching_d_idle) $
                 disjunct (exists dataPorts selected_and_blocked_d)
                          other_selected_and_blocked
            -- data input: all matching colors of some color idle, or selection
            -- is made and blocked
            else disjunct (exists currColors all_matching_m_idle) $
                 disjunct (exists matchPorts selected_and_blocked_m)
                          other_selected_and_blocked
            where
                all_matching_d_idle mColor = forall dataPorts all_matching_idle where
                    all_matching_idle dIn = idleLiteral' (src 190) net (inChan dIn) (filter (flip (matched f) mColor) (inColors dIn))
                all_matching_m_idle dColor = forall matchPorts all_matching_idle where
                    all_matching_idle mIn = idleLiteral' (src 192) net (inChan mIn) (filter (matched f dColor) (inColors mIn))

                selected_and_blocked_d dIn = conjunct (Lit $ MSelect cID (port, dIn)) (exists matching_colors irdy_and_blocked) where
                    matching_colors = filter (\c -> any (matched f c) currColors) (inColors dIn)
                    irdy_and_blocked dColor = conjunct (irdy_any (src 196) net (inChan dIn) dColor vars) (blockLiteral' (src 196) net (outChan port) dColor)
                selected_and_blocked_m mIn = conjunct (Lit $ MSelect cID (mIn, port)) $ (exists (inColors mIn) irdy_and_blocked) where
                    irdy_and_blocked mColor = conjunct (irdy_any (src 198) net (inChan mIn) mColor vars) $
                        blockLiteral' (src 199) net (outChan mIn) (filter (flip (matched f) mColor) currColors)

                other_selected_and_blocked = exists (filter (/= port) matchPorts) (\mIn -> exists (filter (/= port) dataPorts) (sel_and_blocked mIn))
                sel_and_blocked mIn dIn = conjunct (Lit $ MSelect cID (mIn, dIn)) (exists colorClasses (uncurry irdy_and_blocked_m)) where
                    colorClasses = equivClasses f (inColors dIn) (inColors mIn)
                    irdy_and_blocked_m :: [Color] -> [Color] -> Formula
                    irdy_and_blocked_m dColors mColors =
                        conjunct
                            (irdy_any (src 204) net (inChan mIn) (mColors) vars)
                            (exists dColors irdy_and_blocked_d)
                    irdy_and_blocked_d dColor =
                        conjunct
                            (irdy_any (src 205) net (inChan dIn) dColor vars)
                            (blockLiteral' (src 205) net (outChan mIn) dColor)

                matchPorts = [0..length outChans-1]
                dataPorts = [length outChans..length inChans-1]
        LoadBalancer{} -> exists currColors all_outputs_blocked where
            -- note that blocking equations take into account that an output is selected only if it is trdy.
            -- therefore, the deadlock equation checks that for one color all outputs are blocked.
                all_outputs_blocked c = forall outChans (\chan -> blockLiteral' (src 212) net chan c)
        -- Joitch is blocked if either the other incoming channel is idle, or if some color is ready on the other channel and the output is blocked
        Joitch _ preds -> disjunct (idleLiteral' (src 213) net (inChan other) (inColorset other)) (exists (inColors other) irdy_and_blocked) where
            other = 1 - port
            irdy_and_blocked c = conjunct (irdy_any (src 215) net (inChan other) c vars) (exists [0..length preds-1] $ blocked c)
            blocked c p = disjunct (blockLiteral' (src 216) net (outChan $ 2*p + port) matchingColors) $
                case matchingColors of [] -> F; _ -> (blockLiteral' (src 217) net (outChan $ 2*p + other) c); where
                matchingColors = filter (matched' (lookupM (src 213) p preds) c) currColors

            matched' p = if port == 0 then flip (matched p) else matched p
        Automaton{} -> blockLiteral' (src 287) net xID colors' -- Produce a block literal
        GuardQueue{} -> if port == 0 then block_ib
            else block_ig where
                block_ib = conjunct q_full (output_blocked (inColors 0))
                block_ig = disjunct (conjunct (Lit $ Select cID 0) (output_blocked (inColors 0))) (output_blocked colors')
                output_blocked c = blockLiteral' (src 346) net (outChan 0) c

                q_full = Lit $ Is_Full cID

            -- GuardQUeue block
            -- block(i_b, c) = Full(q) && block(o, q.head)
            -- block(i_g, c) = (sel == 0 && block(o, q.head)) || block(o, c)  -- ((||neverEmpty(gq)))

    where
        (cID, port) = getTargetWithPort net xID
        currColors = getColors colors'
        inChans = getInChannels net cID
        inChan :: Int -> ChannelID
        inChan = lookupM' (src 222) inChans
        inPorts = [0..length inChans-1]
        outChans = getOutChannels net cID
        outChan :: Int -> ChannelID
        outChan = lookupM' (src 226) outChans
        colorset = snd . getChannel net
        outColorset = colorset . outChan
        inColors = getColors . colorset . inChan
        inColorset = colorset . inChan
        colors' = case colors of Nothing -> snd (getChannel net xID); Just cs -> toColorSet cs

idleLiteral' :: IsColorSet a => Source -> XColoredNetwork c -> ChannelID -> a -> Formula
idleLiteral' loc net colors = Lit . idleLiteral loc net colors

-- | Produces an idle equation for the initiator component of a channel.
idle_firstcall' :: (Show c) => Source -> XColoredNetwork c -> ChannelID -> Maybe ColorSet -> BlockVariables -> Formula
idle_firstcall' loc net xID colors vars =
    case getComponent net cID of
        Queue{} -> disjunct empty_and_idle some_other_packet_blocked_at_head where
            empty_and_idle = conjunct (Lit $ containsNoneLiteral net cID colors') -- Queue is empty
                             (idleLiteral' (src 244) net (inChan 0) colors') -- Incoming channel is idle
            some_other_packet_blocked_at_head = exists otherColors irdy_and_blocked
            irdy_and_blocked c = conjunct (Lit $ atHeadLiteral net cID c) -- Color is at the head of the queue
                                          (blockLiteral' (src 247) net xID c) -- Color is blocked on outgoing channel
            otherColors = foldr delete (colorsOfChannel xID) currColors
        --Queue{} -> conjunct' (lit' $ containsNoneLiteral net cID colors') -- Buffer is empty
        --                     (idle_all' (src 244) net (inChan 0) colors' vars fm) -- Incoming channel is idle
        -- An automaton is idle for a set of colors, if all of these colors are never produced by the automaton, or if the automaton is dead
        Automaton _ ins _ _ ts _-> disjunct (fromBool $ all colorNeverProduced currColors) (automatonDead net cID vars) where
            colorNeverProduced color = all (\t -> all (\i -> all (doesNotProduce t i) (inColors i)) [0..ins-1]) ts where
                doesNotProduce AutomatonT{eventFunction=e,packetTransformationFunction=f} i c = not (e i c) || (case f i c of Nothing -> True; Just (o, c') -> (o, c') /= (port, color))
        _ -> idle_all loc net xID colors vars
    where
        (cID, port) = getInitiatorWithPort net xID
        currColors = getColors colors'
        inChan = lookupM' (src 250) $ getInChannels net cID
        colorsOfChannel = getColors . snd . getChannel net
        inColors = colorsOfChannel . inChan
        colors' = case colors of Nothing -> snd (getChannel net xID); Just cs -> cs

-- | Produces an idle equation for the given channel with the given set of colors.
-- Given a channel x, and a colorset C, idle_all(x, C) <=> forall c in C : G!irdy(x, c)
idle_all :: IsColorSet a => (Text, Int) -> XColoredNetwork c -> ChannelID -> Maybe a -> BlockVariables -> Formula
idle_all loc net xID colors vars =
    if cID `elem` (liveX vars) then F else
    if empty colors' then T else
    if not (colors' `subTypeOf` colorset xID) then fatal 310 $
        "Illegal call to idle arsing from " +++showT loc +++ ": colorset " +++ showT (toColorSet colors') +++ " is not a subtype of " +++ showT (colorset xID) else
    case getComponent net cID of
        Queue{} -> idleLiteral' loc net xID colors' -- Produce an idle literal
        -- The incoming channel is idle for the given colors
        Vars{} -> idleLiteral' loc net (inChan 0) colors'
        Cut{} -> idleLiteral' loc net (inChan 0) colors'
        Fork{} -> forall currColors idle_one_color where
            idle_one_color c = disjunct (idleLiteral' (src 270) net (inChan 0) c) -- Idle on input
                                        (existsMaybe outChans (blocked c)) where -- Any output blocked
            blocked c x = if x == xID then Nothing else
                Just $ blockLiteral' (src 273) net x c -- output blocked for given color
        ControlJoin{} -> exists inPorts inputIdle where -- Any input idle
            inputIdle p = if p == 0 then idleLiteral' (src 275) net (inChan p) colors' else idleLiteral' (src 276) net (inChan p) (inColorset p)
        FControlJoin _ f -> forall currColors idle_one_color where
            idle_one_color c = conjunct (idle_on_A c) (idle_on_B c)
            -- A color is idle from A if it is idle on A, or if B is idle for all matching colors
            idle_on_A c = disjunct (idle_one 0 c) (forall (filter (matched f c) $ inColors 1) (idle_one 1))
            -- A color is idle from B if it is idle on B, or if A is idle for all non-matching colors
            idle_on_B c = disjunct (idle_one 1 c) (forall (filter (not . flip (matched f) c) $ inColors 0) (idle_one 0))
            idle_one p c = idleLiteral' (src 280) net (inChan p) c
        Switch{} -> idleLiteral' (src 281) net (inChan 0) colors' -- Idle on input
        Merge{} -> disjunct (forall inPorts all_idle) (exists inPorts selected_and_blocked) where -- All inputs idle, or some input selected and blocked
            all_idle x = idleLiteral' (src 283) net (inChan x) (typeIntersection (inColorset x) colors')
            selected_and_blocked x = conjunct (Lit $ Select cID x) $ exists (getColors $ typeDifference (inColorset x) colors') (irdy_and_blocked x)
            irdy_and_blocked x c = conjunct (irdy_any (src 284) net (inChan x) c vars) (blockLiteral' (src 285) net xID c)
        Function _ f _ -> idleLiteral' (src 286) net (inChan 0) preFunctionColors where --Idle for all colors that may be transformed to any of the given colors
            preFunctionColors = filter rightResult (inColors 0)
            rightResult c = eval (IM.singleton 0 c) f `elem` currColors
        Source _ msg -> disjunct produces_wrong_colors some_other_packet_irdy_and_blocked where
            produces_wrong_colors = fromBool . empty $ typeIntersection msg colors'
            some_other_packet_irdy_and_blocked :: Formula
            some_other_packet_irdy_and_blocked = exists otherColors (blockLiteral' (src 248) net xID) --todo(tssb) irdy part
            otherColors = getColors $ typeDifference msg colors'
        PatientSource _ msg -> disjunct produces_wrong_colors some_other_packet_irdy_and_blocked where
            produces_wrong_colors = fromBool . empty $ typeIntersection msg colors'
            some_other_packet_irdy_and_blocked = exists otherColors (blockLiteral' (src 252) net xID) --todo(tssb) irdy part
            otherColors = getColors $ typeDifference msg colors'
        Sink{} -> fatal 328 "idle should not be called on Sink"
        DeadSink{} -> fatal 329 "idle should not be called on DeadSink"
        Match _ f -> disjunct (forall currColors (idle output)) (exists currColors (irdy_and_blocked $ not output)) where
            output = if port == 0 then True else False
            idle match dColor = disjunct (idleLiteral' (src 296) net (inChan 1) dColor) $
                idleLiteral' (src 297) net (inChan 0) (filter ((== match) . matched f dColor) (inColors 0))
            irdy_and_blocked match dColor = conjunct (irdy_any (src 297) net (inChan 1) dColor vars) $ conjunct
                (blockLiteral' (src 299) net (outChan $ if match then 0 else 1) dColor)
                (irdy_any (src 299) net (inChan 0) (filter ((== match) . matched f dColor) (inColors 0)) vars)
        MultiMatch _ f -> disjunct (forall currColors idle) $ disjunct
            (exists dataPorts selected_and_blocked) other_selected_and_blocked where

            idle dColor = disjunct (forallMaybe dataPorts idle_d) (forall matchPorts idle_m) where
                idle_d dIn = if not $ dColor `matches` inColorset dIn then Nothing
                    else Just $ idleLiteral' (src 305) net (inChan dIn) dColor
                idle_m mIn = idleLiteral' (src 306) net (inChan mIn) (filter (matched f dColor) (inColors mIn))

            selected_and_blocked dIn = conjunct (Lit $ MSelect cID (port, dIn)) (exists colorClasses (uncurry irdy_and_blocked)) where
                colorClasses :: [([Color], [Color])]
                colorClasses = equivClasses f (typeDifference (inColorset dIn) colors') (inColorset port)
                irdy_and_blocked :: [Color] -> [Color] -> Formula
                irdy_and_blocked dColors mColors = conjunct (irdy_any (src 311) net (inChan port) mColors vars) (exists dColors irdy_and_blocked_d)
                irdy_and_blocked_d dColor = conjunct (irdy_any (src 312) net (inChan dIn) dColor vars) (blockLiteral' (src 313) net (outChan port) dColor)

            other_selected_and_blocked = exists (filter (/= port) matchPorts) (\mIn -> exists dataPorts (sel_and_blocked mIn))
            sel_and_blocked mIn dIn = conjunct (Lit $ MSelect cID (mIn, dIn)) (exists colorClasses (uncurry irdy_and_blocked_m)) where
                colorClasses = equivClasses f (inColors dIn) (inColors mIn)
                irdy_and_blocked_m dColors mColors = conjunct (irdy_any (src 317) net (inChan mIn) mColors vars) (exists dColors irdy_and_blocked_d)
                irdy_and_blocked_d dColor = conjunct (irdy_any (src 318) net (inChan dIn) dColor vars) (blockLiteral' (src 319) net (outChan mIn) dColor)

            matchPorts = [0..length outChans-1]
            dataPorts = [length outChans..length inChans-1]
        LoadBalancer{} -> idleLiteral' (src 323) net (inChan 0) colors' -- Idle on input
        Joitch _ preds -> forall currColors idle_one_color where
            idle_one_color c = disjunct (idleLiteral' (src 325) net (inChan inport) c) (idleLiteral' (src 326) net (inChan other) matchingColors) where
                matchingColors = filter (matched' (lookupM (src 321) (port `div` 2) preds) c) (inColors other)
            inport = port `mod` 2
            other = 1 - inport
            matched' p = if inport == 0 then matched p else flip (matched p)
        Automaton{} -> idleLiteral' loc net xID colors' -- Produce an idle literal
        GuardQueue{} -> disjunct inputsIdle blockedOther where
            inputsIdle = conjunct (idleLiteral' (src 489) net (inChan 1) (typeIntersection currColors (colorset (inChan 0)))) (idleLiteral' (src 489) net (inChan 1) (typeIntersection currColors (colorset (inChan 1))))
            blockedOther = output_blocked $ typeDifference (colorset $ outChan 0) colors'
            output_blocked = blockLiteral' (src 492) net (outChan 0)
            -- GuardQueue idle
            -- o.idle = (idle(ib, c) && idle(ig, c)) || (exists other color c' such that block(o, c')
    where
        (cID, port) = getInitiatorWithPort net xID
        currColors = getColors colors'
        inChans = getInChannels net cID
        inChan :: Int -> ChannelID
        inChan = lookupM' (src 331) inChans
        inPorts = [0..length inChans-1]
        outChans = getOutChannels net cID
        outChan :: Int -> ChannelID
        outChan = lookupM' (src 335) outChans
        colorset = snd . getChannel net
        inColorset = colorset . inChan
        inColors = getColors . colorset . inChan
        colors' = case colors of Nothing -> snd (getChannel net xID); Just cs -> toColorSet cs

-- | Produces an irdy equation for the given channel with the given set of colors
-- Given a channel x, and a colorset C, irdy_any(x, C) <=> exists c in C : irdy(x, c)
irdy_any :: IsColorSet a => (Text, Int) -> XColoredNetwork c -> ChannelID -> a -> BlockVariables -> Formula
irdy_any source net xID currColorSet vars =
    if empty currColorSet then F else
    if not (currColorSet `subTypeOf` colorset xID) then fatal 466 $
        "Illegal call to irdy arsing from " +++showT source +++ ": colorset " +++ showT (toColorSet currColorSet) +++ " is not a subtype of " +++ showT (colorset xID) else
    case getComponent net cID of
        Queue{} -> Lit $ atHeadLiteral net cID currColorSet --Any of the given colors at head of the queue
        Vars{} -> irdy_any (src 353) net (inChan 0) currColorSet vars --incoming channel irdy
        Cut{} -> irdy_any (src 353) net (inChan 0) currColorSet vars --incoming channel irdy
        Fork{} -> exists currColors irdy_one_color where --incoming channel irdy and all other outgoing channel trdy
            irdy_one_color c = conjunct (irdy_any (src 354) net (inChan 0) c vars)
                                        (forallMaybe outChans (is_trdy c))
            is_trdy c x = if x == xID then Nothing else
                Just $ trdy_any (src 358) net x c vars
        ControlJoin{} -> forall inChans inputIrdy where -- input 0 irdy for the given colors, and all other inputs irdy for any color
            inputIrdy x = if x == inChan 0 then irdy_any (src 359) net x currColorSet vars else irdy_any (src 360) net x (colorset x) vars
        FControlJoin _ f -> exists currColors irdy_one_color where
            irdy_one_color c = disjunct (irdy_from_A c) (irdy_from_B c)
            -- irdy_from_A: input 0 irdy for the given color, input 1 irdy for any matching color
            irdy_from_A c = conjunct (irdy_any (src 362) net (inChan 0) c vars) (irdy_any (src 363) net (inChan 1) matching_colors vars) where
                matching_colors = filter (matched f c) $ inColors 1
            -- irdy_from_B: input 1 irdy for the given color, input 0 irdy for any non-matching color
            irdy_from_B c = conjunct (irdy_any (src 364) net (inChan 1) c vars) (irdy_any (src 365) net (inChan 0) non_matching_colors vars) where
                non_matching_colors = filter (not . flip (matched f) c) $ inColors 0
        Switch{} -> irdy_any (src 366) net (inChan 0) currColorSet vars -- incoming channel irdy
        Merge{} -> exists inPorts port_irdy where --any incoming channel selected and irdy
            port_irdy p = conjunct (Lit $ Select cID p) (irdy_any (src 368) net (inChan p) (colors' p) vars)
            colors' = typeIntersection currColorSet . inColorset
        Function _ f _ -> irdy_any (src 370) net (inChan 0) preFunctionColors vars where --incoming channel irdy for a color that is transformed to any of the given colors
            preFunctionColors = filter rightResult (inColors 0)
            rightResult c = eval (IM.singleton 0 c) f `elem` currColors
        Source _ msg -> fromBool . not . empty $ typeIntersection msg currColorSet --source can produce any of the given colors
        PatientSource _ msg -> fromBool . not . empty $ typeIntersection msg currColorSet --source can produce any of the given colors
        Sink{} -> fatal 484 "irdy should not be called on Sink"
        DeadSink{} -> fatal 485 "irdy should not be called on DeadSink"
        Match _ f -> exists currColors $ irdy_and_match output where
            irdy_and_match match dColor = conjunct (irdy_any (src 378) net (inChan 1) dColor vars) $
                (irdy_any (src 379) net (inChan 0) (filter ((== match) . matched f dColor) (inColors 0)) vars)

            output = if port==0 then True else False
        MultiMatch _ f -> exists dataPorts sel_and_irdy where
            sel_and_irdy dIn = conjunct (Lit $ MSelect cID (port, dIn)) (exists currColors' irdy_and_match) where
                currColors' = getColors $ typeIntersection (inColorset dIn) currColorSet
                irdy_and_match dColor = conjunct (irdy_any (src 384) net (inChan dIn) dColor vars) $
                    irdy_any (src 385) net (inChan port) (filter (matched f dColor) (inColors port)) vars
            dataPorts = [length outChans..length inChans-1]
        LoadBalancer{} -> conjunct (Lit $ Select cID port) (irdy_any (src 388) net (inChan 0) currColorSet vars) --this output selected and input irdy
        Joitch _ preds -> exists currColors irdy_one_color where
            irdy_one_color c = conjunct (irdy_any (src 390) net (inChan inport) c vars) (irdy_any (src 391) net (inChan other) matchingColors vars) where
                matchingColors = filter (matched' (lookupM (src 387) (port `div` 2) preds) c) (inColors other)
            inport = port `mod` 2
            other = 1 - inport
            matched' p = if inport == 0 then matched p else flip (matched p)
        Automaton _ ins _ _ ts _ -> existsMaybe [(i, tNr, t) | i <- [0..ins-1], (tNr, t) <- zip [0..] ts] selected_and_irdy where
            selected_and_irdy (i, tNr, AutomatonT{startState=s,eventFunction=eps,packetTransformationFunction=ph}) = case filter correctTrigger $ inColors i of
                [] -> Nothing
                cs -> Just $ conjunct (conjunct (Lit $ InState cID s) (Lit $ TSelect cID i tNr)) (irdy_any (src 399) net (inChan i) cs vars)
                where
                    correctTrigger c = eps i c && (case ph i c of
                        Nothing -> False
                        Just (o, c') -> o == port && c' `matches` (toColorSet currColorSet)
                        )
        GuardQueue{} -> disjunct sel_0 sel_1 where
            sel_0 = conjunct (Lit $ Select cID 0) (Lit $ atHeadLiteral net cID currColorSet)
            sel_1 = conjunct (Lit $ Select cID 1) $ conjunct (Lit $ All_Not_At_Head cID (Just $ inColorset 0)) (irdy_any (src 578) net (inChan 1) (typeIntersection currColors (inColorset 1)) vars)
            -- GuardQueue o.irdy = (sel == 0 && !Empty(gq)) || (sel == 1 && ig.irdy && Empty(gq))
        where
        (cID, port) = getInitiatorWithPort net xID
        currColors = getColors currColorSet
        inChans = getInChannels net cID
        inChan :: Int -> ChannelID
        inChan = lookupM' (src 397) inChans
        inPorts = [0..length inChans-1]
        outChans = getOutChannels net cID
        colorset = snd . getChannel net
        colors = getColors . colorset
        inColors = colors . inChan
        inColorset = colorset . inChan

-- | Produces a trdy equation for the given channel with the given set of colors
-- Given a channel x, and a colorset C, trdy_any(x, C) <=> exists c in C : trdy(x, c)
trdy_any :: IsColorSet a => (Text, Int) -> XColoredNetwork c -> ChannelID -> a -> BlockVariables -> Formula
trdy_any source net xID currColorSet vars =
    if empty currColorSet then F else
    if not (currColorSet `subTypeOf` colorset xID) then fatal 412 $
        "Illegal call to trdy arsing from " +++showT source +++ ": colorset " +++ showT (toColorSet currColorSet) +++ " is not a subtype of " +++ showT (colorset xID) else
    case getComponent net cID of
        Queue{} -> Lit $ Is_Not_Full cID
        Vars{} -> trdy_any (src 418) net (outChan 0) currColorSet vars
        Cut{} -> trdy_any (src 418) net (outChan 0) currColorSet vars
        Fork{} -> exists currColors trdy_one_color where
            trdy_one_color c = forall outChans (\x -> trdy_any (src 419) net x c vars)
        ControlJoin{} -> if port==0
            then conjunct (trdy_any (src 421) net (outChan 0) currColorSet vars)
                          (forallMaybe inPorts is_irdy)
            else conjunct (exists (inColors 0) irdy_and_trdy)
                          (forallMaybe inPorts is_irdy) where
            is_irdy p = if p == 0 || p == port then Nothing else
                Just $ irdy_any (src 424) net (inChan p) (inColorset p) vars
            irdy_and_trdy c = conjunct (irdy_any (src 425) net (inChan 0) c vars)
                                       (trdy_any (src 428) net (outChan 0) c vars)
        FControlJoin _ f -> exists (inColors other) irdy_and_trdy where
            irdy_and_trdy c = conjunct (irdy_any (src 428) net (inChan other) c vars) $ disjunct
                (trdy_any (src 431) net (outChan 0) match vars) (if null no_match then F else trdy_any (src 432) net (outChan 0) c vars) where
                    (match, no_match) = partition (if port == 0 then flip (matched f) c else not . matched f c) currColors
            other = if port == 0 then 1 else 0
        Switch{} -> exists outChans is_trdy where
            is_trdy x = trdy_any (src 435) net x (typeIntersection currColorSet (colorset x)) vars
        Merge{} -> conjunct (Lit $ Select cID port) (trdy_any (src 436) net (outChan 0) currColorSet vars)
        Function _ f _ -> trdy_any (src 437) net (outChan 0) ((resultingTypeStrict (makeArguments [currColorSet]) f)::ColorSet) vars
        Sink{} -> T
        DeadSink{} -> F
        Source{} -> fatal 605 "trdy should not be called on Source"
        PatientSource{} -> fatal 606 "trdy should not be called on PatientSource"
        Match _ f -> exists currColors trdy_one_color where
            trdy_one_color cIn = if port == 0 then existsMaybe (inColors 1) (matched_and_trdy cIn)
                else disjunct (trdy True cIn) (trdy False cIn)
            matched_and_trdy mColor dColor = if not (matched f dColor mColor) then Nothing else
                Just $ conjunct (irdy_any (src 444) net (inChan 1) dColor vars) (trdy_any (src 446) net (outChan 0) dColor vars)
            trdy match dColor = conjunct (trdy_any (src 447) net (outChan $ if match then 0 else 1) dColor vars) $
                irdy_any (src 446) net (inChan 0) (filter ((== match) . matched f dColor) (inColors 0)) vars
        MultiMatch _ f -> if port < length outChans then --match input
            exists dataPorts selected_and_trdy_d
            else --data input
            exists matchPorts selected_and_trdy_m where

                selected_and_trdy_d dIn = conjunct (Lit $ MSelect cID (port, dIn)) $
                    exists (filter (\c -> any (matched f c) currColors) (inColors dIn)) irdy_and_trdy where
                    irdy_and_trdy dColor = conjunct (irdy_any (src 454) net (inChan dIn) dColor vars) $
                        (trdy_any (src 457) net (outChan port) dColor vars)

                selected_and_trdy_m mIn = conjunct (Lit $ MSelect cID (mIn, port)) $
                    exists (inColors mIn) irdy_and_match where
                    irdy_and_match mColor = conjunct (irdy_any (src 459) net (inChan mIn) mColor vars) $
                        trdy_any (src 462) net (outChan mIn) (filter (flip (matched f) mColor) currColors) vars

                matchPorts = [0..length outChans-1]
                dataPorts = [length outChans..length inChans-1]
        LoadBalancer{} -> exists outPorts selected_and_trdy where
            selected_and_trdy p = conjunct (Lit $ Select cID p) (trdy_any (src 467) net (outChan p) currColorSet vars)
        Joitch _ preds -> exists (inColors other) irdy_and_trdy where
            irdy_and_trdy c = conjunct (irdy_any (src 467) net (inChan other) c vars) (exists [0..length preds-1] (both_trdy c))
            both_trdy c p = forallMaybe currColors match_then_trdy where
                match_then_trdy c' = if not $ matched' (lookupM (src 466) p preds) c' c then Nothing else Just $
                    conjunct (trdy_any (src 472) net (outChan $ 2*p + port) c' vars) (trdy_any (src 473) net (outChan $ 2*p + other) c vars)
            other = 1 - port
            matched' p = if port == 0 then matched p else flip (matched p)
        Automaton _ _ _ _ ts _ -> existsMaybe (zip [0..] ts) selected_and_trdy where
            selected_and_trdy (tNr, AutomatonT{startState=s,eventFunction=eps,packetTransformationFunction=ph}) = case filter (eps port) currColors of
                [] -> Nothing
                cs -> Just $ conjunct (conjunct (Lit $ InState cID s) (Lit $ TSelect cID port tNr)) (exists cs trdy) where
                    trdy c = case ph port c of Nothing -> T; Just (o, c') -> trdy_any (src 490) net (outChan o) c' vars
        GuardQueue{} -> if port == 0 then conjunct (Lit $ Select cID port) (Lit $ Is_Not_Full cID)
            else conjunct (Lit $ Select cID port) $ conjunct (Lit $ ContainsNone cID (Just (colorset (inChan 0)))) (trdy_any (src 436) net (outChan 0) currColorSet vars)
            -- GuardQueue trdy
            -- ib.trdy = sel == 0 && !Full(gq)
            -- ig.trdy = sel == 1 && Empty(gq) && o.trdy
    where
        (cID, port) = getTargetWithPort net xID
        currColors = getColors currColorSet
        inChans = getInChannels net cID
        inChan :: Int -> ChannelID
        inChan = lookupM' (src 476) inChans
        inPorts = [0..length inChans-1]
        outChans = getOutChannels net cID
        outChan :: Int -> ChannelID
        outChan = lookupM' (src 480) outChans
        outPorts = [0..length outChans-1]
        colorset = snd . getChannel net
        colors = getColors . colorset
        inColorset = colorset . inChan
        inColors = colors . inChan
