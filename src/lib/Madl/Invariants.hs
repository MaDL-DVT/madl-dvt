{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, FlexibleContexts #-}

{-|
Module      : Madl.Invariants
Description : Derives invariants from a madl network.
Copyright   : (c) Tessa Belder 2015-2016

Provides a data type for invariants. Provides a function to derive invariants from a madl network.
-}
module Madl.Invariants (
    Invariant(..),
    emptyInvariant,
    getInvariants,
    showInvariant,
    showInvariants,
    showInvariants2,
    matrix
) where

-- import Debug.Trace

import qualified Data.IntMap as IM
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Maybe (catMaybes, isJust, mapMaybe, fromMaybe)
import qualified Data.Partition as P
import Data.Ratio(denominator)
import qualified Data.Set as Set
import qualified Data.Text as T

import GHC.Real( Ratio((:%)) )

import Utils.Map
import Utils.Text

import Echelon.Echelon

import Madl.Base
import Madl.MsgTypes
import Madl.Network

-- Error function
fileName :: Text
fileName = "Madl.Invariants"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

--------------------------
-- Invariant generation --
--------------------------

-- | Invariant type, parameterized over the type of multipliers
data Invariant a = Invariant {
    -- | Variables denoting the amount of packets in a queue:
    -- ComponentID must identify a queue.
    -- The color @Nothing@ corresponds to the total amount of packets in the queue.
    -- A color @Just c@ corresponds to the amount of packets of color @c@ in the queue
    queueVariables :: Map ComponentID (Map (Maybe Color) a),
    -- | Variables denoting the state of an automaton:
    -- ComponentID must identify an automaton.
    -- @Int@ identifies a state of the automaton
    automatonVariables :: Map ComponentID (Map Int a),
    -- | A constant value to be added/subtracted.
    constantOne :: a
    }
    -- Invariant of the form variables + constant <= 0
    | LeqInvariant {
        -- | Variables denoting the amount of packets in a queue:
    -- ComponentID must identify a queue.
    -- The color @Nothing@ corresponds to the total amount of packets in the queue.
    -- A color @Just c@ corresponds to the amount of packets of color @c@ in the queue
    queueVariables :: Map ComponentID (Map (Maybe Color) a),
    -- | Variables denoting the state of an automaton:
    -- ComponentID must identify an automaton.
    -- @Int@ identifies a state of the automaton
    automatonVariables :: Map ComponentID (Map Int a),
    -- | A constant value to be added/subtracted.
    constantOne :: a
    }

-- | The empty invariant.
emptyInvariant :: (Eq a, Num a) => Invariant a -> Bool
emptyInvariant invariant = case invariant of
    Invariant qMap aMap c -> Map.null qMap && Map.null aMap && c == 0
    LeqInvariant qMap aMap c -> Map.null qMap && Map.null aMap && c == 0

-- | Main function: generate invariants and apply some invariant transformations. Finally filter empty invariants.
getInvariants :: Show c => XColoredNetwork c -> [Invariant Int]
getInvariants network = filter (not . emptyInvariant) $ fmap (toIntInvariant . cleanInvariant network) (invariants network)

-- | Helper type for readability
-- Row of an augmented matrix
-- Variables on the left side of the matrix are variables we are not interested in.
-- Variables on the right side of the matrix are interesting variables. We use them in the final invariants.
type MatrixRow = (Map DeleteVariable Int, Map KeepVariable (Ratio Int))

-- | Variables we are not interesting in
data DeleteVariable =
    -- | @ChannelTransfers xID c@ corresponds to the number of packets of color @c@
    -- that have been transfered over the channel identified by @xID@
      ChannelTransfers ChannelID Color
    -- | @AutomatonTransition cID n@ corresponds to the number of times the @n@th transition
    -- of the automaton identified by @cID@ has fired.
    | AutomatonTransition ComponentID Int
    deriving (Eq, Ord, Show)

-- | Variables we are interested in
data KeepVariable =
    -- | @QueueVar cID Nothing@ corresponds to the total number of packets in the queue identified by @cID@
    -- | @QueueVar cID (Just c)@ corresponds to the number of packets of color @c@ in the queue identified by @cID@
      QueueVar ComponentID (Maybe Color)
    -- | @AutomatonState cID n@ corresponds to the current state of the automaton identified by @cID@.
    -- If the automaton is in state @n@, then the value of this variable is 1. Otherwise it is 0.
    | AutomatonState ComponentID Int
    -- | Constant value 1.
    | One
    deriving (Eq, Ord, Show)

-- | Invariant generation function
invariants :: Show c => XColoredNetwork c -> [Invariant (Ratio Int)]
invariants = fmap collectResults . echelonFilter . matrix where
    collectResults :: Map KeepVariable (Ratio Int) -> Invariant (Ratio Int)
    collectResults inv = Invariant{
        queueVariables = fmap Map.fromList $ Map.fromListWith (++) [(c, [(t, v)])| (QueueVar c t, v) <- Map.assocs inv],
        automatonVariables = fmap Map.fromList $ Map.fromListWith (++) [(c, [(n, v)])| (AutomatonState c n, v) <- Map.assocs inv],
        constantOne = fromMaybe 0 $ Map.lookup One inv
        }

-- | Invariant matrix
matrix :: Show c => XColoredNetwork c -> [MatrixRow]
matrix network = concatMap getEquation $ getComponentsWithID network where
    getEquation :: (ComponentID, XComponent c) -> [MatrixRow]
    getEquation (node, comp) = case comp of
        Source{} -> []
        PatientSource{} -> []
        Sink{} -> []
        DeadSink{} -> [(Map.singleton (ChannelTransfers ichan c) 1, Map.empty)| c <- getColors itype] where
            -- The number of transfers of each color c on the inputchannel is 0.
            [(ichan, itype)] = input
        Function{} ->
            -- The number of transfers of some color c on the outchannel is equal to the combined number of transfers on the inputchannel
            --  of all colors c' that are transformed to color c by the function.
                [(Map.fromList (
                   (ChannelTransfers ochan otype, -1):[(ChannelTransfers ichan t, 1) | t <- itypes]),
                    Map.empty) | (otype, itypes) <- Map.assocs m] -- for each pair (output type, input type),
                                                                  -- #transfers output = #transfers input for all possible types
                where
                    [(ichan, itype)] = input
                    [(ochan, _)] = output
                    m = Map.fromListWith (++)
                        [(eval args fun, [c]) | c <- getColors itype, let args = IM.singleton 0 c] -- evaluation of function on all colors
                        -- output color left
                        -- input color right
                        -- (c = f a, a), (c = f b, b) ....
                        -- grouped in (c, [a,b]) ...
                    fun = function comp -- function of the Function primitive
        Queue{} -> let
            [(ichan, itype)] = input
            [(ochan, _)] = output
            in case getColors itype of
                -- If the inputType of the queue is empty, the total number of packets in the queue is 0.
                [] -> [(Map.empty, Map.singleton (QueueVar node Nothing) 1)]
                -- Otherwise, the number of transfers of some color c on the inputchannel is equal to the number of packets with color c in the queue
                --  and the number of transfers of color c on the outputchannel combined.
                itypes -> [(Map.fromList [(ChannelTransfers ichan t, 1), (ChannelTransfers ochan t, -1)],
                            Map.singleton (QueueVar node $ Just t) (-1)) | t <- itypes]
        Vars{} -> [(Map.fromList [(ChannelTransfers ichan t, 1), (ChannelTransfers ochan t, -1)], Map.empty) | t <- getColors itype] where
            [(ichan, itype)] = input
            [(ochan, _)] = output
        Cut{} -> [(Map.fromList [(ChannelTransfers ichan t, 1), (ChannelTransfers ochan t, -1)], Map.empty) | t <- getColors itype] where
            [(ichan, itype)] = input
            [(ochan, _)] = output
        Switch{} -> [( Map.fromList (switchEquation ochan c), Map.empty)| (ochan, otype) <- output, c <- getColors otype] where
            --  The number of transfers of some color c on some outputchannel is equal to the number of transfers of color c on the inputchannel.
                switchEquation ochan c = [(ChannelTransfers ichan c, 1), (ChannelTransfers ochan c, -1)]
                [ichan] = inChannels
        Merge{} -> [( Map.fromList (mergeEquation c), Map.empty)| c <- getColors otype] where
            -- The number of transfers of some color c on the outputChannel is equal to the number of transfers of color c on all inputchannels combined.
            mergeEquation c = (ChannelTransfers ochan c, -1):[(ChannelTransfers ichan c, 1)| (ichan, itype) <- input, c `matches` itype]
            [(ochan, otype)] = output
        Fork{} -> [( Map.fromList (forkEquation ochan c), Map.empty)| ochan <- outChannels, c <- getColors itype] where
            -- The number of transfers of some color c on the inputchannel is equal to the number of transfers of color c on each outputchannel.
            forkEquation ochan c = [(ChannelTransfers ichan c, 1), (ChannelTransfers ochan c, -1)]
            [(ichan, itype)] = input
        ControlJoin{} -> dataEquations ++ map tokenEquations tokenInputs where
            (ichan0, itype0):tokenInputs = input
            [(ochan, otype)] = output
            dataEquations = case getColors otype of
                -- If the output colorset of the join is empty, the number of transfers of each color c on the data inputchannel is 0.
                [] -> [(Map.singleton (ChannelTransfers ichan0 t) 1, Map.empty) | t <- getColors itype0]
                -- The number of transfers of some color c on the data inputchannel is equal to the number of transfers of color c on the outputchannel.
                otypes -> [(Map.fromList[(ChannelTransfers ichan0 t, 1), (ChannelTransfers ochan t, -1)], Map.empty) | t <- otypes]
            -- The number of transfers on a token inputchannel is equal to the number of transfers on the outputchannel. Colors don't match.
            tokenEquations (ichan, itype) =
                ( Map.fromList (
                   [(ChannelTransfers ichan t, 1) | t <- getColors itype]
                ++ [(ChannelTransfers ochan t, -1)| t <- getColors otype]),
                  Map.empty )
        FControlJoin _ f -> [(Map.fromList $ uncurry tokenEquation i, Map.empty) | i <- input] ++ mapMaybe dataEquation (getColors otype) where
            (ichan0, itype0):(ichan1, itype1):[] = input
            [(ochan, otype)] = output

            dataEquation :: Color -> Maybe MatrixRow
            dataEquation c = if alwaysFromA c then Just $ (Map.fromList [(ChannelTransfers ichan0 c, 1), (ChannelTransfers ochan c, -1)], Map.empty)
                else if alwaysFromB c then Just $ (Map.fromList [(ChannelTransfers ichan1 c, 1), (ChannelTransfers ochan c, -1)], Map.empty)
                else Nothing

            alwaysFromA :: Color -> Bool
            alwaysFromA c = (not (c `matches` itype1) || not (mayMatch False f itype0 c)) && not (mayMatch False f c itype1)
            alwaysFromB :: Color -> Bool
            alwaysFromB c = (not (c `matches` itype0) || not (mayMatch True f c itype1)) && not (mayMatch True f itype0 c)

            tokenEquation :: ChannelID -> ColorSet -> [(DeleteVariable, Int)]
            tokenEquation ichan itype = [(ChannelTransfers ichan c, 1) | c <- getColors itype]
                                     ++ [(ChannelTransfers ochan c, -1)| c <- getColors otype]
        Match _ f -> [(Map.fromList (dataEquation c), Map.empty) | c <- getColors dType]
                  ++ [(Map.fromList (uncurry tokenEquation eqClass), Map.empty) | eqClass <- equivClasses f tType mType] where
            (mIn, mType):(dIn, dType):[] = input
            (tOut, tType):(_fOut, _):[] = output

            dataEquation c = (ChannelTransfers dIn c, 1) : map (\x -> (ChannelTransfers x c, -1)) (map fst $ filter ((c `matches`) . snd) output)
            tokenEquation dColors mColors = map (\c -> (ChannelTransfers mIn c, 1)) mColors ++ map (\c -> (ChannelTransfers tOut c, -1)) dColors
        MultiMatch _ f -> [(Map.fromList (dataEquation c), Map.empty) | c <- getColors dType]
                       ++ concatMap (uncurry tokenEquations) (zip matchIns output) where
            (matchIns, dataIns) = splitAt (length output) input
            dType  = foldr typeUnion nul (map snd dataIns)

            dataEquation c = map (\x -> (ChannelTransfers x c,  1)) (map fst $ filter ((c `matches`) . snd) dataIns)
                          ++ map (\x -> (ChannelTransfers x c, -1)) (map fst $ filter ((c `matches`) . snd) output)
            tokenEquations (mIn, mType) (o, oType) = [(Map.fromList (uncurry tokenEquation eqClass), Map.empty) |
                                                            eqClass <- equivClasses f oType mType] where
                tokenEquation dColors mColors = map (\c -> (ChannelTransfers mIn c, 1)) mColors ++ map (\c -> (ChannelTransfers o c, -1)) dColors
        LoadBalancer{} -> dataEquations where -- ++ arbiterEquations where
            [(ichan, itype)] = input
            -- The number of tranfers of some color c on the input channel,
            --  is equal to the number of transfers of color c on all outputchannels combined.
            dataEquations = [ ( Map.fromList (dataEquation c), Map.empty)| c <- getColors itype]
            dataEquation c = (ChannelTransfers ichan c, 1):[ (ChannelTransfers ochan c, -1) | ochan <- outChannels]
        Joitch _ preds -> [(Map.fromList (dataEquation1 True  c), Map.empty) | c <- getColors itype0]
                       ++ [(Map.fromList (dataEquation1 False c), Map.empty) | c <- getColors itype1]
                       ++ [(Map.fromList result, Map.empty) | c <- getColors itype0, let result = dataEquation2 True  c, not (null result)]
                       ++ [(Map.fromList result, Map.empty) | c <- getColors itype1, let result = dataEquation2 False c, not (null result)]
                       ++ [(Map.fromList (uncurry tokenEquation te), Map.empty) | te <- tokenEquations] where
            input0@(ichan0, itype0):input1@(ichan1, itype1):[] = input
            (evenOuts, oddOuts) = splitChannels output

            dataEquation1 :: Bool -> Color -> [(DeleteVariable, Int)]
            dataEquation1 evenColor c = (ChannelTransfers ichan c, 1) : [(ChannelTransfers ochan c, -1) | (ochan, otype) <- outs, c `matches` otype] where
                ichan = if evenColor then ichan0 else ichan1
                outs = if evenColor then evenOuts else oddOuts

            dataEquation2 :: Bool -> Color -> [(DeleteVariable, Int)]
            dataEquation2 evenColor c = if any ((> 1) . length) allMatches then [] else
                 (ChannelTransfers ichan c, 1) :
                    [(ChannelTransfers ochan c', -1) | (p, (ochan, otype)) <- zip preds outs, c' <- getColors otype, condition p c c'] where
                    (ichan, itype) = if evenColor then input0 else input1
                    outs = if evenColor then oddOuts else evenOuts
                    condition p c'' c' = if evenColor then matched p c'' c' else matched p c' c''

                    allMatches = [ filter (\c'' -> condition p c'' c') (getColors itype) |
                                        (p, (_, otype)) <- zip preds outs, c' <- getColors otype, condition p c c']

            tokenEquations :: [([(ChannelID, ColorSet)], [(ChannelID, ColorSet)])]
            tokenEquations = [([input0], [input1]), ([input1], evenOuts)] ++ [([evenOut], [oddOut]) | (evenOut, oddOut) <- zip evenOuts oddOuts]
            tokenEquation :: [(ChannelID, ColorSet)] -> [(ChannelID, ColorSet)] -> [(DeleteVariable, Int)]
            tokenEquation chans1 chans2 = [(ChannelTransfers ichan c, 1) | (ichan, itype) <- chans1, c <- getColors itype]
                                       ++ [(ChannelTransfers ichan c, -1)| (ichan, itype) <- chans2, c <- getColors itype]

            splitChannels [] = ([], [])
            splitChannels [_] = fatal 174 "invalid network"
            splitChannels (c1:c2:cs) = (c1:cs', c2:cs'') where
                (cs', cs'') = splitChannels cs

        Automaton _ _ _ n ts -> [(Map.empty, Map.fromList stateEquation)]
                -- (AutomatonState node i, 1) = 1* A.i (A.s in the paper)
                -- [(One, -1) | i == 0]) | i <- [0..n-1]] = - (s == s0)
            ++ [(Map.filter (/= 0) $ Map.fromListWith (+) (transitionEquation i), Map.fromList $ (AutomatonState node i, 1) : [(One, -1) | i == 0]) | i <- [0..n-1]]
            ++ [(Map.filter (/= 0) $ Map.fromListWith (+) (inputEquation  $ Set.toList p), Map.empty) | p <- getPartition partitionI $ Set.fromList allCombinationsI]
--            ++ [(Map.filter (/= 0) $ Map.fromListWith (+) (inputEquation  $ allCombinationsI), Map.empty)]
            ++ [(Map.filter (/= 0) $ Map.fromListWith (+) (outputEquation $ Set.toList p), Map.empty) | p <- getPartition partitionO $ Set.fromList allCombinationsO]
            where
                -- an automaton is exactly in one state.
                stateEquation = (One, -1) : [(AutomatonState node i, 1) | i <- [0..n-1]]

                -- relation between #ingoing transitions to #outgoing transition. Implement equation (1) section 4.
                -- come from (transitionEquation i), now i = sNr (state number). it is the current state.
                -- (AutomatonTransition node tNr, 1) | (tNr, AutomatonT s _ _ _) <- zip [0..] ts, s == sNr]
                -- sum over all transitions starting in s, so outgoing transitions.
                -- [(AutomatonTransition node tNr, -1) | (tNr, AutomatonT _ s _ _) <- zip [0..] ts, s == sNr]
                -- sum over all transitions going to s, so incoming transitions.
                -- Note: node = id of the automaton (current component)
                transitionEquation :: Int -> [(DeleteVariable, Int)]
                transitionEquation sNr = [(AutomatonTransition node tNr,  1) | (tNr, AutomatonT{startState=s}) <- zip [0..] ts, s == sNr]
                                      ++ [(AutomatonTransition node tNr, -1) | (tNr, AutomatonT{endState=s}) <- zip [0..] ts, s == sNr]

                -- [(ChannelTransfers (inChannel i) c, 1) | (i, c) <- triggers]
                -- sum over in/out-coming channels
                -- [(AutomatonTransition node tNr, -1) | tNr <- enabledTs]
                -- sim over transitions triggered by event on the channels.
                inputEquation :: [(Int, Color)] -> [(DeleteVariable, Int)]
                inputEquation triggers = [(ChannelTransfers (inChannel i) c, 1) | (i, c) <- triggers]
                                    ++ [(AutomatonTransition node tNr, -1) | tNr <- enabledTs] where
                    enabledTs = map fst . filter (\(_, t) -> any (uncurry $ eventFunction t) triggers) $ zip [0..] ts
                    -- enabledTs is T(I).
                    -- trigger = I

                outputEquation events = [(ChannelTransfers (outChannel i) c, 1) | (i, c) <- events]
                                    ++ [(AutomatonTransition node tNr, -1) | tNr <- triggeringTs] where
                    triggeringTs = map fst . filter (\(_, t) -> any (mayProduce t) events) $ zip [0..] ts
                    -- triggeringTs = transitions that may trigger one (or more) of the given events
                    mayProduce (AutomatonT{eventFunction=eps,packetTransformationFunction=ph}) event = any (\(i, c) -> eps i c && (ph i c == Just event)) allCombinationsI
                    -- returns true if the given transition is capable of triggering the given event

                -- Compute equivalence partitioning (see paper I~).
                -- eventFunction = epsilon of a transition, trigger of the transition (input channel/output channel/guards)
                -- Results: partitions I~
                partitionI, partitionO :: P.Partition (Int, Color)
                partitionI = P.fromSets $ map (epsToSet . eventFunction) ts where -- map (epsToSet . eventFunction) ts = list of sets of (int,color).
                    epsToSet :: (Int -> Color -> Bool) -> Set (Int, Color)
                    epsToSet eps = Set.fromList $ filter (uncurry eps) allCombinationsI -- filter from all possible types, those triggering each transition t in ts.
                partitionO = P.fromSets $ map producedColors ts where
                    producedColors :: AutomatonTransition -> Set (Int, Color)
                    producedColors (AutomatonT{eventFunction=eps,packetTransformationFunction=ph}) = Set.fromList . catMaybes . map (uncurry ph) $ filter (uncurry eps) allCombinationsI
                    -- find all possible (outputchannel, color) combinations that may be produced by each transition t in ts

                -- Compute all possible combinations of channels and colors
                -- Input = channels: (position,colorsets)
                -- Output = (position, color). We basically split the colorset into colors.
                -- We do this for all input and output channels.
                -- Results correspond to tuples (i,d) and (o,d') in the paper.
                allCombinationsI, allCombinationsO :: [(Int, Color)]
                allCombinationsI = concatMap (\(i, cs) -> zip (repeat i) $ getColors cs) $ zip [0..] inTypes
                allCombinationsO = concatMap (\(i, cs) -> zip (repeat i) $ getColors cs) $ zip [0..] outTypes

                -- Convert partition into list of sets. We compute the list of all I in I~.
                getPartition :: Ord a => P.Partition a -> Set a -> [Set a]
                getPartition partition elems = if Set.null elems then []
                    else newSet : (getPartition partition $ Set.difference elems newSet) where
                        newSet = P.find partition $ Set.elemAt 0 elems
        GuardQueue{} -> [( Map.fromList (mergeEquation c), Map.singleton (QueueVar node Nothing) 1)| c <- getColors otype] where
            -- The number of transfers of some color c on the outputChannel is equal to the number of transfers of color c on all inputchannels combined.
            mergeEquation c = (ChannelTransfers ochan c, -1):[(ChannelTransfers ichan c, 1)| (ichan, itype) <- input, c `matches` itype]
            [(ochan, otype)] = output
        where
            inChannels = getInChannels network node
            inChannel i = lookupM (src 248) i inChannels
            inTypes = inputTypes network node
            input = zip inChannels inTypes
            outChannels = getOutChannels network node
            outChannel i = lookupM (src 264) i outChannels
            outTypes = outputTypes network node
            output = zip outChannels outTypes

-------------------------------
-- Invariant transformations --
-------------------------------

-- | Helper type for readability
type QueueColorRatios = Map (Maybe Color) (Ratio Int)

-- | Clean an invariant by combining types for the same queue
cleanInvariant :: Show c => XColoredNetwork c -> Invariant (Ratio Int) -> Invariant (Ratio Int)
cleanInvariant net invariant = case invariant of
    Invariant qMap aMap c -> Invariant (Map.mapWithKey annotateType qMap) aMap c
    LeqInvariant qMap aMap c -> LeqInvariant (Map.mapWithKey annotateType qMap) aMap c
    where
        cleanQueue :: ColorSet -> QueueColorRatios -> QueueColorRatios
        cleanQueue t typeRatios = if totalType == t && not (null ratios) then
                Map.insertWith (+) Nothing minRatio $ Map.mapMaybeWithKey adjustRatio typeRatios
                else typeRatios where
            adjustRatio :: Maybe Color -> Ratio Int -> Maybe (Ratio Int)
            adjustRatio (Just _) r = if r == minRatio then Nothing else Just (r - minRatio)
            adjustRatio Nothing r = Just r
            totalType = toColorSet (catMaybes $ Map.keys typeRatios)
            minRatio = minimum ratios
            ratios :: [Ratio Int]
            ratios = map snd $ filter (isJust . fst) (Map.assocs typeRatios)
        annotateType :: ComponentID -> QueueColorRatios -> QueueColorRatios
        annotateType cID = cleanQueue (head $ outputTypes net cID)

-- | Transform invariant with rational multipliers to an invariant with integer multipliers
toIntInvariant :: Invariant (Ratio Int) -> Invariant Int
toIntInvariant (Invariant qMap aMap c) = Invariant (fmap (fmap toInt) qMap) (fmap (fmap toInt) aMap) (toInt c)
    where
        toInt :: Ratio Int -> Int
        toInt (n :% d) = n * (f `div` d)
        f = foldl' lcm 1 denominators
        denominators = fmap denominator ratios
        ratios = c : (concat (fmap Map.elems $ Map.elems qMap) ++  concat (fmap Map.elems $ Map.elems aMap))

toIntInvariant (LeqInvariant qMap aMap c) = LeqInvariant (fmap (fmap toInt) qMap) (fmap (fmap toInt) aMap) (toInt c)
    where
        toInt :: Ratio Int -> Int
        toInt (n :% d) = n * (f `div` d)
        f = foldl' lcm 1 denominators
        denominators = fmap denominator ratios
        ratios = c : (concat (fmap Map.elems $ Map.elems qMap) ++  concat (fmap Map.elems $ Map.elems aMap))

--------------------
-- Pretty Printer --
--------------------

-- | Print invariants of a given network in a readable format
showInvariants :: forall c. Show c => XColoredNetwork c -> Text
showInvariants network = T.unlines $ map (showInvariant nameFunction) invs where
    nameFunction :: ComponentID -> c
    nameFunction = getName . (getComponent network)
    invs = getInvariants network

    -- | Print invariants of a given network in a readable format
showInvariants2 :: forall c. Show c => [Invariant Int] -> XColoredNetwork c -> Text
showInvariants2 invs network = T.unlines $ map (showInvariant nameFunction) invs where
    nameFunction :: ComponentID -> c
    nameFunction = getName . (getComponent network)

-- | Print an invariant in a readable format
showInvariant :: forall c d . (Show c, Show d, Num d, Eq d) => (ComponentID -> c) -> Invariant d -> Text
showInvariant nameFunction invariant = case invariant of
    Invariant qMap aMap c -> "0 = " +++ T.intercalate " + " (map showQ (Map.assocs qMap) ++ map showA (Map.assocs aMap) ++ [showT c | c /= 0]) 
    LeqInvariant qMap aMap c -> "0 >= " +++ T.intercalate " + " (map showQ (Map.assocs qMap) ++ map showA (Map.assocs aMap) ++ [showT c | c /= 0]) 
    where
        showQ :: (ComponentID, (Map (Maybe Color) d)) -> Text
        showQ (i, m) = "[" +++ (T.intercalate ", " (map g $ Map.assocs m)) +++ "]" where
            g (Nothing, j) = showT j +++ " * " +++ showT (nameFunction i)
            g (Just t, j) = showT j +++ " * " +++ showT (nameFunction i) +++ "{" +++ showT t +++ "}"
        showA :: (ComponentID, (Map Int d)) -> Text
        showA (i, m) = "[" +++ (T.intercalate ", " (map g $ Map.assocs m)) +++ "]" where
            g (n, j) = showT j +++ " * " +++ showT (nameFunction i) +++ "[" +++ showT n +++ "]"


-- TODO(tssb) : unit-tests for invariants
