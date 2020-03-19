{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}

{-|
Module      : Madl.Deadlock.Formulas
Description : Data types for deadlock and idle equations.
Copyright   : (c) Freek Verbeek, Sanne Wouda 2015-2016, Tessa Belder 2015-2016

This module contains data types for deadlock and idle equations, as well as functions to instantiate and simplify these equations.
-}
module Madl.Deadlock.Formulas (
    Literal(..), Formula(..), Source,
    atHeadLiteral, {-inBufferLiteral,-} notAtHeadLiteral, blockLiteral, idleLiteral,
    containsNoneLiteral,
    disjunct, disjunct',
    conjunct, conjunct',
    negation,
    disjunctive, conjunctive,
    exists, exists',
    forall, forall',
    existsMaybe, forallMaybe, forallMaybe',
    fromBool, simplify_singletons
) where

-- import Debug.Trace

import Data.Foldable (toList)
import Data.Maybe (mapMaybe, fromMaybe)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes
import Madl.Network

-- Error function
fileName :: Text
fileName = "Madl.Deadlock.Formulas"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

type Source = (Text, Int)

src :: Int -> Source
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | The formula data type
data Formula
    = AND (Set Formula) -- ^ conjunction
    | OR (Set Formula) -- ^ disjunction
    | NOT Formula -- ^ negation
    | T -- ^ True
    | F -- ^ False
    | Lit Literal -- ^ Literal
    deriving (Show, Eq, Ord)

-- | Literals that can be used in formula
data Literal
    = Is_Full ComponentID -- ^ Queue is full. @ComponentID@ should identify a queue.
    | Is_Not_Full ComponentID -- ^ Queue is not full. @ComponentID@ should identify a queue.
    | ContainsNone ComponentID (Maybe ColorSet)-- ^ None of the given colors are anywhere in the queue. @ComponentID@ should identify a queue.
    -- @ContainsNone q Nothing \<=\> isEmpty q@.
    | Any_At_Head ComponentID (Maybe ColorSet) -- ^ Any of the given colors is at the head of the queue. @ComponentID@ should identify a queue.
--    | Any_In_Buffer ComponentID (Maybe ColorSet) -- ^ Any of the given colors is in the buffer. @ComponentID@ should identify a buffer.
    | All_Not_At_Head ComponentID (Maybe ColorSet) -- ^ None of the given colors is at the head of the queue. @ComponentID@ should identify a queue.
    | Select ComponentID Int -- ^ Buffer arbiter has selected cell @Inp@, Merge arbiter has selected input @Int@, or LoadBalancer arbiter has selected output @Int@. @ComponentID@ should identify a merge or loadbalancer.
    | MSelect ComponentID (Int, Int) -- ^ MultiMatch arbiter has selected (matchInput, dataInput) @(Int, Int)@. @ComponentID@ should identify a multi-match.
    | InState ComponentID Int -- ^ Automaton is in state @Int@. @ComponentID@ should identify an automaton.
    | TSelect ComponentID Int Int -- ^ Automaton arbiter has selected input @Int@ and transition @Int@. @ComponentID@ should identify an automaton.
    | IdleState ComponentID Int -- ^ Idleness of state @Int@ of the automaton
    | DeadTrans ComponentID Int -- ^ Transition @Int@ of automaton @ComponentID@ is dead
    | Sum_Compare [(ComponentID, Maybe Color)] String Int -- ^ TODO(snnw, frkv) : explain what @Sum_Compare@ means.
    | BlockSource ComponentID -- ^ The outgoing channel of the source identified by @ComponentID@ satisfies @G!trdy@ for at least one of the colors produced by the source.
    | BlockBuffer ComponentID -- ^ The outgoing channel of the buffer is blocked for the contents of the buffer.
    | BlockAny Source ChannelID (Maybe ColorSet) -- ^ Channel satisfies @G!trdy@ for at least one of the given colors.
    | IdleAll Source ChannelID (Maybe ColorSet) -- ^ Channel satisfies @G!irdy@ for all of the given colors.
    deriving (Show)

instance Ord Literal where
    Is_Full l <= Is_Full r = l <= r
    Is_Not_Full l <= Is_Not_Full r = l <= r
    ContainsNone l0 l1 <= ContainsNone r0 r1 = (l0, l1) <= (r0, r1)
    Any_At_Head l0 l1 <= Any_At_Head r0 r1 = (l0, l1) <= (r0, r1)
--    Any_In_Buffer l0 l1 <= Any_In_Buffer r0 r1 = (l0, l1) <= (r0, r1)
    All_Not_At_Head l0 l1 <= All_Not_At_Head r0 r1 = (l0, l1) <= (r0, r1)
    Select l0 l1 <= Select r0 r1 = (l0, l1) <= (r0, r1)
    MSelect l0 l1 <= MSelect r0 r1 = (l0, l1) <= (r0, r1)
    InState l0 l1 <= InState r0 r1 = (l0, l1) <= (r0, r1)
    TSelect l0 l1 l2 <= TSelect r0 r1 r2 = (l0, l1, l2) <= (r0, r1, r2)
    IdleState l0 l1 <= IdleState r0 r1 = (l0, l1) <= (r0, r1)
    DeadTrans l0 l1 <= DeadTrans r0 r1 = (l0, l1) <= (r0, r1)
    Sum_Compare l0 l1 l2 <= Sum_Compare r0 r1 r2 = (l0, l1, l2) <= (r0, r1, r2)
    BlockSource l <= BlockSource r = l <= r
    BlockBuffer l <= BlockBuffer r = l <= r
    BlockAny _ l0 l1 <= BlockAny _ r0 r1 = (l0, l1) <= (r0, r1)
    IdleAll _ l0 l1 <= IdleAll _ r0 r1 = (l0, l1) <= (r0, r1)
    Is_Full{} <= _ = True
    _ <= Is_Full{} = False
    Is_Not_Full{} <= _ = True
    _ <= Is_Not_Full{} = False
    ContainsNone{} <= _ = True
    _ <= ContainsNone{} = False
    Any_At_Head{} <= _ = True
    _ <= Any_At_Head{} = False
--    Any_In_Buffer{} <= _ = True
--    _ <= Any_In_Buffer{} = False
    All_Not_At_Head{} <= _ = True
    _ <= All_Not_At_Head{} = False
    Select{} <= _ = True
    _ <= Select{} = False
    MSelect{} <= _ = True
    _ <= MSelect{} = False
    InState{} <= _ = True
    _ <= InState{} = False
    IdleState{} <= _ = True
    _ <= IdleState{} = False
    DeadTrans{} <= _ = True
    _ <= DeadTrans{} = False
    TSelect{} <= _ = True
    _ <= TSelect{} = False
    Sum_Compare{} <= _ = True
    _ <= Sum_Compare{} = False
    BlockSource{} <= _ = True
    _ <= BlockSource{} = False
    BlockBuffer{} <= _ = True
    _ <= BlockBuffer{} = False
    BlockAny{} <= _ = True
    _ <= BlockAny{} = False

instance Eq Literal where
    x == y = (x <= y) && (y <= x)

-- | Constructs an @Any_At_Head@ literal. Uses @Nothing@ as colorset if appropriate.
atHeadLiteral :: (IsColorSet c, INetwork n a (WithColors b)) => n a (WithColors b) -> ComponentID -> c -> Literal
atHeadLiteral net cID cs = Any_At_Head cID cs' where
    cs' = if toColorSet cs == head (inputTypes net cID) then Nothing else Just $ toColorSet cs


-- | Constructs an @Any_In_Buffer@ literal. Uses @Nothing@ as colorset if appropriate.
{-inBufferLiteral :: (IsColorSet c, INetwork n a (WithColors b)) => n a (WithColors b) -> ComponentID -> c -> Literal
inBufferLiteral net cID cs = Any_In_Buffer cID cs' where
    cs' = if toColorSet cs == head (inputTypes net cID) then Nothing else Just $ toColorSet cs-}


-- | Constructs an @All_Not_At_Head@ literal. Uses @Nothing@ as colorset if appropriate.
notAtHeadLiteral :: INetwork n a (WithColors b) => n a (WithColors b) -> ComponentID -> ColorSet -> Literal
notAtHeadLiteral net cID cs = All_Not_At_Head cID cs' where
    cs' = if cs == head (inputTypes net cID) then Nothing else Just cs

-- | Constructs a @ContainsNone@ literal. Uses @Nothing@ as colorset if appropriate.
containsNoneLiteral :: (IsColorSet c, INetwork n a (WithColors b)) => n a (WithColors b) -> ComponentID -> c -> Literal
containsNoneLiteral net cID cs = ContainsNone cID cs' where
    cs' = if toColorSet cs == head (inputTypes net cID) then Nothing else Just $ toColorSet cs

-- | Constructs a @BlockAny@ literal. Uses @Nothing@ as colorset if appropriate.
blockLiteral :: (INetwork n a (WithColors b), IsColorSet c) => Source -> n a (WithColors b) -> ChannelID -> c -> Literal
blockLiteral loc net xID cs = BlockAny loc xID cs' where
    cs' = if toColorSet cs == snd (getChannel net xID) then Nothing else Just (toColorSet cs)

-- | Constructs an @IdleAll@ literal. Uses @Nothing@ as colorset if appropriate.
idleLiteral :: (IsColorSet c, INetwork n a (WithColors b)) => Source -> n a (WithColors b) -> ChannelID -> c -> Literal
idleLiteral loc net xID cs = IdleAll loc xID cs' where
    cs' = if toColorSet cs == snd (getChannel net xID) then Nothing else Just $ toColorSet cs

disjunct' :: Ord k => (Map k a, Formula) -> (Map k a, Formula) -> (Map k a, Formula)
disjunct' (fm, f) (fm', f') = (Map.union fm fm', disjunct f f')

-- | The disjunction of two formulas. Simplifies where possible.
disjunct :: Formula -> Formula -> Formula
disjunct T _ = T
disjunct _ T = T
disjunct F f = f
disjunct f F = f
disjunct (Lit l) (OR fs)   = OR (Set.insert (Lit l) fs)
disjunct (OR fs) (Lit l)   = OR (Set.insert (Lit l) fs)
disjunct (OR fs0) (OR fs1) = OR (Set.union fs0 fs1)
disjunct f0 f1 = if f0 == f1 then f0 else OR $ Set.fromList [f0,f1]

conjunct' :: Ord k => (Map k a, Formula) -> (Map k a, Formula) -> (Map k a, Formula)
conjunct' (fm, f) (fm', f') = (Map.union fm fm', conjunct f f')

-- | The conjunction of two formulas. Simplifies where possible.
conjunct :: Formula -> Formula -> Formula
conjunct F _ = F
conjunct _ F = F
conjunct T f = f
conjunct f T = f
conjunct (Lit l) (AND fs)    = AND (Set.insert (Lit l) fs)
conjunct (AND fs) (Lit l)    = AND (Set.insert (Lit l) fs)
conjunct (AND fs0) (AND fs1) = AND (Set.union fs0 fs1)
conjunct f0 f1 = if f0 == f1 then f0 else AND $ Set.fromList [f0,f1]

-- | The negation of two formulas. Simplifies where possible.
negation :: Formula -> Formula
negation T = F
negation F = T
negation (NOT f) = f -- TODO (js) check that this is correct negation somewhere?
negation (AND fs) = disjunctive $ Set.map negation fs
negation (OR fs) = conjunctive $ Set.map negation fs
negation (Lit (Is_Full cID)) = Lit $ Is_Not_Full cID
negation (Lit (Is_Not_Full cID)) = Lit $ Is_Full cID
negation (Lit (Any_At_Head cID c)) = Lit $ All_Not_At_Head cID c
negation (Lit (All_Not_At_Head cID c)) = Lit $ Any_At_Head cID c
negation l@Lit{} = NOT l

-- | Constructs the conjunciton of a set of formulas.
conjunctive :: Foldable t => t Formula -> Formula
conjunctive = foldr conjunct T

-- | Constructs the disjunction of a set of formulas.
disjunctive :: Foldable t => t Formula -> Formula
disjunctive = foldr disjunct F

forall' :: forall a b k t . (Foldable t, Ord k) => Map k a -> t b -> (b -> Map k a -> (Map k a, Formula)) -> (Map k a, Formula)
forall' fm xs f = foldr g (fm, T) xs where
    g :: b -> (Map k a, Formula) -> (Map k a, Formula)
    g x (fm', f') = mapSnd (conjunct f') (f x fm')


-- | Apply a function to a set of objects, and take the conjunction of the resulting formulas.
forall :: Traversable t => t a -> (a -> Formula) -> Formula
forall xs f = conjunctive $ fmap f xs

forallMaybe' :: forall a b k t . (Foldable t, Ord k) => Map k a -> t b -> (b -> Map k a -> Maybe (Map k a, Formula)) -> (Map k a, Formula)
forallMaybe' fm xs f = foldr g (fm, T) xs where
    g :: b -> (Map k a, Formula) -> (Map k a, Formula)
    g x (fm', f') = mapSnd (conjunct f') (fromMaybe (fm', T) $ f x fm')

-- | Apply a partial function to a set of objects, and take the conjunction of the resulting formulas.
forallMaybe :: Traversable t => t a -> (a -> Maybe Formula) -> Formula
forallMaybe xs f = conjunctive $ mapMaybe f (toList xs)

exists' :: forall a b k t . (Foldable t, Ord k) => Map k a -> t b -> (b -> Map k a -> (Map k a, Formula)) -> (Map k a, Formula)
exists' fm xs f = foldr g (fm, F) xs where
    g :: b -> (Map k a, Formula) -> (Map k a, Formula)
    g x (fm', f') = mapSnd (disjunct f') (f x fm')

-- | Apply a function to a set of objects, and take the disjunction of the resulting formulas.
exists :: Traversable t => t a -> (a -> Formula) -> Formula
exists xs f = disjunctive $ fmap f xs

-- | Apply a partial function to a set of objects, and take the disjunction of the resulting formulas.
existsMaybe :: Traversable t => t a -> (a -> Maybe Formula) -> Formula
existsMaybe xs f = disjunctive $ mapMaybe f (toList xs)

-- | Transform a boolean to a formula
fromBool :: Bool -> Formula
fromBool True  = T
fromBool False = F

-- | Simplify a formula by removing unneeded conjunctions and disjunctions.
simplify_singletons :: Formula -> Formula
simplify_singletons (OR fs) =
    let fs' = Set.unions $ Set.toList $ Set.map (\f -> case f of OR fs'' -> fs''; _ -> Set.singleton f) (Set.map simplify_singletons fs) in
        if Set.size fs' == 1 then
            Set.findMin fs'
        else if Set.size fs' == 0 then
            F -- TODO(frkv) uitzoeken waar dit vandaan komt
        else
            OR fs'
simplify_singletons (AND fs) =
    let fs' = Set.unions $ Set.toList $ Set.map (\f -> case f of AND fs'' -> fs''; _ -> Set.singleton f) (Set.map simplify_singletons fs) in
        if Set.size fs' == 1 then
            Set.findMin fs'
        else if Set.size fs' == 0 then
            T
        else
            AND fs'
simplify_singletons f = f
