{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -fno-max-relevant-binds -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -Wmissing-local-signatures #-}
{-# LANGUAGE BangPatterns, TypeFamilies, GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveTraversable, DeriveFoldable, DeriveFunctor, OverloadedStrings, ScopedTypeVariables, LambdaCase, NoImplicitPrelude #-}

{-|
Module      : BooleanSymbolic.CalcX
Copyright   : (c) Sebastiaan J C Joosten

Add the X and Z and verilog-gate semantics
We do not export the constructor for WireReference, so that we can change it and experiment with it
For instance: this version introduced explicit sharing using DAGs
a lot of functions are not used anywhere, and therefore not exported, but we might need them later (we needed them in the past at some point..)
so we ignore all these warnings for now..
-}
module BooleanSymbolic.CalcX
 ( scopeScopedWireName
 , runX, showWireReference, showScopedWireName
 , transFN
 , WithDAG
 , WireReference, selfSimplify, canonizeBoolean
 -- not used, but harmless and possibly helpful during debug
 , Symbolic (..), Operator (..)
 , MOperator (..), UnaryOperator (..)
 -- re-export of most likely Classes:
 , BooleanXZ(..), ScopedWireName, AtomToBoolean(..)
 )
 where

import BooleanSymbolic.Class
import qualified Data.Sequence as Sequence

import qualified Data.Vector as Vector
import Data.Vector.Generic.Base
import Data.Vector.Generic (unsafeFreeze, unsafeThaw, unsafeTake)
import qualified Data.Vector.Generic.Mutable as M
import Control.Monad.ST -- ( runST )

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.List (nub)
import Debug.Trace
import Control.Monad.Identity
import Control.Monad.State
import Data.Monoid
import BaseLike.CustomPrelude as Prelude

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in Boolean/CalcX.hs:\n  "++s)
_unused :: a
_unused = undefined trace fatal -- these may be used, but their use is not required

-- | TODO
newtype WireReference a = WireRef{runWireRef::Int} deriving (Show)

type DAG = Sequence.Seq (Symbolic Int) -- note: not all functions require that the Symbolic only points backwards (thus creating a DAG) but this is the default direction.
-- | TODO
newtype WithDAG btype a
 = WD (State DAG a) deriving (Monad, Applicative, Functor)

maPure :: forall a tp. (DAG -> a) -> WithDAG tp a
maPure f = WD (state (\i -> (f i,i)))

-- | TODO
data MOperator = AND | OR | CONNECT deriving (Eq, Show, Ord) -- these turn out to be commutative and idempotent as well
-- | TODO
data Operator = IMP | NIMPL | XOR | EQ | BUFIF deriving (Eq, Show, Ord) -- while some are associative, all lack a unit element (X is absorbing for XOR and EQ)
-- | TODO
data UnaryOperator = NOT | BUF deriving (Eq, Show, Ord)
-- | TODO
data Symbolic a
 = Symbol ScopedWireName
 | Symbolic Operator a a
 | MSymbolic MOperator [a]
 | Unary UnaryOperator a
 | ITE a a a
 | X
 deriving (Foldable, Functor, Traversable, Show, Eq, Ord)

-- | TODO
runX :: (forall allTp. WithDAG allTp a) -> a
runX f = resVal -- trace ("Running DAG returned "++show (Sequence.length _resVec)) resVal
  where (_resVec,resVal) = getPair Sequence.empty f

getPair :: DAG -> WithDAG a b -> (DAG,b)
getPair i (WD v) = let ~(a,b) = runState v i in (b,a)
{-
constructNA :: forall v a f b. (Vector v a, Foldable f)
            => f b -> (Int -> v a -> b -> a) -> (v a)
{-# INLINE constructNA #-}
-- NOTE: We *CANNOT* wrap this in New and then fuse because the elements
-- might contain references to the immutable vector!
constructNA bs f
 = runST (
   do
     v  <- M.new n
     v' <- unsafeFreeze v
     checkNr$ foldl' fill (0, pure v') bs
   )
   where
     n = length bs
     fill :: forall s. (Int, ST s (v a)) -> b -> (Int, ST s (v a))
     fill (!i,!v) b
      = (i+1, do !v'' <- v
                 let x = f i (unsafeTake i v'') b
                 v' :: Mutable v s a <- unsafeThaw v''
                 M.unsafeWrite v' i x
                 unsafeFreeze v')
     -- fill v _ = return v
     checkNr :: forall s. (Int, ST s (v a)) -> ST s (v a)
     checkNr (nr,!v) = if nr==n then v else fatal 99 "constructNA was applied on a Foldable for which `length' returned the wrong size!"

transFN2 :: forall b t f.
           ( AtomToBoolean ScopedWireName (BooleanResult b)
           , BooleanXZ b, Show b
           , Traversable f)
        => f (WireReference t)
        -> WithDAG t ((BooleanMonad b) (f b))
transFN2 fs
 = maPure (\maVec -> let findNr :: Int -> BooleanMonad b b
                         findNr nr = do trace ("Effects for "++show nr) (return ())
                                        transVec Vector.! nr
                         transVec :: Vector.Vector (BooleanMonad b b)
                         transVec --
                          = constructNA maVec (\_ v b -> symbolicToBoolean toBoolean (v Vector.!) b)
                     in traverse (findNr . runWireRef) fs)
-}


constructNAM :: forall v a m f b. (Vector v a, Foldable f, Monad m)
             => f b -> (Int -> v a -> b -> m a) -> m (v a)
{-# INLINE constructNAM #-}
constructNAM bs f
 = snd$ foldl' fill (0, pure (runST (do v <- M.new n
                                        unsafeFreeze v))) bs
   where
     n = length bs
     fill :: (Int, m (v a)) -> b -> (Int, m (v a))
     fill (!i,!msv) b
      = (i+1, do !v'' <- msv
                 x <- f i (unsafeTake i v'') b
                 return (runST (do v' <- unsafeThaw v''
                                   _ <- M.unsafeWrite v' i x
                                   unsafeFreeze v')))

-- | TODO
transFN :: forall b t f.
           ( AtomToBoolean ScopedWireName (BooleanResult b)
           , BooleanXZ b
           , Traversable f)
        => f (WireReference t)
        -> WithDAG t (BooleanMonad b (f b))
transFN fs
 = maPure (\maVec -> let transVec :: BooleanMonad b (Vector.Vector b)
                         transVec
                          = constructNAM maVec (\_ v b -> symbolicToBoolean toBoolean (pure . (v Vector.!)) b)
                     in (\tv -> map ((tv Vector.!) . runWireRef) fs) <$> transVec)

-- | TODO
showScopedWireName :: ScopedWireName -> ByteString
showScopedWireName (ScopedWN _ lst a) = mconcat (map (<>">") lst) <> a
-- | TODO
showWireReference :: WireReference a -> WithDAG a ByteString
showWireReference (WireRef inp)
  = maPure (\i -> let vtLook nr  = (Sequence.index (fmap trans i) nr)
                      trans symb = symbolicToBoolean (Identity . showScopedWireName) vtLook symb
                  in  runIdentity$ vtLook inp)

symbolicToBoolean :: (BooleanXZ b, m ~ (BooleanMonad b))
                  => (ScopedWireName -> m b) -> (a -> m b) -> Symbolic a -> m b
symbolicToBoolean f myLookup = join . myTranslate
  where
    myTranslate (Symbol a)           = return$ f a
    myTranslate (Symbolic opr a1 a2) = translateOperator opr <$> myLookup a1 <*> myLookup a2
    myTranslate (MSymbolic mop aLst) = translateMOperator mop <$> traverse myLookup aLst
    myTranslate (Unary op a)         = translateUnary op <$> myLookup a
    myTranslate (ITE a b c)          = iteC <$> myLookup a <*> myLookup b <*> myLookup c
    myTranslate X                    = return$ xC

-- | basically does the same as selfSimplify, but it is much simpeler, because it does not reduce loops (it cannot introduce any).
canonizeBoolean :: forall x t. (Traversable x) -- in this implementation, we only use Foldable x and Functor x, but we may need Traversable x if we decide to use the same technique as in "incrementMapLoopless". I do not believe that a Traversable can do anything more than some structure which is both Foldable and Functor, I choose to use Traversable right away.
                => (forall s. WithDAG s (x (WireReference s))) -- list of values to update
                -> (ScopedWireName -> ScopedWireName) -- rename function for items that could not be found in the map
                -> Map.Map ScopedWireName (WireReference t) -- map to update
                -> WithDAG t (x (WireReference t)) -- updated list with only the used values
canonizeBoolean tr rename mp
 = WD (state
    (\i -> let oldStructure :: x (WireReference t)
               (oldVec, oldStructure) = getPair Sequence.empty tr
               (usedVec, structureLookup) = restrictToUsedItems (Sequence.length i) oldVec (fmap (\(WireRef nr) -> nr) oldStructure)
               newStructure :: x (WireReference t)
               newStructure = fmap (WireRef . structureLookup . runWireRef) oldStructure
               res = i <> fmap (\case
                                    Symbol a -> case Map.lookup a mp of {Just (WireRef v) -> Sequence.index i v; Nothing -> Symbol (rename a)}
                                    v -> v) usedVec
           in (newStructure, res)
      ))

-- restricts the map to the items that were used in the first iteration, and also simplifies indiviual terms
-- because of this, restrictToUsedItems (restrictToUsedItems x) can be different from (restrictToUsedItems x)
restrictToUsedItems :: (Foldable t)
                    => Int -- offset
                    -> Sequence.Seq (Symbolic Int) -- should not have loops!
                    -> t Int
                    -> (Sequence.Seq (Symbolic Int), Int -> Int)
restrictToUsedItems offset lookupf lst
 = (Sequence.fromList [symbolicKeep Symbol newLookup v | v <- toList newMap], newLookup)
   where newMap    = foldl' incrementMap IntMap.empty lst
         newLookup = (IntMap.!) (snd $ mapAccumL (\incr _ -> seq incr (1+incr,incr)) offset newMap)
         incrementMap :: IntMap.IntMap (Symbolic Int)
                      -> Int
                      -> IntMap.IntMap (Symbolic Int)
         incrementMap mp nr
           = case IntMap.lookup nr mp of
              Just _ -> mp
              Nothing -> let newVal = Sequence.index lookupf nr
                             newMap' = foldl' incrementMap mp newVal -- new map without 'newVal'
                             findI = (newMap' IntMap.!)
                         in IntMap.insert nr (normVal findI newVal) newMap'

type StateQuadriple a
  =  ( a -- next unique value
     , IntMap.IntMap ( a -- new node number
                     , Symbolic a) -- its value
       -- top layer
     , [IntMap.IntMap ( a -- new node number
                      , Symbolic a) -- its value
       ] -- list of next layers
       -- empty list stands for infinite empty maps
     , Map.Map (Symbolic a) a -- reverse lookup
     )
incrementMapLoopless
  :: forall a. -- we can't mix up a and Int
     (Enum a, Ord a, Show a)
  => -- a function to obtain original values:
     ( Int -> Symbolic Int )
  -> IntSet.IntSet -- check cycles (initially empty set)
  -> IntSet.IntSet -- nodes which resulted in a new layer
  -> StateQuadriple a
  -> Int -- reference to follow
  -> ( StateQuadriple a
     , a -- a new reference (in the new map)
     )
incrementMapLoopless lookupf cycleCheck layerNodes st nr
 = if IntSet.member nr cycleCheck
   then addTop (workSharing incrWLayer (stripTop st))
   else workSharing incrWithinSameLayer st
  where
   -- recursive call with proper cycle-protection arguments
   symbol = if IntSet.member nr layerNodes then MSymbolic CONNECT [] -- todo(basj): this should work with X too!
            else lookupf nr
   newCheck = IntSet.insert nr cycleCheck
   incrementWith :: IntSet.IntSet -> StateQuadriple a
                 -> (StateQuadriple a, Symbolic a)
   incrementWith useLayers useState
    = mapAccumL (incrementMapLoopless lookupf newCheck
                                      useLayers)
                useState symbol
   incrWLayer = incrementWith (IntSet.insert nr layerNodes)
   incrWithinSameLayer = incrementWith layerNodes
   -- moving to and from the next layer
   stripTop :: StateQuadriple a -> StateQuadriple a
   stripTop (nextA,_,layers,revmp)
    = case layers of
        []     -> (nextA,IntMap.empty,[],revmp)
        (h:tl) -> (nextA,h           ,tl,revmp)
   addTop :: (StateQuadriple a, a)
          -> (StateQuadriple a, a)
   addTop ((nA,              h,  tl,revL),v)
        = ((nA,currentTopLayer,h:tl,revL),v)
   currentTopLayer = let (_,tp,_,_) = st in tp
   -- check if any work needs to be done, share nodes
   workSharing doWork myState@(_,topLayer,_,_)
    = case IntMap.lookup nr topLayer of
       -- use the current node from this layer if it exists
       Just v -> ( myState, fst v )
       Nothing-> shareOrAdd (doWork myState)
   -- share a node if possible, but do not share X or Z
   shareOrAdd (newSt,X) = addNode (newSt,X)
   shareOrAdd (newSt,z@(MSymbolic CONNECT []))
    = addNode (newSt,z)
   shareOrAdd (newSt@(_,_,_,newRevMap), newSymbol)
    = case Map.lookup newSymbol newRevMap of
       Just v -> (newSt, v)
       Nothing -> addNode (newSt,newSymbol)
   -- create the node referenced as `newNextA'
   addNode :: (StateQuadriple a, Symbolic a)
           -> (StateQuadriple a, a)
   addNode ( (newNextA,newTopLayer,newLayers,newRevMap)
           , newSymbol)
    = ( ( succ newNextA
        , IntMap.insert nr (newNextA,newSymbol) newTopLayer
        , newLayers
        , Map.insert newSymbol newNextA newRevMap
        )
      , newNextA)

-- | TODO
selfSimplify :: forall ap x. Traversable x
             => (forall tp. -- note that this forall-type can make it fairly difficult to use selfSimplify, but it is a sufficient condition for safety, so think very carefully if you feel the need to create another version of selfSimplify in order to remove this forall.
                WithDAG tp ( Map.Map ScopedWireName (WireReference tp) -- stuff to reduce with (all the ScopedWireName in this map will not be a Symbol in the final DAG)
                                 , x (WireReference tp) -- stuff to keep around
                                 ))
             -> WithDAG ap ( Map.Map ScopedWireName (WireReference ap) -- reduced values
                                 , x (WireReference ap) -- kept values
                                 )
selfSimplify mpk
 = WD (state
    (\i -> let plus = (Sequence.length i +)
               plus2 = WireRef . plus :: Int -> WireReference ap
               res = i <> fmap (fmap plus) (Sequence.fromList (IntMap.elems normedNewVec))
            in ( (fmap plus2 newMp, fmap plus2 newInOutValues)
               , res
               )))
 where (oldVec, (mp,inOutValues)) = getPair Sequence.empty (mpk::WithDAG ap ( Map.Map ScopedWireName (WireReference ap), x (WireReference ap) ) ) -- restricting type to get rid of polymorphic local bind warnings. We're not really using polymorphism inside of this function, and the Rank2 polymorphism is merely used as a restriction on the functions calling selfSimplify (as with runX)
       lookupNoLoops nrSet nr
        = case Sequence.index oldVec nr of
               o@(Symbol apr) -> (case Map.lookup apr mp of
                                    Nothing -> o
                                    Just (WireRef v) -> if IntSet.member nr nrSet then MSymbolic CONNECT [] else lookupNoLoops (IntSet.insert nr nrSet) v
                                 )
               o -> o
       lookupf nr = lookupNoLoops IntSet.empty nr
       (st                   , newMp         )
        = mapAccumL (incrementMapLoopless lookupf IntSet.empty IntSet.empty)
                    ( 0 -- note: by starting at (Sequence.length i) instead of 0, we can avoid some "fmap plus" occurences, at the expense of having to recompute these statements once for every i (which is costlier).
                    , IntMap.empty
                    , []
                    , Map.empty) (fmap runWireRef mp)
       ((_newLength,intVecH,intVecT,_), newInOutValues)
        = mapAccumL (incrementMapLoopless lookupf IntSet.empty IntSet.empty) st (fmap runWireRef inOutValues)
       newVec = IntMap.fromListWith (fatal 277 "Duplicates in result of incrementMapLoopless!") (concatMap IntMap.elems (intVecH:intVecT))
       normedNewVec = fmap (normVal (normedNewVec IntMap.!)) newVec

newItem :: Symbolic Int -> WithDAG a (WireReference a)
newItem v = WD (state (\vec -> case v of
                                (MSymbolic a lst) -> case nub (concat [case Sequence.index vec i of
                                                                         (MSymbolic a' lst') | a==a' -> lst'
                                                                         _ -> [i]
                                                                      | i<-lst]) of
                                                              [i] -> (WireRef i, vec)
                                                              [i,j] | i == j -> (WireRef i, vec)
                                                              lst' -> (WireRef (Sequence.length vec), vec Sequence.|> MSymbolic a lst')
                                _ -> (WireRef (Sequence.length vec), vec Sequence.|> (normVal (Sequence.index vec) v))
               ))

symbolicKeep :: (ScopedWireName -> Symbolic b) -> (b -> b) -> Symbolic b -> Symbolic b
symbolicKeep f myLookup = myTranslate
     where
       myTranslate (Symbol a)           = f a
       myTranslate (Symbolic  opr a1 a2)= Symbolic  opr   (myLookup a1) (myLookup a2)
       myTranslate (MSymbolic mop aLst) = MSymbolic mop $ map myLookup aLst
       myTranslate (Unary     op a)     = Unary     op  $ myLookup a
       myTranslate (ITE a b c)          = ITE (myLookup a) (myLookup b) (myLookup c)
       myTranslate X                    = X

instance AtomToBoolean ByteString (WithDAG tp (WireReference tp)) where
  toBoolean bs = newItem (Symbol (toBoolean bs))
instance AtomToBoolean ScopedWireName (WithDAG tp (WireReference tp)) where
  toBoolean = newItem . Symbol

instance BooleanXZ (WireReference tp) where
  gbufC (WireRef a) (WireRef b) = newItem$ Symbolic BUFIF a b
  combineC (WireRef a) (WireRef b) = newItem$ MSymbolic CONNECT [a,b]
  combineListC lst = newItem$ MSymbolic CONNECT (fmap runWireRef lst)
  bufC (WireRef a) = newItem$ Unary BUF a
  xC = newItem$ X
  zC = newItem$ MSymbolic CONNECT []
instance Boolean (WireReference tp) where
  type BooleanMonad (WireReference tp) = (WithDAG tp)
  fromBool b = newItem$ MSymbolic (if b then AND else OR) []
  andC (WireRef a) (WireRef b) = newItem$ MSymbolic AND [a,b]
  orC  (WireRef a) (WireRef b) = newItem$ MSymbolic OR  [a,b]
  eqC  (WireRef a) (WireRef b) = newItem$ Symbolic  EQ   a b
  xorC (WireRef a) (WireRef b) = newItem$ Symbolic  XOR  a b
  impC (WireRef a) (WireRef b) = newItem$ Symbolic  IMP  a b
  notImpC (WireRef a) (WireRef b) = newItem$ Symbolic NIMPL a b
  iteC (WireRef a) (WireRef b) (WireRef c) = newItem$ ITE a b c
  notC (WireRef a) = newItem$ Unary NOT a

translateOperator :: forall boolean. BooleanXZ boolean
                  => Operator -> boolean -> boolean -> BooleanResult boolean
translateOperator XOR = xorC
translateOperator EQ  = eqC
translateOperator BUFIF = gbufC
translateOperator IMP = impC
translateOperator NIMPL = notImpC
translateMOperator :: forall a. BooleanXZ a
                   => MOperator -> [a] -> BooleanResult a
translateMOperator AND []  = trueC
translateMOperator AND (h:lst) = foldlM andC h lst
translateMOperator OR  []  = falseC
translateMOperator OR  (h:lst) = foldlM orC h lst
translateMOperator CONNECT lst = combineListC lst
translateUnary :: BooleanXZ boolean
               => UnaryOperator -> boolean -> BooleanResult boolean
translateUnary NOT = notC
translateUnary BUF = bufC

normVal :: (Ord a)
        => (a -> Symbolic a)
        -> Symbolic a -> Symbolic a -- normalize a value (simplify AND(0,x) to 0 etc..)
normVal findI inpVal
 = -- if True then inpVal else
   case inpVal of
      o@(Unary NOT a')
        -> case findI a' of
             (MSymbolic AND  []   ) -> MSymbolic OR  []
             (MSymbolic OR   []   ) -> MSymbolic AND []
             (MSymbolic CONNECT []) -> X
             (Symbolic  XOR  a b  ) -> normVal findI$ Symbolic EQ    a b
             (Symbolic  EQ   a b  ) -> normVal findI$ Symbolic XOR   a b
             (Symbolic  IMP  a b  ) -> normVal findI$ Symbolic NIMPL a b
             (Symbolic NIMPL a b  ) -> normVal findI$ Symbolic IMP   a b
             (Unary NOT a) -> findI a
             X -> X
             _ -> o
      (Symbolic XOR a' b')
        -> if a' == b' then MSymbolic OR [] else
           case (findI a', findI b') of
             (MSymbolic AND     [], _) -> normVal findI$ Unary NOT b'
             (MSymbolic OR      [], b) -> b
             (X                   , _) -> X
             (MSymbolic CONNECT [], _) -> X
             (_, MSymbolic AND     []) -> normVal findI$ Unary NOT a'
             (b, MSymbolic OR      []) -> b
             (_, X                   ) -> X
             (_, MSymbolic CONNECT []) -> X
             _ -> Symbolic XOR (min a' b') (max a' b')
      (Symbolic EQ  a' b')
        -> if a' == b' then MSymbolic AND [] else
           case (findI a', findI b') of
             (MSymbolic AND     [], b) -> b
             (MSymbolic OR      [], _) -> normVal findI$ Unary NOT b'
             (X                   , _) -> X
             (MSymbolic CONNECT [], _) -> X
             (a, MSymbolic AND     []) -> a
             (_, MSymbolic OR      []) -> normVal findI$ Unary NOT a'
             (_, X                   ) -> X
             (_, MSymbolic CONNECT []) -> X
             _ -> Symbolic EQ (min a' b') (max a' b')
      (Symbolic IMP a' b')
        -> if a' == b' then MSymbolic AND [] else
           case (findI a', findI b') of
             (MSymbolic AND     [], b) -> b
             (MSymbolic OR      [], _) -> MSymbolic AND []
             (_, MSymbolic AND     []) -> MSymbolic AND []
             (_, MSymbolic OR      []) -> normVal findI$ Unary NOT a'
             _ -> Symbolic IMP a' b'
      (Symbolic NIMPL a' b')
        -> if a' == b' then MSymbolic OR [] else
           case (findI a', findI b') of
             (MSymbolic AND     [], _) -> normVal findI$ Unary NOT b'
             (MSymbolic OR      [], _) -> MSymbolic OR []
             (_, MSymbolic AND     []) -> MSymbolic OR []
             (a, MSymbolic OR      []) -> a
             _ -> Symbolic NIMPL a' b'
      o@(MSymbolic opr mlst)
        -> case nub (concat [case findI l of
                                 (MSymbolic opr2 lst2) | opr2 == opr -> lst2
                                 _ -> [l]
                            | l <- mlst]) of
             [] -> MSymbolic opr []
             [a] -> case findI a of
                      (MSymbolic CONNECT []) -> o
                      vs -> vs
             vs -> (if opr == AND && (MSymbolic OR  [] `Prelude.elem` (map findI vs)) then MSymbolic OR  [] else
                    if opr == OR  && (MSymbolic AND [] `Prelude.elem` (map findI vs)) then MSymbolic AND [] else
                    MSymbolic opr vs
                    )
      (ITE a' b' c')
        -> if a' == b' then normVal findI$ MSymbolic OR  [a',c'] else
           if a' == c' then normVal findI$ MSymbolic AND [a',b'] else
           if b' == c' then findI b' else
           case (findI a', findI b', findI c') of
             (MSymbolic AND [], b, _) -> b
             (MSymbolic OR  [], _, c) -> c
             (Unary NOT a     , _, _) -> normVal findI$ ITE a c' b'
             (_, Unary NOT b     , _) | b == c' -> normVal findI$ Symbolic XOR a' c'
             (_, _, Unary NOT c     ) | b' == c -> normVal findI$ Symbolic EQ  a' b'
             (_, MSymbolic AND [], _) -> normVal findI$ MSymbolic OR  [a',c']
             (_, _, MSymbolic OR  []) -> normVal findI$ MSymbolic AND [a',b']
             (_, MSymbolic OR  [], _) -> normVal findI$ Symbolic NIMPL c' a'
             (_, _, MSymbolic AND []) -> normVal findI$ Symbolic IMP   a' b'
             _ -> ITE a' b' c'
      _ -> inpVal

