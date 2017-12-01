{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -Wmissing-local-signatures #-}
{-# LANGUAGE BangPatterns, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, NoImplicitPrelude #-}

{-|
Module      : BooleanSymbolic.UseMiniSat
Copyright   : (c) Sebastiaan J C Joosten
-}
module BooleanSymbolic.UseMiniSat (MiniSatA, PreLit, runMiniSatMonad, testEquivInIO, Solver, closeSolver) where
import MiniSat
import BooleanSymbolic.Class (Boolean(..),AtomToBoolean(..),BooleanXZ(..),createEverythingBooleanFromStructure,ScopedWireName)
import Control.Applicative
import qualified Data.Map as Map
-- import Control.Compose -- currently from TypeCompose >=0.9 && <0.10
import BaseLike.CustomPrelude

-- | TODO
closeSolver :: (t -> b) -> IO (t, Solver) -> IO b
closeSolver mp v
 = do (val,s)<-v
      deleteSolver s
      return (mp val)

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in BooleanSymbolic/UseMiniSat.hs:\n  "++s)

-- | TODO
testEquivInIO :: Solver -> MiniSatA PreLit -> MiniSatA PreLit -> IO (Bool)
testEquivInIO solver a b
 = do let (MiniSatA o) = (join$ isEquiv <$> a <*> b)
      (HBSTracker _ valCalc) <- o solver Map.empty
      return$ valCalc

isEquiv :: PreLit -> PreLit -> MiniSatA Bool
isEquiv p1 p2
   = testFalse (xorC p1 p2)
   where testFalse (MiniSatA preLit)
          = MiniSatA (\solver mp -> do (HBSTracker v b1) <- preLit solver mp
                                       pl <- makeLit solver b1
                                       -- putStrLn ("Calling the SAT procedure with "++show (Map.size v)++" literals")
                                       ok <- minisat_okay solver
                                       el <- minisat_isEliminated solver (minisat_var pl)
                                       if ok then return () else fatal 23 "Minisat is not ok!"
                                       if el then fatal 26 "Is eliminated!" else return ()
                                       (HBSTracker v . not <$> solve solver [pl])
                     )

-- | TODO
runMiniSatMonad :: MiniSatA a -> IO (a,Solver)
runMiniSatMonad (MiniSatA o)
 = do solver <- newSolver
      (HBSTracker _ valCalc) <- o solver Map.empty
      return$ (valCalc,solver)

data HBSTracker a = HBSTracker !(Map.Map ScopedWireName Lit) !a
-- | TODO
newtype MiniSatA a = MiniSatA (Solver -> Map.Map ScopedWireName Lit -> IO (HBSTracker a))

instance Functor HBSTracker where
 fmap f (HBSTracker v x) = HBSTracker v (f x)
instance Monad MiniSatA where
 (>>=) (MiniSatA val) f
  = MiniSatA (\solver mp -> do (HBSTracker valMap valVal) <- val solver mp
                               let (MiniSatA newFn) = f valVal
                               (HBSTracker newMap newVal) <- newFn solver valMap
                               return (HBSTracker newMap newVal))

instance Functor MiniSatA where
 fmap f (MiniSatA x) = MiniSatA (\solver mp -> map (map f) (x solver mp))
instance Applicative MiniSatA where
 pure x = MiniSatA (\ _ mp -> return (HBSTracker mp x))
 (<*>) = ap

instance AtomToBoolean ScopedWireName (MiniSatA PreLit) where
 toBoolean bs = MiniSatA withSolver
  where withSolver solver mp'
         = case (Map.lookup bs mp') of
             Nothing -> do newlit <- newLit solver
                           return (HBSTracker (Map.insert bs newlit mp')
                                              (PreLit AOAnd [newlit]))
             Just v -> return (HBSTracker mp' (PreLit AOAnd [v]))

instance BooleanXZ PreLit where
 xC = MiniSatA (\solver mp -> HBSTracker mp . PreLit AOOr . (:[]) <$> newLit solver)
 gbufC g v = iteC g v =<< xC
 combineC a b = (\x -> iteC x a b) =<< xC
 bufC x = return$x
 zC = xC

instance Boolean PreLit where
 type (BooleanMonad PreLit) = MiniSatA
 everythingBoolean = createEverythingBooleanFromStructure f0 f1 f2 f3
  where f0 :: (Solver -> IO PreLit) -> MiniSatA PreLit
        f0 x1 = MiniSatA (\solver mp -> HBSTracker mp <$> (x1 solver)) :: MiniSatA PreLit
        f1 :: (IO PreLit -> Solver -> IO PreLit)
           -> PreLit -> MiniSatA PreLit
        f1 f x1
          = MiniSatA (\solver mp -> HBSTracker mp <$> (f (return x1) solver)) :: MiniSatA PreLit
        f2 :: (IO PreLit -> IO PreLit -> (Solver -> IO PreLit))
           -> PreLit -> PreLit -> MiniSatA PreLit
        f2 f x1 x2
          = MiniSatA (\solver mp -> HBSTracker mp <$> (f (return x1) (return x2) solver))
        f3 :: (IO PreLit -> IO PreLit -> IO PreLit -> (Solver -> IO PreLit))
           -> PreLit -> PreLit -> PreLit -> MiniSatA PreLit
        f3 f x1 x2 x3
          = MiniSatA (\solver mp -> HBSTracker mp <$> (f (return x1) (return x2) (return x3) solver))

-- | TODO
data PreLit = PreLit !AndOrOr ![Lit] deriving Show
data AndOrOr = AOAnd | AOOr deriving Show
negateAndOrOr :: AndOrOr -> AndOrOr
negateAndOrOr AOAnd = AOOr
negateAndOrOr AOOr = AOAnd

takeAnd,takeOr :: (IO PreLit) -> Solver -> IO [Lit]
takeAnd pl s = do pl'<-pl
                  case pl' of
                   (PreLit AOAnd lst) -> return lst
                   (PreLit AOOr [a]) -> return [a]
                   (PreLit AOOr lst)
                    -> do new <- newLit s
                          mbTrue 28$addClause s (new:lst)
                          sequence_ [mbTrue 29$addClause s [neg l,neg new] | l<-lst]
                          return [neg new]
takeOr  pl s = do pl'<-pl
                  case pl' of
                   (PreLit AOOr lst) -> return lst
                   (PreLit AOAnd [a]) -> return [a]
                   (PreLit AOAnd lst)
                    -> do new <- newLit s
                          mbTrue 36$addClause s (new:map neg lst)
                          sequence_ [mbTrue 37$addClause s [l,neg new] | l<-lst]
                          return [new]

makeLit :: Solver -> PreLit -> IO Lit
makeLit s pl
 = do case pl of
                 (PreLit _ [a]) -> return a
                 (PreLit AOOr lst)
                  -> do new <- newLit s
                        mbTrue 56$ addClause s (neg new:lst)
                        sequence_ [mbTrue 29$addClause s [neg l,new] | l<-lst]
                        return new
                 (PreLit AOAnd lst)
                  -> do new <- newLit s
                        mbTrue 61$addClause s (new:map neg lst)
                        sequence_ [mbTrue 37$addClause s [l,neg new] | l<-lst]
                        return new

-- negatePreLit :: (Solver -> IO PreLit) -> (Solver -> IO PreLit)

instance Boolean (IO PreLit) where
  type (BooleanMonad (IO PreLit)) = ((->) Solver)
  fromBool b _ = pure (PreLit (if b then AOAnd else AOOr) [])
  andC f1 f2 solver = PreLit AOAnd <$> liftA2 (++) (takeAnd f1 solver) (takeAnd f2 solver)
  orC  f1 f2 solver = PreLit AOOr  <$> liftA2 (++) (takeOr  f1 solver) (takeOr  f2 solver)
  notC f1 _ = (\ (PreLit tp lst) -> PreLit (negateAndOrOr tp) (map neg lst)) <$> f1
  impC f1 f2 = orC f2 =<< notC f1

mbTrue :: Int -> IO Bool -> IO ()
mbTrue i x = do v <- x
                if v then return () else fail ("NOT TRUE! " ++ show i)

