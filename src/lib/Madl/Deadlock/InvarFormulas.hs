{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}


module Madl.Deadlock.InvarFormulas where


import Data.Foldable (toList)
import Data.Maybe (mapMaybe, fromMaybe)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import qualified Data.Bimap as BM

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes
import Madl.Network


data InvarFormula
    = TRUE
    | FALSE
    | NEG InvarFormula
    | CONJ InvarFormula InvarFormula
    | DISJ InvarFormula InvarFormula
    | IMPL InvarFormula InvarFormula
    | BIIMPL InvarFormula InvarFormula
    | EQUALS IntExpr IntExpr
    | LESS IntExpr IntExpr
    | GREATER IntExpr IntExpr
    | BVAR BoolVar
    | CUSTOMBVAR String

data IntExpr
    = INT Int
    | IVAR IntVar
    | CUSTOMIVAR String
    | MINUS IntExpr IntExpr
    | PLUS IntExpr IntExpr
    | ITE InvarFormula IntExpr IntExpr

data IntVar
    = QOccupancy ComponentID Int
    | QCell ComponentID Int Int
    | Sel ComponentID Int
    | Cur ComponentID Int
    | Data ChannelID Int

data BoolVar
    = Irdy ChannelID Int
    | Trdy ChannelID Int


instance Show BoolVar where
  show (Irdy cid step) = "irdy_" ++ (show cid) ++ "_" ++ (show step)
  show (Trdy cid step) = "trdy_" ++ (show cid) ++ "_" ++ (show step)


instance Show IntVar where
  show (QOccupancy cid step) = "qhas_" ++ (show cid) ++ "_" ++ (show step)
  show (QCell cid x step) = "qcell_" ++ (show cid) ++ "_" ++ (show x) ++ "_" ++ (show step)
  show (Sel cid step) = "sel_" ++ (show cid) ++ "_" ++ (show step)
  show (Cur cid step) = "cur_" ++ (show cid) ++ "_" ++ (show step)
  show (Data cid step) = "data_" ++ (show cid) ++ "_" ++ (show step)


instance Show IntExpr where
  show (INT x) = show x
  show (IVAR v) = show v
  show (CUSTOMIVAR s) = s
  show (MINUS a b) = "(- " ++ (show a) ++ " " ++ (show b) ++ ")"
  show (PLUS a b) = "(+ " ++ (show a) ++ " " ++ (show b) ++ ")"
  show (ITE f f' f'') = "(ite " ++ show f ++ " " ++ show f' ++ " " ++ show f'' ++ " " ++ ")"


instance Show InvarFormula where
  show TRUE = "true"
  show FALSE = "false"
  show (NEG f) = "(not " ++ show f ++ ")"
  show (CONJ f f') = "(and " ++ show f ++ " " ++ show f' ++ ")"
  show (DISJ f f') = "(or " ++ show f ++ " " ++ show f' ++ ")"
  show (IMPL f f') = "(=> " ++ show f ++ " " ++ show f' ++ ")"
  show (BIIMPL f f') = "(= " ++ show f ++ " " ++ show f' ++ ")"
  show (EQUALS f f') = "(= " ++ show f ++ " " ++ show f' ++ ")"
  show (LESS f f') = "(< " ++ show f ++ " " ++ show f' ++ ")"
  show (GREATER f f') = "(> " ++ show f ++ " " ++ show f' ++ ")"
  show (BVAR v) = show v
  show (CUSTOMBVAR s) = s

{-
class ShowFormula a where
  showF :: a -> String -> String


instance ShowFormula BoolVar where
  showF (Irdy cid step) postfix = "irdy_" ++ (show cid) ++ "_" ++ (show step) ++ postfix
  showF (Trdy cid step) postfix = "trdy_" ++ (show cid) ++ "_" ++ (show step) ++ postfix


instance ShowFormula IntVar where
  showF (QOccupancy cid step) postfix = "qhas_" ++ (show cid) ++ "_" ++ (show step) ++ postfix
  showF (QCell cid x step) postfix = "qcell_" ++ (show cid) ++ "_" ++ (show x) ++ "_" ++ (show step) ++ postfix
  showF (Sel cid step) postfix = "sel_" ++ (show cid) ++ "_" ++ (show step) ++ postfix
  showF (Cur cid step) postfix = "cur_" ++ (show cid) ++ "_" ++ (show step) ++ postfix
  showF (Data cid step) postfix = "data_" ++ (show cid) ++ "_" ++ (show step) ++ postfix


instance ShowFormula IntExpr where
  showF (INT x) postfix = show x
  showF (IVAR v) postfix = showF v postfix
  showF (CUSTOMIVAR s) postfix = s
  showF (MINUS a b) postfix = "(- " ++ (showF a postfix) ++ " " ++ (showF b postfix) ++ ")"
  showF (PLUS a b) postfix = "(+ " ++ (showF a postfix) ++ " " ++ (showF b postfix) ++ ")"
  showF (ITE f f' f'') postfix = "(ite " ++ showF f postfix ++ " " ++ showF f' postfix ++ " " ++ showF f'' postfix ++ " " ++ ")"


instance ShowFormula InvarFormula where
  showF TRUE _ = "true"
  showF FALSE _ = "false"
  showF (NEG f) postfix = "(not " ++ showF f postfix ++ ")"
  showF (CONJ f f') postfix = "(and " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (DISJ f f') postfix = "(or " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (IMPL f f') postfix = "(=> " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (BIIMPL f f') postfix = "(= " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (EQUALS f f') postfix = "(= " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (LESS f f') postfix = "(< " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (GREATER f f') postfix = "(> " ++ showF f postfix ++ " " ++ showF f' postfix ++ ")"
  showF (BVAR v) postfix = showF v postfix
  showF (CUSTOMBVAR s) _ = s
-}

makeIntKeys :: [a] -> Int -> [(a,Int)]
makeIntKeys [] _ = []
makeIntKeys (x:xs) n = ((x,n):makeIntKeys xs (n+1))


typeMap :: ColoredNetwork -> BM.Bimap Color Int
typeMap net = let chans = getChannelIDs net
                  cs = map (\x -> let (ColorSet cols) = getColorSet net x in cols) chans
                  cs' = foldr (\x y -> Set.union x y) Set.empty cs
                  cs'' = Set.toList cs'
              in BM.fromList $ makeIntKeys cs'' 1


transMap :: [AutomatonTransition] -> BM.Bimap AutomatonTransition Int
transMap ts = BM.fromList $ makeIntKeys ts 1


compMap :: ColoredNetwork -> BM.Bimap ComponentID Int
compMap net = BM.fromList [(a,b) | a <- getComponentIDs net, b <- [0..(length (getComponentIDs net))-1]]


chanMap :: ColoredNetwork -> BM.Bimap ChannelID Int
chanMap net = BM.fromList [(a,b) | a <- getChannelIDs net, b <- [0..(length (getChannelIDs net))-1]]


makeConj :: [InvarFormula] -> InvarFormula
makeConj [] = TRUE
makeConj (x:[]) = x
makeConj (x:xs) = CONJ x (makeConj xs)


makeDisj :: [InvarFormula] -> InvarFormula
makeDisj [] = TRUE
makeDisj (x:[]) = x
makeDisj (x:xs) = DISJ x (makeDisj xs)


makeSum :: [IntExpr] -> IntExpr
makeSum [] = (INT 0)
makeSum (x:[]) = x
makeSum (x:xs) = PLUS x (makeSum xs)
