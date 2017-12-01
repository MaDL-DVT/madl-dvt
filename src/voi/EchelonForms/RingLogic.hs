{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -fno-max-relevant-binds -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -Wmissing-local-signatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, RankNTypes, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveTraversable, DeriveFoldable, DeriveFunctor, OverloadedStrings, ScopedTypeVariables, LambdaCase, NoImplicitPrelude #-}
-- | Add the X and Z and verilog-gate semantics
-- We do not export the constructor for BPair, so that we can change it and experiment with it
-- For instance: this version introduced explicit sharing using DAGs
-- a lot of functions are not used anywhere, and therefore not exported, but we might need them later (we needed them in the past at some point..)
-- so we ignore all these warnings for now..
module EchelonForms.RingLogic (NaturalBoolean(..),DuoXZ(..),Abelian(..),Ring(..),SingleHelper(..),MonoidFragment(..)
                         -- ,SumOfProducts(..)
                         -- ,substituteMap
                         -- ,HashSet(..)
                         -- ,mkHashSet
                         )
 where

import BooleanSymbolic.Class
import Control.Monad.Identity
import Data.Monoid
import BaseLike.CustomPrelude as Prelude

newtype NaturalBoolean m = NaturalBoolean {runNaturalBoolean :: m} deriving (Monoid,Abelian,Ring)

infixl 6 </>
infixr 7 .*

instance Show x => Show (NaturalBoolean x) where
  show x = show (runNaturalBoolean x)
class Monoid m => Abelian m where -- sorry for not including the abelian library, but I felt like it made me write too many instances. Also sorry for not using Algebra.Ring, it felt too experimental and I'm not sure it is what I need.
  (</>) :: m -> m -> m
  aTimes :: Int -> m -> m
  aTimes i m = if i > 0 then m <> aTimes (i - 1) m -- default not used
               else if i < 0 then mempty </> aTimes (-i) m
                 else mempty
class Abelian m => Ring m where
  rOne :: m
  (.*) :: m -> m -> m

newtype MonoidFragment m = MonoidFragment {_runMonoidFragment :: m}
instance forall m. Ring m => Monoid (MonoidFragment m) where
  mempty = MonoidFragment rOne
  mappend (MonoidFragment a) (MonoidFragment b) = MonoidFragment (a .* b)

instance SingleHelper nb => SingleHelper (NaturalBoolean nb) where
  singleHelper = NaturalBoolean singleHelper
  substituteHelper v a = NaturalBoolean (substituteHelper v (runNaturalBoolean a))

instance Ring m => Boolean (NaturalBoolean m) where
 type (BooleanMonad (NaturalBoolean m)) = Identity
 fromBool b = return$ if b then rOne else mempty
 notC c     = return$ rOne </> c
 andC a b   = return$ a .* b
 orC a b    = return$ (a <> b) </> (a .* b)
 xorC a b   = return$ (a <> b) </> aTimes 2 (a .* b)
 eqC a b    = return$ rOne <> (aTimes 2 (a .* b) </> a </> b)
 iteC a b c = return$ (a .* b) <> (c .* (rOne </> a))


