{-# OPTIONS_GHC -w  -fno-max-relevant-binds -fwarn-tabs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, RankNTypes, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveTraversable, DeriveFoldable, DeriveFunctor, OverloadedStrings, ScopedTypeVariables, LambdaCase, NoImplicitPrelude #-}
module BooleanSymbolic.SMT (showSMT,buildSMT)
 where

import BooleanSymbolic.Class as BXZ (AtomToBoolean(..), ScopedWireName(..), Boolean(..))
import BaseLike.CustomPrelude as Prelude
import CommonDataTypes.TraverseProps -- (InverseProp(..),InverseProps(..))
import EchelonForms.RingLogic (SingleHelper, DuoXZ)
import Data.SBV
import EchelonForms.SumOfProductForEchelon
import Control.Monad.Identity
import EchelonForms.RingLogic
import qualified Data.Map as Map

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in voi/BooleanSymbolic/SMT.hs:\n  "++s)

data HBool = HBool SBool deriving Show

showSMT :: IO SatResult -> ByteString -> IO ByteString
showSMT res nm
 = do res' <- res
      return (nm<>" checked using an SMT solver: \n"<>pack (show res'))

buildSMT :: ( Symbolic (InverseProps (DuoXZ HBool))
            , Identity (InverseProps (DuoXZ (NaturalBoolean (SumOfProducts ScopedWireName))))
            )
         -> IO SatResult
buildSMT (lstSmt', lstRing')
 = sat $ do let lstRing = runIdentity lstRing'
            lstSmt <- lstSmt'
            let queues =         [ ( encode qn1
                                   , (zip ins1 ins2)
                                   , (zip outs1 outs2)
                                   )
                                 | ((qn1,ins1,outs1)
                                   ,(qn2,ins2,outs2)) <- zip (findQueues lstSmt) (findQueues lstRing)
                                 , qn1==qn2 || fatal 43 "Two translations of the same network gave different results"
                                 ]
            isBlocking <- traverse getBlockingProperties queues
            solve [bOr isBlocking]
 where getBlockingProperties (qn,ins,outs)
        = do fatal 47 "undefined"
       invariants = fatal 48 "undefined"

instance BXZ.Boolean HBool where
 type (BooleanMonad HBool) = Symbolic
instance BXZ.AtomToBoolean ScopedWireName (Symbolic (DuoXZ HBool)) where
instance SingleHelper HBool where
