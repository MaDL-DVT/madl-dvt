{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
-- see the list at the bottom of https://ghc.haskell.org/trac/ghc/wiki/BurningBridgesSlowly to decide which version to use
{-|
Module      : BaseLike.CustomPrelude
Copyright   : (c) Sebastiaan J C Joosten
-}
module BaseLike.CustomPrelude
  ( P.Maybe(..), P.Either(..), P.Bool(..), P.IO, P.Int, P.Integer, P.Char, P.String, P.Real, P.Rational
  , P.Num(..), P.Eq(..), P.Ord(..), P.Show(..), P.Monad(..)
  , P.Enum(..), P.Functor(..), P.Integral(..), P.Fractional(..)
  , (P.++), (P..), (P.||), (P.&&), (P.$), (P.=<<)
  , P.reverse, P.take, P.read, P.id, P.flip, P.fst, P.snd, P.const
  , P.undefined, P.subtract, P.maxBound, P.minBound, P.lcm, P.ceiling
  , P.drop, P.zip, P.unzip, P.zip3, P.error, P.repeat, P.seq, P.not
  , P.and, P.gcd, P.fromIntegral, P.toRational, P.head, P.tail, P.filter
  , P.uncurry, P.curry, P.zipWith
  , (M.<>), M.Monoid(..)
  , (A.<$>), A.Applicative(..)
  , F.Foldable(foldr,foldr1,foldl')
  , F.concat, F.sequence_
  , F.sum, F.elem, F.toList, F.concatMap -- these are part of the prelude in 7.10, but not in 7.8
  , F.foldlM
  , T.Traversable(..), T.mapAccumL
  -- these don't have a corresponding implementation in 7.8 (are not in Foldable or Applicative)
  -- so they are just re-implemented here, to avoid accidents
  , map, F.length, F.null -- note: F.length and F.null might be a lot slower in 7.8 compared with 7.10!
  -- these are not in the regular prelude, but terribly convenient:
  , CM.ap , CM.join , foldrM'
  , CMI.Identity(..)
  , (CA.&&&), CA.first, CA.second
  , Encodable(..)
  , BC.pack, BC.unpack, BC.ByteString
  ) where
import qualified Prelude as P
import qualified Data.Monoid as M
import qualified Control.Applicative as A
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import qualified Control.Monad as CM
import qualified Control.Monad.Identity as CMI
import qualified Control.Arrow as CA
import qualified Text.Encoding.Z as TE
import qualified Data.ByteString.Char8 as BC (pack, unpack, ByteString)

-- | fmap renamed to map
map :: (P.Functor f) => (a -> b) -> f a -> f b
map = P.fmap

-- | TODO
foldrM' :: (P.Monad m, F.Foldable t)
        => (a -> b -> m b) -> m b -> t (m a) -> m b
foldrM' fn initial structure = F.foldr (\ a b -> CM.join P.$ fn A.<$> a A.<*> b) initial structure

-- | TODO
class Encodable a where
 encode :: a -> BC.ByteString
instance Encodable BC.ByteString where
 encode = BC.pack P.. TE.zEncodeString P.. BC.unpack
instance Encodable P.Int where
 encode b | b P.>= 0      = ((M.<>) "i_"  P.. BC.pack P.. P.show) b
          | P.otherwise   = ((M.<>) "n_"  P.. BC.pack P.. P.show P.. P.abs) b
instance Encodable a => Encodable [a] where
 encode lst = (M.<>) "l" (M.mconcat (P.map (\a -> "_" M.<> encode a) lst)) M.<> "_r"
instance (Encodable a,Encodable b) => Encodable (a,b) where
 encode (a,b) = "L_" M.<>encode a M.<> "_" M.<>encode b M.<> "_R"
