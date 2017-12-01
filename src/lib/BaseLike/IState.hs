{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings, MultiParamTypeClasses, FlexibleInstances, BangPatterns #-}
{-|
Module      : BaseLike.IState
Copyright   : (c) Sebastiaan J C Joosten
-}
module BaseLike.IState where

import Control.Applicative
import Data.Hashable
import Data.ByteString

-- | TODO
runIState :: a -> IState a b -> b
runIState initVal (IState f) = snd (f initVal)

-- | TODO
get :: IState a a
get = IState (\mp -> (mp,mp))
-- | TODO
put :: b -> IState b ()
put v = IState (const (v,()))

-- | TODO
newtype IState b a = IState (b -> (b, a))
instance Functor (IState x) where
 fmap f (IState f2) = IState (\v -> let (nv,a) = f2 v in (nv,f a))
instance Applicative (IState x) where
 pure v = IState (\mp -> (mp,v))
 (<*>) (IState f1) (IState x)
   = IState (\mp -> let (mp1,f) = f1 mp
                        (mp2,v) = x mp1
                        res = f v
                    in (mp2,res))

instance Monad (IState x) where
 return = pure
 (IState f1) >>= f = IState (\v -> let (mp1,a) = f1 v
                                       (IState f2) = f a
                                   in f2 mp1)