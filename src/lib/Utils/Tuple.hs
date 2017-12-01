{-|
Module      : Utils.Tuple
Description : Utilities for working with tuples
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for working with tuples.
-}
module Utils.Tuple (
        unzipConcat,
        mapFst, mapSnd,
        tmap, tmap2,
        swap,
        fst3, snd3, thrd3,
        fst4, snd4, thrd4, frth4
        ) where

import qualified Data.Graph.Inductive.Query.Monad as T (mapFst, mapSnd)

-- | Unzip a list of tuples of lists, and concatenate the resulting lists of lists
unzipConcat :: [([a], [b])] -> ([a], [b])
unzipConcat = mapFst concat . mapSnd concat . unzip

-- | Map a function to the first element in a tuple
mapFst :: (a -> a') -> (a, b) -> (a', b)
mapFst = T.mapFst

-- | Map a function to the first element in a tuple
mapSnd :: (b -> b') -> (a, b) -> (a, b')
mapSnd = T.mapSnd

-- | Map a function to both elements in a tuple
tmap :: (a -> b) -> (a, a) -> (b, b)
tmap f = mapFst f . mapSnd f

-- | Map functions to both elements in a tuple
tmap2 :: (a -> a') -> (b -> b') -> (a, b) -> (a', b')
tmap2 f g = mapFst f . mapSnd g

-- | Swap the elements of a tuple
swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

-- | Obtain the first element of a 3-tuple
fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

-- | Obtain the second element of 3-tuple
snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

-- | Obtain the third element of a 3-tuple
thrd3 :: (a, b, c) -> c
thrd3 (_, _, x) = x

-- | Obtain the first element of a 4-tuple
fst4 :: (a, b, c, d) -> a
fst4  (x, _, _, _) = x

-- | Obtain the second element of a 4-tuple
snd4 :: (a, b, c, d) -> b
snd4  (_, x, _, _) = x

-- | Obtain the third element of a 4-tuple
thrd4 :: (a, b, c, d) -> c
thrd4  (_, _, x, _) = x

-- | Obtain the fourth element of a 4-tuple
frth4 :: (a, b, c, d) -> d
frth4  (_, _, _, x) = x
