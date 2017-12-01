{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -Wmissing-local-signatures #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, FlexibleContexts,ScopedTypeVariables,OverloadedStrings,NoImplicitPrelude #-}

{-|
Module      : BooleanSymbolic.Class
Copyright   : (c) Sebastiaan J C Joosten
-}
module BooleanSymbolic.Class where
import Data.String
import BaseLike.CustomPrelude
import Data.Hashable
-- | TODO
type BooleanResult b = (BooleanMonad b) b

-- | TODO
class (Boolean boolean) => BooleanXZ boolean where
 gbufC, combineC :: boolean -> boolean -> (BooleanMonad boolean) boolean
 bufC :: boolean -> (BooleanMonad boolean) boolean
 combineListC :: [boolean] -> (BooleanMonad boolean) boolean
 combineListC [] = zC
 combineListC [a] = return a
 combineListC (h:lst) = foldlM combineC h lst
 xC, zC :: (BooleanMonad boolean) boolean

-- | TODO
instance BooleanXZ ByteString where
 gbufC a b = return$ "gbuf("<>a<>","<>b<>")"
 combineC a b = return$ "combine("<>a<>","<>b<>")"
 bufC a = return$ "buf("<>a<>")"
 xC = return$ "X"
 zC = return$ "Z"

-- | The main idea here is that b represent some form of Boolean, and a represents some string (which may be scoped)
-- In some cases, we go from string to a scoped version of that string which may be instantiated later
class AtomToBoolean a b where
 toBoolean :: a -> b

-- | TODO
getUniqueVariants :: forall identifier b. (Monoid identifier, IsString identifier, AtomToBoolean identifier b)
                  => identifier -> Int -> [b] -- list should be of the length of the number supplied
getUniqueVariants identifier i
 = map ( (toBoolean :: identifier -> b)
       . (\v -> identifier <> "[" <> fromString v <> "]")
       . show )
       (take i [0::Int ..])

-- | TODO
class (Monad (BooleanMonad boolean)) => Boolean boolean where
 type BooleanMonad boolean :: * -> *
 fromBool :: Bool -> (BooleanMonad boolean) boolean
 fromBool = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _fromBool
 andC,orC,eqC,impC,notImpC,xorC :: boolean -> boolean -> (BooleanMonad boolean) boolean
 andC    = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _andC
 orC     = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _orC
 eqC     = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _eqC
 impC    = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _impC
 notImpC = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _notImpC
 xorC    = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _xorC
 iteC :: boolean -> boolean -> boolean -> (BooleanMonad boolean) boolean
 iteC = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _iteC
 notC :: boolean -> (BooleanMonad boolean) boolean
 notC = let ~(_fromBool,_andC,_orC,_eqC,_impC,_notImpC,_xorC,_iteC,_notC) = everythingBoolean in _notC
 everythingBoolean :: ( Bool    -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> boolean -> boolean -> (BooleanMonad boolean) boolean
                      , boolean -> (BooleanMonad boolean) boolean)
 -- There are three minimal complete definitions:
 -- 1. andC, notC, fromBool
 -- 2. iteC, fromBool
 -- 3. everythingBoolean
 -- For efficiency, we recommend you to implement all operations (not just 1 or 2), except "everythingBoolean".
 -- If you're lazy, please at least implement impC, or it will be defined as notC (andC (notC y) x).
 -- Use of "everythingBoolean" is meant to implement all operations conveniently (see createEverythingBooleanForMonad for example)
 -- The defaults assume boolean Boolean algebra, but have been implemented such that
 -- the xor, and eq will correspond to their gate-level counterparts (based on and, or, not)
 {-# MINIMAL (andC, notC, fromBool) | (iteC, fromBool) | everythingBoolean #-}
 everythingBoolean = (fromBool,andC',orC',eqC',impC',notImpC',xorC',iteC',notC')
  where andC' x y = falseC >>= iteC x y :: (BooleanMonad boolean) boolean -- (these local binds need not be polymorphic)
        orC'  x y = trueC >>= (flip (iteC x) y) :: (BooleanMonad boolean) boolean -- note that we're using the non accented versions, that is: without '
        xorC' x y = notC y >>= (flip (iteC x) y) :: (BooleanMonad boolean) boolean -- this is so we'll use the more efficient versions by the user
        eqC'  x y = notC y >>= iteC x y :: (BooleanMonad boolean) boolean
        impC' x y = (notC y >>= andC x) >>= notC :: (BooleanMonad boolean) boolean
        notImpC' x y = notC y >>= andC x :: (BooleanMonad boolean) boolean
        iteC' boolean b c = do b1<-(impC boolean b)
                               b2<-(notC boolean) >>= (flip impC c)
                               andC b1 b2 :: (BooleanMonad boolean) boolean
        notC' x = do t<-trueC
                     f<-falseC
                     iteC x f t :: (BooleanMonad boolean) boolean
 {-# INLINE everythingBoolean #-}

-- | TODO
class SingleHelper b where
  singleHelper :: b
  substituteHelper :: Bool -> b -> b
  helperDependent :: b -> Bool
  helperDependent _ = True
  -- substituteHelper v a == a  when  not (helperDependent a)  (and a is an instance of Eq)
  -- helperDependent singleHelper = True
  -- substituteHelper a . substituteHelper a = substituteHelper a  when  not (helperDependent a)
  -- helperDependent (substituteHelper a b) = True  when  helperDependent a  and  helperDependent b
  -- when also Evaluatable m b, then helperDependent a must be True if the evaluated value depends on the assignment for singleHelper

-- | TODO
instance Boolean ByteString where
 type BooleanMonad ByteString = Identity
 fromBool True  = return$ "1"
 fromBool False = return$ "0"
 andC a b       = return$ "and("<>a<>","<>b<>")"
 orC  a b       = return$ "or(" <>a<>","<>b<>")"
 eqC  a b       = return$ "eq(" <>a<>","<>b<>")"
 impC a b       = return$ "imp("<>a<>","<>b<>")"
 notImpC a b    = return$ "!imp("<>a<>","<>b<>")"
 xorC a b       = return$ "xor("<>a<>","<>b<>")"
 iteC a b c     = return$ "if "<>a<>" then "<>b<>" else "<>c
 notC a         = return$ "!"<>a

-- | TODO
createEverythingBooleanFromStructure :: forall t m2 boolean.
                                              (Boolean boolean) =>
                                              ((BooleanMonad boolean) boolean -> m2 t)
                                              -> ((boolean -> (BooleanMonad boolean) boolean) -> t -> m2 t)
                                              -> ((boolean -> boolean -> (BooleanMonad boolean) boolean)
                                                  -> t -> t -> m2 t)
                                              -> ((boolean -> boolean -> boolean -> (BooleanMonad boolean) boolean)
                                                  -> t -> t -> t -> m2 t)
                                              -> (Bool   ->      m2 t,
                                                  t -> t ->      m2 t,
                                                  t -> t ->      m2 t,
                                                  t -> t ->      m2 t,
                                                  t -> t ->      m2 t,
                                                  t -> t ->      m2 t,
                                                  t -> t ->      m2 t,
                                                  t -> t -> t -> m2 t,
                                                  t ->           m2 t)
createEverythingBooleanFromStructure return' ap' ap2' ap3'
 = (fromBool',andC',orC',eqC',impC',notImpC',xorC',iteC',notC')
  where
   fromBool' b = return' (fromBool b)
   notC'    ws1     = ap'  notC ws1
   andC'    ws1 ws2 = ap2' andC    ws1 ws2
   orC'     ws1 ws2 = ap2' orC     ws1 ws2
   xorC'    ws1 ws2 = ap2' xorC    ws1 ws2
   eqC'     ws1 ws2 = ap2' eqC     ws1 ws2
   impC'    ws1 ws2 = ap2' impC    ws1 ws2
   notImpC' ws1 ws2 = ap2' notImpC ws1 ws2
   iteC'    a b c   = ap3' iteC a b c
{-# INLINE createEverythingBooleanFromStructure #-}

-- | you can lift your monadic boolean with this.
createEverythingBooleanForMonad :: forall m2 boolean. (Monad m2, Boolean boolean) =>
                      ( Bool      ->                                   m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->                  m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->                  m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->                  m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->                  m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->                  m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->                  m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->   ((BooleanMonad boolean) boolean) ->   ((BooleanMonad boolean) boolean) -> m2 ((BooleanMonad boolean) boolean)
                      , (BooleanMonad boolean) boolean ->                                   m2 ((BooleanMonad boolean) boolean))
createEverythingBooleanForMonad
 = createEverythingBooleanFromStructure return' ap1 ap2 ap3
 where return' :: ((BooleanMonad boolean) boolean) -> m2 ((BooleanMonad boolean) boolean)
       return'    = return
       ap1 :: (boolean ->                       (BooleanMonad boolean) boolean) -> (BooleanMonad boolean) boolean ->                           m2 ((BooleanMonad boolean) boolean)
       ap1 f x    = return' (join$ f <$> x            )
       ap2 :: (boolean -> boolean ->            (BooleanMonad boolean) boolean) -> (BooleanMonad boolean) boolean -> (BooleanMonad boolean) boolean ->              m2 ((BooleanMonad boolean) boolean)
       ap2 f x y  = return' (join$ f <$> x <*> y      )
       ap3 :: (boolean -> boolean -> boolean -> (BooleanMonad boolean) boolean) -> (BooleanMonad boolean) boolean -> (BooleanMonad boolean) boolean -> (BooleanMonad boolean) boolean -> m2 ((BooleanMonad boolean) boolean)
       ap3 f x y z= return' (join$ f <$> x <*> y <*> z)

-- | TODO
falseC,trueC :: Boolean a => (BooleanMonad a) a
falseC = fromBool False
{-# INLINE falseC #-}
trueC  = fromBool True
{-# INLINE trueC #-}

-- | TODO
data ScopedWireName = ScopedWN Int [ByteString] ByteString
                      deriving (Ord, Eq)

-- | TODO
instance Show ScopedWireName where
  show (ScopedWN _ lst bs)
   = concat (map (<>"/") (map unpack lst) ++ [show bs])

-- | TODO
instance Hashable ScopedWireName where
  hashWithSalt nr (ScopedWN i _ _) = hashWithSalt nr i

-- | TODO
instance AtomToBoolean ByteString ScopedWireName where
  toBoolean bs = ScopedWN (hash bs)
                          []
                          bs
-- | TODO
scopeScopedWireName :: ByteString -> ScopedWireName -> ScopedWireName
scopeScopedWireName i (ScopedWN _nr lst b)
   = ScopedWN (hash (hash i,_nr))
              (i:lst)
              b

-- | TODO
data DuoXZ b
 = DuoXZ {runDuoXZ :: b} -- ^ Should be Boolean m b with SingleHelper (m b)
 | Duo {runDuoXZ :: b} -- ^ same thing, but does not depend on the helper
 deriving Show

-- | TODO
instance (SingleHelper b) => SingleHelper (DuoXZ b) where
  singleHelper = DuoXZ singleHelper
  substituteHelper b (DuoXZ v) = Duo$ substituteHelper b v
  substituteHelper _ v = v
  helperDependent (DuoXZ _) = True
  helperDependent (Duo   _) = False

-- | TODO
instance (Boolean b, SingleHelper b) => BooleanXZ (DuoXZ b) where
 zC = return$ singleHelper  -- identity function
 xC = DuoXZ <$> notC singleHelper
 gbufC a b = DuoXZ <$> join (iteC (runDuoXZ a) <$> (runDuoXZ <$> (bufC b)) <*> return singleHelper)
 combineC a b
  = DuoXZ <$> join (iteC singleHelper <$> andC (runDuoXZ a) (runDuoXZ b)
                                      <*> orC  (runDuoXZ a) (runDuoXZ b))
 bufC (DuoXZ b)
  = DuoXZ
    <$> join (iteC singleHelper <$> andC b0 b1
                                <*> orC  b0 b1)
   where b0 = substituteHelper False b
         b1 = substituteHelper True  b
 bufC b = return b

-- | TODO
instance (Boolean b, SingleHelper b) => Boolean (DuoXZ b) where
 type BooleanMonad (DuoXZ b) = BooleanMonad b
 fromBool b = Duo <$> fromBool b
 notC (DuoXZ a) = bufC =<< (DuoXZ <$> notC a)
 notC (Duo b) = Duo <$> notC b
 andC (Duo a) (Duo b) = Duo <$> andC a b
 andC a b   = DuoXZ <$> join (andC <$> (runDuoXZ <$> bufC a) <*> (runDuoXZ <$> bufC b))
 orC  (Duo a) (Duo b) = Duo <$> orC  a b
 orC  a b   = DuoXZ <$> join (orC  <$> (runDuoXZ <$> bufC a) <*> (runDuoXZ <$> bufC b))
 everythingBoolean = createEverythingBooleanFromStructure (Duo <$>) lift1 lift2 lift3
  where lift1 :: (b -> (BooleanMonad b) b) -> DuoXZ b -> (BooleanMonad b) (DuoXZ b)
        lift1 f (Duo a) = Duo <$> f a
        lift1 f a = bufC =<< (DuoXZ <$> (f . runDuoXZ) a)
        lift2 :: (b -> b -> (BooleanMonad b) b) -> DuoXZ b -> DuoXZ b -> (BooleanMonad b) (DuoXZ b)
        lift2 f (Duo a) (Duo b) = Duo <$> f a b
        lift2 f a b = bufC =<< (DuoXZ <$> join (f (runDuoXZ a) <$> (runDuoXZ <$> bufC b)))
        lift3 :: (b -> b -> b -> (BooleanMonad b) b) -> DuoXZ b -> DuoXZ b -> DuoXZ b -> (BooleanMonad b) (DuoXZ b)
        lift3 f (Duo a) (Duo b) (Duo c) = Duo <$> f a b c
        lift3 f a b c = bufC =<< (DuoXZ <$> join (f (runDuoXZ a) <$> (runDuoXZ <$> bufC b) <*> (runDuoXZ <$> bufC c)))
