{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates #-} -- local pattern binds warnings missing, as I cannot express those
{-# LANGUAGE OverloadedStrings, DeriveFoldable,DeriveTraversable,DeriveFunctor, NoImplicitPrelude #-}

{-|
Module      : BooleanSymbolic.NetStructure
Copyright   : (c) Sebastiaan J C Joosten
-}
module BooleanSymbolic.NetStructure (showForest, judgeForest, showNetGraph, getStructure, closeSolver, NETTree(..), Orientation(..)) where
import BooleanSymbolic.UseMiniSat as UMS (MiniSatA, PreLit, testEquivInIO, runMiniSatMonad, Solver,closeSolver)
import Control.Monad
import qualified Data.ByteString.Char8 as B (replicate,length)
import BooleanSymbolic.Class (falseC,trueC,Boolean(..))
import Data.Maybe (catMaybes,isJust)
import qualified Data.Set as Set
import CommonDataTypes.TraverseProps
import BaseLike.CustomPrelude
-- import System.IO

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in BooleanSymbolic/NetStructure.hs:\n  "++s)

-- | TODO
data NETTree x
 = NETLeaf x (MiniSatA PreLit) -- transfer
             (MiniSatA PreLit) -- ready
 | NETSync (NETTree x) [NETTree x] -- all these fire at once
 | NETXor  [NETTree x] (MiniSatA PreLit) -- transfer
                       (MiniSatA PreLit) -- ready
 | NETImpl (NETTree x)
           (NETTree x)
           (MiniSatA PreLit) -- transfer
           (MiniSatA PreLit) -- ready

transferLit :: NETTree t -> MiniSatA PreLit
transferLit (NETLeaf _ v _) = v
transferLit (NETSync v _  ) = transferLit v
transferLit (NETXor  _ v _) = v
transferLit (NETImpl _ _ v _) = v

readyLit :: NETTree t -> MiniSatA PreLit
readyLit (NETLeaf _ _ v) = v
readyLit (NETSync _ lst) = foldrM' andC trueC (map readyLit lst)
readyLit (NETXor  _ _ v) = v
readyLit (NETImpl _ _ _ v) = v

interspace :: Monoid t => [[t]] -> [t]
interspace []     = []
interspace [s]    = s
interspace (s:ss) = s ++[mempty]++ interspace ss

intercalate :: Monoid a => (a -> a -> a) -> [a] -> a
intercalate f = go
    where
      go []     = mempty
      go (s:[]) = s
      go (s:ss) = s `f` go ss

-- | TODO
showForest :: [NETTree ([ByteString],ByteString)] -> ByteString -> ByteString
showForest tree nm = nm<>" as a tree:\n"<> (intercalate (\a b -> a<>"\n"<>b) . interspace . map showTree) tree
 where showTree (NETLeaf x _ _)   = [pack$ show x]
       showTree (NETSync a lst)   = (concatSpecial "||" [showTree v | v<-(a:lst)])
       showTree (NETXor  lst _ _) = (concatSpecial "|" (map showTree lst))
       showTree (NETImpl h tl _ _) = (concatSpecial "/" (map showTree [h,tl]))
       concatSpecial pf ([(a:as)]) -- last one: add a space
        = trailEmpty$ (pf <> (dashFor pf) <> a):(map prefixSpace as)
       concatSpecial pf ((a:as):rst@(_:_))
        = (pf <> (dashFor pf) <> a):(map ((pf<>(unDashFor pf))<>) as)
          ++ concatSpecial pf rst
       concatSpecial _ _ = error "concatSpecial called on empty list!"
       prefixSpace "" = ""
       prefixSpace x = (B.replicate treeSpaceSize ' ') <> x
       trailEmpty [""] = [""]
       trailEmpty [] = [""]
       trailEmpty (a:as) = a:trailEmpty as
       dashFor pf   = B.replicate (treeSpaceSize-B.length pf) '-'
       unDashFor pf = B.replicate (treeSpaceSize-B.length pf) ' '
       treeSpaceSize = 4

getQueues :: NETTree ([ByteString], ByteString) -> [ByteString]
getQueues (NETLeaf a _ _)
 = [snd (shQueue a)]
getQueues (NETSync h tl  ) = concatMap getQueues (h:tl)
getQueues (NETXor lst _ _) = concatMap getQueues lst
getQueues (NETImpl a b _ _) = concatMap getQueues [a,b]

shQueue :: ([ByteString], ByteString) -> (ByteString,ByteString)
shQueue (scp,_)
 = (ref,ref<>" [shape=plaintext label=<<table border=\"0\"><TR><TD><TABLE BORDER=\"1\" cellspacing=\"0\"><TR><TD PORT=\"in\">&nbsp;&nbsp;</TD></TR><TR><TD PORT=\"out\">&nbsp;</TD></TR></TABLE></TD><TD>"<>name<>"</TD></TR></table>>];\n")
 where name = intercalate (\a b -> a <> "\\" <> b) scp
       ref="Queue"<>encode scp

mConcatMap :: Monoid c => (a -> c) -> [a] -> c -- can be generalised over foldable structures, which is not needed here and not used as it requires a diferent implementation
mConcatMap f = mconcat . map f

-- | TODO
showNetGraph :: [(NETTree ([ByteString],ByteString), Bool)] -> ByteString -> ByteString
showNetGraph network name
 = ( "digraph "<>name<>" {" <>
     "overlap=false;rankdir=TD;\n" <> mconcat queues
     <> mconcat flatdraw
     <> "\n}\n"
   )
 where
  flatdraw = mapWithIndex drawtree network
  queues   = Set.toList$ Set.fromList (mconcat [getQueues tr | (tr,_)<-network])
  drawtree i (NETSync a as,False)
    = drawTreeFromTop i$
        NETSync (NETLeaf ([],"P"<>pack (show i)) falseC falseC)
                (a:as)
  drawtree i (tree,False)
    = drawTreeFromTop i$
        NETSync (NETLeaf ([],"P"<>pack (show i)) falseC falseC)
                [tree]
  drawtree i (tree,True)
    = drawTreeFromTop i tree
  drawTreeFromTop :: Int -> NETTree ([ByteString],ByteString) -> ByteString
  drawTreeFromTop i (NETSync h tl)
    = case giveTwoSides i (h:tl) of
        ([(a,as)],[b]) -> as <> connect False a b -- do not draw top level synchroniser
        (upSide,downSide) -> syncVal
                             <> mConcatMap (connect True  syncNorth) upSide
                             <> mConcatMap (connect False syncSouth) downSide
    where (syncNorth,syncSouth,syncVal) = sync [i]
  drawTreeFromTop i e
    = case orient [] i e of
       (Up   (nm,res)) -> res <> nm<>" -> Snk"<>encode i<>";\n"
       (Down (nm,res)) -> res <> "Src"<>encode i<>" -> "<>nm<>";\n"
       (Both ((nm,res),_)) -> res <> nm<>" -> Snk"<>encode i<>";\n"
  giveTwoSides i lst -- balance; add sink/source if needed
    = case splitOver (mapWithIndex (orient [i]) lst) of
        ([],rhs) -> ([("Src"<>pack (show i),"")],rhs)
        (lhs,[]) -> (lhs,[("Snk"<>pack (show i),"")])
        (lhs,rhs) -> (lhs,rhs)
  splitOver oriented -- attempts to balance its arguments over Down and Up
    = case (ups++extraUps, downs) of
        (lhs,rhs@(_:_)) -> (lhs,rhs)
        (_,[]) -> (case (ups, downs++extraDowns) of
                    ([],_) -> (take 1 extraUps,drop 1 extraDowns)
                    (lhs@(_:_),rhs) -> (lhs,rhs)
                  )
    where ups = [a | Up a <- oriented]
          downs = [a | Down a <- oriented]
          extraUps = [a | Both (a,_) <- oriented]
          extraDowns = [a | Both (_,a) <- oriented]
  sync ref
   = (nm<>":n",nm<>":s", nm<>" [shape=none height=\"0\" label=<<table border=\"0\" cellspacing=\"2\" cellpadding=\"0\" width=\"52\" height=\"9\" FIXEDSIZE=\"true\"><TR><TD bgcolor=\"black\" width=\"48\" height=\"1\"></TD></TR><TR><TD bgcolor=\"black\" width=\"48\" height=\"1\"></TD></TR></table>>];\n")
   where nm = encode ref
  rout ref
   = (nm<>":n",nm<>":s", nm<>" [shape=none height=\"0\" label=<<table border=\"0\" cellspacing=\"0\" cellpadding=\"0\" width=\"50\" height=\"1\" FIXEDSIZE=\"true\" bgcolor=\"black\"><TR><TD></TD></TR></table>>];\n")
   where nm = encode ref
  orient _ _ (NETLeaf ([],v) _ _)
   = Both ((v,""),(v,""))
  orient _ _ (NETLeaf o@(_,v) _ _)
   = if v `elem` ["inputTransfer","increase"]
     then Down (qname<>":in", "")
     else Up   (qname<>":out", "")
   where (qname,_) = shQueue o
  orient lst i (NETSync h tl)
   = case splitOver oriented of
       ([],rhs) -> Down (syncNorth,syncVal <> mConcatMap (connect False syncSouth) rhs)
       (lhs,[]) -> Up   (syncSouth,syncVal <> mConcatMap (connect True  syncNorth) lhs)
       (lhs,rhs)-> Both ((syncSouth,syncVal <> mConcatMap (connect False syncSouth) rhs <> mConcatMap (connect True  syncNorth) lhs)
                        ,(syncNorth,syncVal <> mConcatMap (connect False syncSouth) rhs <> mConcatMap (connect True  syncNorth) lhs)
                        )
   where (syncNorth,syncSouth,syncVal) = sync ref
         oriented = mapWithIndex (orient ref) (h:tl)
         ref = i:lst
  orient lst i (NETImpl h tl _ _)
   = case (oH,oTl) of
       (Up h'       ,dwn           ) -> Up  $ switchFor h' (makeDown ref dwn)
       (Both (_ ,h'),Up   tl'      ) -> Down$ mergeFor h' tl'
       (Both (h',_ ),Down tl'      ) -> Up  $ switchFor h' tl'
       (Both (h1,h2),Both (tl1,tl2)) -> Both (switchFor h1 tl2, mergeFor h2 tl1)
       (Down h'     ,up            ) -> Down$ mergeFor h' (makeUp ref up)
   where (xorNorth,xorSouth,xorVal) = rout ref
         oH  = orient ref 0 h
         oTl = orient ref 1 tl
         mergeFor  h' tl' = (xorSouth,xorVal <> connect True  xorNorth h'  <> connect False xorSouth tl')
         switchFor h' tl' = (xorNorth,xorVal <> connect False xorSouth tl' <> connect True  xorNorth h' )
         ref = i:lst
  orient lst i (NETXor subs _ _)
   = case (allUp,allDown) of
      (True,False)  -> Up   resUp
      (False,True)  -> Down resDown
      (True,True)   -> Both (resUp,resDown)
      (False,False) -> if length ups > length downs then Up forceUp
                       else if length ups < length downs then Down forceDown
                       else Both (forceUp,forceDown)
   where (xorNorth,xorSouth,xorVal) = rout ref
         oriented = mapWithIndex (orient ref) subs
         allUp     = and (map (isJust . giveUp  ) oriented)
         allDown   = and (map (isJust . giveDown) oriented)
         resUp     = (xorSouth,xorVal <> mConcatMap (connect True  xorNorth) ups)
         resDown   = (xorNorth,xorVal <> mConcatMap (connect False xorSouth) downs)
         forceUp   = (xorSouth,xorVal <> mConcatMap (connect True  xorNorth) forceUps)
         forceDown = (xorNorth,xorVal <> mConcatMap (connect False xorSouth) forceDowns)
         forceUps,forceDowns :: [(ByteString,ByteString)]
         forceUps  = mapWithIndex (curry makeUp   ref) oriented
         forceDowns= mapWithIndex (curry makeDown ref) oriented
         ups   = catMaybes (map giveUp   oriented)
         downs = catMaybes (map giveDown oriented)
         ref = i:lst
         giveUp (Up a) = Just a
         giveUp (Both (a,_)) = Just a
         giveUp (Down _) = Nothing
         giveDown (Up _) = Nothing
         giveDown (Both (_,a)) = Just a
         giveDown (Down a) = Just a
  makeUp   _ (Up a) = a
  makeUp   _ (Both (a,_)) = a
  makeUp   r (Down a)
   = (syncNorth
     , connect True  ("Snk"<>encode r) (syncSouth, syncVal<>"Snk"<>encode r<>" [label=<eager sink>];\n")
     <>connect True  syncNorth a
     )
     where (syncNorth,syncSouth,syncVal) = sync r
  makeDown r (Up a)
   = (syncSouth
     , connect False ("Src"<>encode r) (syncNorth, syncVal<>"Src"<>encode r<>" [label=<eager source>];\n")
     <>connect False syncSouth a
     )
     where (syncNorth,syncSouth,syncVal) = sync r
  makeDown _ (Both (_,a)) = a
  makeDown _ (Down a) = a
  connect :: Bool -> ByteString -> (ByteString,ByteString) -> ByteString
  connect isReversed fromNm (toNm,toStr)
   = toStr
     <> (if isReversed
         then toNm   <> " -> " <> fromNm
         else fromNm <> " -> " <> toNm)
     <> ";\n"

-- | TODO
data Orientation a
 = Up a
 | Down a
 | Both (a,a)
 deriving (Traversable,Foldable,Functor)

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0..]

-- | TODO
judgeForest :: IO ([NETTree ([ByteString], ByteString)],Solver)
            -> IO ([(NETTree ([ByteString], ByteString), Bool)],Solver)
judgeForest i
 = do (iolst,s) <- i
      flip (,) s <$> mapM (judge s) iolst
 where
  judge :: Solver -> NETTree ([ByteString], ByteString) -> IO (NETTree ([ByteString], ByteString), Bool)
  judge s o = (,) o <$> UMS.testEquivInIO s (readyLit o) (transferLit o)

-- | TODO
getStructure :: MiniSatA (InverseProps PreLit) -> IO ([NETTree ([ByteString],ByteString)],Solver)
getStructure props'
 = do (InverseProps propList, solver) <- runMiniSatMonad props'
      flip (,) solver <$> analyse solver (singleVals propList)
 where singleVals :: [InverseProp PreLit] -> [NETTree ([ByteString], ByteString)]
       singleVals propList
        = [ uncurry (NETLeaf (b,c))
                 (case (bools,correspondingReady) of
                       ([b1],[b2]) -> (return b1,return b2)
                       ([b1],[])   -> (return b1,trueC)
                       ([_],_) -> fatal 65 ("The `Ready' property corresponding to "++show c++" should occur once and be one bit only")
                       _ -> fatal 64$ "Required: one-bit inputTransfer/increase or one-bit outputTransfer/decrease ("++show c++" has "++show (length bools)++" bits)"
                 )
          | (InverseProp a _ b props) <- propList
          , a `elem` ["queue", "sink", "source"]
          , (c,_, bools) <- props
          , c `elem` ["inputTransfer","outputTransfer","increase","decrease"]
          , let correspondingReady
                  = concat [bs | (c',_,bs) <- props
                               , c' `elem` (if c `elem` ["inputTransfer","increase"] then ["inputReady"] else ["outputReady"])
                           ]
          ]
       analyse :: Solver -> [NETTree x] -> IO [NETTree x]
       analyse solver lst
        = do (_, res1)       <- findEqualities solver lst -- finds *all* equalities, so it will be stable after one go
             (stable2, res2) <- findXors solver res1 -- may not be stable after one go..
             if stable2 then do (stable3, res3) <- findImpl solver res2
                                if stable3 then return res3 else analyse solver res3
                        else analyse solver res2
       -- findXors, findEqualities :: [NETTree t] -> IO (Bool, [NETTree t])
       findImpl s (o:lst)
        = do let testUnEquiv v = UMS.testEquivInIO s (transferLit o) (join$ andC <$> transferLit o <*> transferLit v)
             (res,remainder) <- first' testUnEquiv lst
             (stable, rest) <- findImpl s remainder
             case res of
                         Nothing -> return (stable, o:rest)
                         Just v  -> return (False, NETImpl o v (join$ andC <$> (notC =<< transferLit o) <*> transferLit v) (join$ andC <$> (notC =<< readyLit o) <*> readyLit v) : rest)
       findImpl _ [] = pure (True,[])
       findXors s (o:lst)
        = do let testUnEquiv v = UMS.testEquivInIO s falseC (join$ andC <$> transferLit o <*> transferLit v)
             (res,remainder) <- first' testUnEquiv lst
             (stable, rest) <- findXors s remainder
             case res of
                         Nothing -> return (stable, o:rest)
                         Just v ->  return (False, NETXor [o,v] (join$ orC <$> transferLit v <*> transferLit o) (join$ orC <$> readyLit v <*> readyLit o) : rest)
       findXors _ [] = pure (True,[])
       findEqualities s (o:lst)
        = do (equiv,notEquiv) <- partitionM (testEquiv s (transferLit o)) lst
             (\(stable,rest) -> ( null equiv && stable -- if we found nothing, we remain stable
                                , if (null equiv) then o:rest
                                                  else NETSync o equiv:rest
                                ) ) <$> findEqualities s notEquiv
       findEqualities _ [] = pure (True,[]) -- no equalities found, so we are stable!
       testEquiv :: Solver -> MiniSatA PreLit -> NETTree t -> IO Bool
       testEquiv s val x = UMS.testEquivInIO s val (transferLit x)
       partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a])
       partitionM p xs = foldlM f ([], []) xs
                       where f (a, b) x = p x >>= (\ flag -> return $ if flag then (x : a, b) else (a, x : b))
       first' :: (Monad m) => (a -> m Bool) -> [a] -> m (Maybe a,[a])
       first' _ [] = return (Nothing,[])
       first' f (a:rst)
        = do res <- f a
             if res then return (Just a,rst) else
              do (res',lst) <- first' f rst
                 return (res',a:lst)
