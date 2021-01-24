{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, OverloadedStrings, FlexibleInstances, MultiParamTypeClasses #-}

{-|
Module      : Madl.Deadlock.Nuxmv
Description : Nuxmv model generation.
Copyright   : (c) Sanne Wouda 2015-2016, Tessa Belder 2016

This module generates a nuxmv model from a colored network. It also contains functions to run different tools on this model.
-}
module Madl.Deadlock.Nuxmv (
        writeModel, hasDeadlock,
        ReachabilityEngine(..), AbcEngine(..), NuxmvEngine(..),
        ReachabilityOptions(..), ReachabilityInput(..)
        ) where

-- import Debug.Trace

import Control.Monad (when)

import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.String (IsString)
import qualified Data.Text as T

import Utils.Concatable (WithApplicative(..))
import qualified Utils.Concatable as C (unlines)
import Utils.Map
import Utils.NuxmvCode
import Utils.Text

import Text.Regex.TDFA ((=~))
import System.IO (hPutStrLn,hClose)
import System.IO.Temp (withTempFile)
import System.Process (callProcess)
import System.Environment

--import Control.Concurrent (forkIO,killThread)
import System.Directory (removeFile)
import Madl.Invariants
import Madl.Islands
import Madl.MsgTypes
import Madl.Network

import Madl.Deadlock.Formulas

-- Error function
fileName :: Text
fileName = "Madl.Deadlock.Nuxmv"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- | Type to represent a list of fields in a colorset
type FieldPath = [Text]

-- | Finds all the type fields in a colorset, as well as the paths leading to these fields
disjFields :: IsColorSet a => a -> [(FieldPath, [Text])]
disjFields = disjs [] . toColorSet where
    disjs :: FieldPath -> ColorSet -> [(FieldPath, [Text])]
    disjs prefix colors =
        -- if Hash.size m >= 2 then
            choice : concat (map (uncurry (\k -> either (structs $ prefix ++ [k]) bvs)) $ colorSetAssocs colors) where
        --else concat $ Hash.map (structs prefix) m where
                choice :: (FieldPath, [Text])
                choice = (prefix, map nuxmv_color $ colorSetKeys colors)
    structs :: FieldPath -> Struct -> [(FieldPath, [Text])]
    structs prefix = concat . map (uncurry (\k -> either (disjs $ prefix ++ [k]) bvs)) . structAssocs
    bvs :: BitVector -> [(FieldPath, [Text])]
    bvs _ = []

-- | Finds the size and values of all the bitvectors in a colorset, as well the paths leading to these bitvectors
bitVectors :: IsColorSet a => a -> [(FieldPath, Int, Set Int)]
bitVectors = disjs [] . toColorSet where
    disjs prefix = concat . map (uncurry (\k -> either (structs $ prefix ++ [k]) (bvs $ prefix ++ [k]))) . colorSetAssocs
    bvs prefix bv = [(prefix, bvSize bv, bvInts bv)]
    structs prefix = concat . map (uncurry (\k -> either (disjs $ prefix ++ [k]) (bvs $ prefix ++ [k]))) . structAssocs

-- | Variable declarations for a component in a network
varDefinition :: ColoredNetwork -> ComponentID -> ColorSet -> [Text]
varDefinition net cID t = case getComponent net cID of
    Queue name size -> nuxmv_int State (size+1) (nuxmvQueueSizeVar name) --variable to store the number of packets in the queue
                    : mapMaybe fldVar (disjFields t) ++ map bvVar (bitVectors t) where
                        -- Variables to store the values of the type fields of the packets in the queue
                        fldVar :: (FieldPath, [Text]) -> Maybe Text
                        fldVar (_, []) = Nothing
                        fldVar (flds, fieldValues) = Just $ nuxmv_array State (int_type size) (enum_type fieldValues) (nuxmvQueueVar name flds)
                        -- Variables to store the values of the bitvector fields of the packets in the queue
                        bvVar :: (FieldPath, Int, Set Int) -> Text
                        bvVar (flds, bitSize, bvVals) =
                            nuxmv_array State (int_type size) elemType (nuxmvQueueVar name flds) where
                                    elemType = if Set.size bvVals == 1 then range_type x x else int_type (2^bitSize)
                                    x = Set.elemAt 0 bvVals
    Buffer name size -> ((nuxmv_int Input size $ buffer_oracle name):(nuxmv_int State (size+1) (nuxmvBufferSizeVar name) --variable to store the number of packets in the queue
                    : mapMaybe fldVar (disjFields t) ++ map bvVar (bitVectors t))) where
                        -- Variables to store the values of the type fields of the packets in the queue
                        fldVar :: (FieldPath, [Text]) -> Maybe Text
                        fldVar (_, []) = Nothing
                        fldVar (flds, fieldValues) = Just $ nuxmv_array State (int_type size) (enum_type fieldValues) (nuxmvBufferVar name flds)
                        -- Variables to store the values of the bitvector fields of the packets in the queue
                        bvVar :: (FieldPath, Int, Set Int) -> Text
                        bvVar (flds, bitSize, bvVals) =
                            nuxmv_array State (int_type size) elemType (nuxmvBufferVar name flds) where
                                    elemType = if Set.size bvVals == 1 then range_type x x else int_type (2^bitSize)
                                    x = Set.elemAt 0 bvVals
    Source name msg ->
        (if emptyColorSet msg then [] else [nuxmv_bool Input $ source_oracle name]) --variable to determine whether the source is irdy
        -- Variables to store the values of the type fields of the packets send by the source
        ++ map (\(flds, fieldValues) -> nuxmv_enum Input fieldValues (nuxmvSourceVar name flds)) (disjFields t)
        -- Variables to store the values of the bitvector fields of the packets send by the source
        ++ map (\(flds, bitSize, _bvVals) -> nuxmv_int Input (2^bitSize) (nuxmvSourceVar name flds)) (bitVectors t)
    PatientSource name msg ->
        (if emptyColorSet msg then [] else [nuxmv_bool Input $ source_oracle name])
        ++ map (\(flds, fieldValues) -> nuxmv_enum Input fieldValues (nuxmvSourceVar name flds)) (disjFields t)
        ++ map (\(flds, bitSize, _bvVals) -> nuxmv_int Input (2^bitSize) (nuxmvSourceVar name flds)) (bitVectors t)
    Sink name -> [nuxmv_bool Input $ sink_oracle name] --variable to determine whether the sink is trdy
    Merge name -> [nuxmv_int Input (getNrInputs net cID) $ merge_oracle name] --variable to determine which input of the merge is selected
    LoadBalancer name -> [nuxmv_int Input (getNrOutputs net cID) $ loadbalancer_oracle name] --variable to determine which output of the loadbalancer is selected
    MultiMatch name _ -> [nuxmv_int Input (getNrOutputs net cID) $ mmatch_m_oracle name, --variable to determine which match-input of the multimatch is selected
                          nuxmv_int Input (getNrInputs net cID - getNrOutputs net cID) $ mmatch_d_oracle name] --variable to determine which data-input of the multimatch is selected
    DeadSink{} -> []
    Function{} -> []
    Vars{} -> []
    Cut{} -> []
    Switch{} -> []
    Fork{} -> []
    ControlJoin{} -> []
    FControlJoin{} -> []
    Match{} -> []
    Joitch{} -> []
    Automaton{componentName=name,nrOfStates=n,transitions=ts} ->
        [nuxmv_int_with_singleton State n (nuxmv_psvar name),
         nuxmv_int_with_singleton Input (length ts) (nuxmv_ptvar name)] -- ++
        --[nuxmv_bool State (nuxmv_proc_stvar name i) | i <- [0..n-1]] ++
        --[nuxmv_bool State (nuxmv_proc_deadvar name i) | i <- [0..(length ts)-1]]
    GuardQueue name size -> nuxmv_int State (size+1) (nuxmvQueueSizeVar name)
                        : ((nuxmv_int Input (getNrInputs net cID) $ merge_oracle name)
                        : mapMaybe fldVar (disjFields t) ++ map bvVar (bitVectors t)) where
                        -- Variables to store the values of the type fields of the packets in the queue
                        fldVar :: (FieldPath, [Text]) -> Maybe Text
                        fldVar (_, []) = Nothing
                        fldVar (flds, fieldValues) = Just $ nuxmv_array State (int_type size) (enum_type fieldValues) (nuxmvQueueVar name flds)
                        -- Variables to store the values of the bitvector fields of the packets in the queue
                        bvVar :: (FieldPath, Int, Set Int) -> Text
                        bvVar (flds, bitSize, bvVals) =
                            nuxmv_array State (int_type size) elemType (nuxmvQueueVar name flds) where
                                    elemType = if Set.size bvVals == 1 then range_type x x else int_type (2^bitSize)
                                    x = Set.elemAt 0 bvVals


-- | Produces a condition that is true if any island in the given islandset is enabled
nuxmvAnyEnabled :: ColoredNetwork -> IslandSet ChannelID -> Text
nuxmvAnyEnabled net is = if null conds then nuxmv_true else nuxmv_or conds where
    conds = map (nuxmvEnabled net) (IM.elems is)

-- | Produces a condition that is true if the given island is enabled
nuxmvEnabled :: ColoredNetwork -> Island ChannelID -> Text
nuxmvEnabled net island = nuxmv_and (irdy_island ++ trdy_island ++ switchConditions) where
    -- an island is enabled if it is irdy, trdy, and any additional conditions are satisfied
    irdy_island = mapMaybe (uncurry irdy . getInitiatorWithPort net) $ Map.elems (islandChannels island)
    irdy cID port = case getComponent net cID of
        Source name msg -> Just $ if emptyColorSet msg then nuxmv_false else source_oracle name
        PatientSource name msg -> Just $ if emptyColorSet msg then nuxmv_false else source_oracle name
        Sink{} -> Nothing
        DeadSink{} -> Nothing
        Function{} -> Nothing
        Queue name _  -> Just $ nuxmv_unequal (nuxmvQueueSizeVar name) "0"
        Buffer name _ -> Just $ nuxmv_unequal (nuxmvBufferSizeVar name) "0"
        Vars{} -> Nothing
        Cut{} -> Nothing
        Switch{} -> Nothing
        Merge{} -> Nothing
        Fork{} -> Nothing
        ControlJoin{} -> Nothing
        FControlJoin{} -> Nothing
        Match{} ->  Nothing
        MultiMatch{} -> Nothing
        LoadBalancer name -> Just $ nuxmv_equals (loadbalancer_oracle name) (showT port)
        Joitch{} -> Nothing
        Automaton{} -> Nothing -- snnw: every transition has an consuming port, so we check transitions only there.
        GuardQueue name _ -> Just $ nuxmv_or [nuxmv_and [(nuxmv_equals (merge_oracle name) "0"), (nuxmv_unequal (nuxmvQueueSizeVar name) "0")]
                                              , nuxmv_equals (merge_oracle name) "1"]

    trdy_island = mapMaybe (uncurry trdy . getTargetWithPort net) $ Map.elems (islandChannels island)
    trdy cID port = case getComponent net cID of
        Source{} -> Nothing
        PatientSource{} -> Nothing
        Sink name -> Just $ sink_oracle name
        DeadSink{} -> Just $ nuxmv_false
        Function{} -> Nothing
        Queue name cap  -> Just $ nuxmv_unequal (nuxmvQueueSizeVar name) (showT cap)
        Buffer name cap -> Just $ nuxmv_unequal (nuxmvBufferSizeVar name) (showT cap)
        Vars{} -> Nothing
        Cut{} -> Nothing
        Switch{} -> Nothing
        Merge name -> Just $ nuxmv_equals (merge_oracle name) (showT port)
        Fork{} -> Nothing
        ControlJoin{} -> Nothing
        FControlJoin{} -> Nothing
        Match{} ->  Nothing
        MultiMatch name _ -> Just $ if port < getNrOutputs net cID
            then nuxmv_equals (mmatch_m_oracle name) (showT port)
            else nuxmv_equals (mmatch_d_oracle name) (showT $ port - getNrOutputs net cID)
        LoadBalancer{} -> Nothing
        Joitch{} -> Nothing
        Automaton{componentName=name} -> Just $
            nuxmv_and [nuxmv_equals (nuxmv_psvar name) (showT s),
                       nuxmv_equals (showT idx) (nuxmv_ptvar name)] where
            idx :: Int
            (AutomatonT{startState=s}, idx) = lookupM (src 159) cID (islandTransitions island)
        GuardQueue name size -> if port == 0 then Just $ nuxmv_and [(nuxmv_equals (merge_oracle name) "0"), (nuxmv_unequal (nuxmvQueueSizeVar name) (showT size))]
                        else Just $ nuxmv_and [(nuxmv_equals (merge_oracle name) "1"), (nuxmv_equals (nuxmvQueueSizeVar name) "0")]


    switchConditions = concatMap (isTrue net) $ condition net island

-- | Produces a condition that is true if the given boolean function is satisfied
isTrue :: ColoredNetwork -> MFunctionBool -> [Text]
isTrue net = maybeToList . runWA . nuxmvValueB [] IM.empty (makeArgsAt 0 net)

-- | todo(tssb, snnw)
matchesTypeAt :: IsColorSet a => Int -> ColoredNetwork -> (MFunctionDisj, a) -> [Text]
matchesTypeAt at net (msgF, t) = mapMaybe (runWA . cond) (disjFields t) ++ mapMaybe (runWA . condBV) (bitVectors t) where
    condBV :: (FieldPath, Int, Set Int) -> WithApplicative Maybe Text
    condBV (flds, _, values) = nuxmv_or (map (\v -> nuxmv_equals (nuxmvValueT flds IM.empty cmap msgF) (pure $ showT v)) (Set.elems values) )
    cond :: (FieldPath, [Text]) -> WithApplicative Maybe Text
    cond (_, []) = nuxmv_false
    cond (_, ["val_otherwise"]) = nuxmv_false
    cond (flds, values) = nuxmv_in (nuxmvValueT flds IM.empty cmap msgF) (WA . Just $ enum_type values) -- TODO(snnw): check if value is valid
    cmap = makeArgsAt at net

-- | Produce the init statement for the queue size variable of the given queue
queueSizeInit :: Component -> Maybe Text
queueSizeInit (Queue name _) = Just $ nuxmv_init (nuxmvQueueSizeVar name) "0"
queueSizeInit (GuardQueue name _) = Just $ nuxmv_init (nuxmvQueueSizeVar name) "0"
queueSizeInit _ = Nothing

-- | Produce the next statement for the queue size variable of the given queue
queueSizeUpdate :: ColoredNetwork -> Component -> IslandSet ChannelID -> IslandSet ChannelID -> [Text]
queueSizeUpdate net (Queue name size) ins outs = nuxmv_next qs $ nuxmv_switch [
      (nuxmv_equals qs "0", nuxmv_toint (nuxmvAnyEnabled net ins))
    , (nuxmv_equals qs (showT size), nuxmv_minus (showT size) (nuxmv_toint $ nuxmvAnyEnabled net outs))
    , (nuxmv_true, nuxmv_add [nuxmvQueueSizeVar name, nuxmv_minus (nuxmv_toint $ nuxmvAnyEnabled net ins) (nuxmv_toint $ nuxmvAnyEnabled net outs)])
    ] where
    qs = nuxmvQueueSizeVar name
queueSizeUpdate net (GuardQueue name size) ins outs = nuxmv_next qs $ nuxmv_switch [
    (nuxmv_equals "0" (merge_oracle name), T.intercalate "" $ nuxmv_switch [
      (nuxmv_equals qs "0", nuxmv_toint (nuxmvAnyEnabled net ins))
    , (nuxmv_equals qs (showT size), nuxmv_minus (showT size) (nuxmv_toint $ nuxmvAnyEnabled net outs))
    , (nuxmv_true, nuxmv_add [nuxmvQueueSizeVar name, nuxmv_minus (nuxmv_toint $ nuxmvAnyEnabled net ins) (nuxmv_toint $ nuxmvAnyEnabled net outs)])])
    ,(nuxmv_equals "1" (merge_oracle name), qs)
    ] where
    qs = nuxmvQueueSizeVar name

queueSizeUpdate _ _ _ _ = []

-- | todo(tssb, snnw) : can we remove this?
queuePosInit :: Component -> ColorSet -> Int -> Maybe Text
queuePosInit _ _ _ = Nothing

-- | Produce the next statement for the queue field and bitvec value variables
queuePosUpdate :: ColoredNetwork -> (ComponentID, Component) -> ColorSet -> IslandSet ChannelID -> IslandSet ChannelID -> Int -> [Text]
queuePosUpdate net c t ins outs i =
    concatMap (assign net outs ins c i) (fields ++ vecs) where
        fields = map fst $ filter (\(_,vs) -> length vs > 1) (disjFields t)
        vecs = map (\(a,_,_) -> a) $ filter (\(_,n,vs) -> (n /= 0) && (Set.size vs /= 1)) (bitVectors t)
        --"Q" +++ name +++ "_ = "


-- | Produce the init statement for the buffer size variable of the given buffer
bufferSizeInit :: Component -> Maybe Text
bufferSizeInit (Buffer name _) = Just $ nuxmv_init (nuxmvBufferSizeVar name) "0"
bufferSizeInit _ = Nothing


-- | Produce the next statement for the buffer size variable of the given buffer
bufferSizeUpdate :: ColoredNetwork -> Component -> IslandSet ChannelID -> IslandSet ChannelID -> [Text]
bufferSizeUpdate net (Buffer name size) ins outs = nuxmv_next bs $ nuxmv_switch [
      (nuxmv_equals bs "0", nuxmv_toint (nuxmvAnyEnabled net ins))
    , (nuxmv_equals bs (showT size), nuxmv_minus (showT size) (nuxmv_toint $ nuxmvAnyEnabled net outs))
    , (nuxmv_true, nuxmv_add [nuxmvBufferSizeVar name, nuxmv_minus (nuxmv_toint $ nuxmvAnyEnabled net ins) (nuxmv_toint $ nuxmvAnyEnabled net outs)])
    ] where
    bs = nuxmvBufferSizeVar name
bufferSizeUpdate _ _ _ _ = []


-- | Produce the next statement for the buffer field and bitvec value variables
bufferPosUpdate :: ColoredNetwork -> (ComponentID, Component) -> ColorSet -> IslandSet ChannelID -> IslandSet ChannelID -> Int -> [Text]
bufferPosUpdate net c t ins outs i =
    concatMap (assign net outs ins c i) (fields ++ vecs) where
        fields = map fst $ filter (\(_,vs) -> length vs > 1) (disjFields t)
        vecs = map (\(a,_,_) -> a) $ filter (\(_,n,vs) -> (n /= 0) && (Set.size vs /= 1)) (bitVectors t)


-- | todo(tssb, snnw) : can we remove this?
bufferPosInit :: Component -> ColorSet -> Int -> Maybe Text
bufferPosInit _ _ _ = Nothing


-- | Produce SMV code for the given mfunctiondisj
nuxmvValueT :: [Text] -> ArgMap -> CMap -> MFunctionDisj -> WithApplicative Maybe Text
nuxmvValueT [] _ _ (XChoice name _f) = pure $ nuxmv_color name
nuxmvValueT [_] _ _ (XChoice name _f) = pure $ nuxmv_color name
nuxmvValueT flds args cmap (XSelect s m) = C.unlines $ nuxmv_switch (mapMaybeCase toCase $ Hash.assocs m) where
    toCase (k,f) = (nuxmv_equals (nuxmvValueT [] args cmap s) (pure $ nuxmv_color k), nuxmvValueT flds args cmap f)
nuxmvValueT flds args cmap (XIfThenElseD b t f) = nuxmv_ite (nuxmvValueB [] args cmap b) (nuxmvValueT flds args cmap t) (nuxmvValueT flds args cmap f)
nuxmvValueT flds args cmap (XVar i) = nuxmvValueT flds IM.empty cmap (lookupM (src 188) i args)
nuxmvValueT flds _ cmap (XInput i) = f (lookupM (src 191) i cmap) where
    f Nothing = WA Nothing -- fatal 176 "source or queue lacks a value expression"
    f (Just (prefix, postfix)) = pure $ T.intercalate "_" ([prefix] ++ flds ++ [postfix]) -- TODO(snnw) generate Nothing if `i` has no corresponding field
nuxmvValueT (fld:flds) args cmap (XChoice name f) = if name == fld then nuxmvValueCV flds args cmap f else WA Nothing
nuxmvValueT flds _args cmap (XAppliedTo f gs) = nuxmvValueT flds args' cmap f where
    args' = IM.fromList (zip [0..] gs)
    -- valueExpressions = map (runWA . nuxmvValueT flds args cmap) gs
nuxmvValueT flds args cmap (XGetFieldDisj name f) = nuxmvValueC (name:flds) args cmap f

-- | Produce SMV code for the given mfunctionstruct
nuxmvValueC :: [Text] -> ArgMap -> CMap -> MFunctionStruct -> WithApplicative Maybe Text
nuxmvValueC (fld:flds) args cmap (XConcat m) = nuxmvValueTV flds args cmap =<< WA (Hash.lookup fld m)
nuxmvValueC _ _ _ (XConcat{}) = WA Nothing
nuxmvValueC flds args cmap (XChooseStruct name f) = nuxmvValueT (name:flds) args cmap f
nuxmvValueC flds args cmap (XIfThenElseC b t f) = nuxmv_ite (nuxmvValueB [] args cmap b) (nuxmvValueC flds args cmap t) (nuxmvValueC flds args cmap f)

-- | Produce SMV code for the given mfunctionbool
nuxmvValueB :: [Text] -> ArgMap -> CMap -> MFunctionBool -> WithApplicative Maybe Text
nuxmvValueB flds args cmap (XCompare op f g) = operator (nuxmvValueV flds args cmap f) (nuxmvValueV flds args cmap g) where
    operator = case op of Eq -> nuxmv_equals; Gt -> nuxmv_gt
nuxmvValueB _ args cmap (XMatch f g) = nuxmv_equals (nuxmvValueT [] args cmap f) (nuxmvValueT [] args cmap g)
nuxmvValueB _ _ _ XTrue = nuxmv_true
nuxmvValueB _ _ _ XFalse = nuxmv_false
nuxmvValueB flds args cmap (XUnOpBool op f) = operator $ nuxmvValueB flds args cmap f where
    operator = case op of Not -> nuxmv_negate
nuxmvValueB flds args cmap (XBinOpBool op f g) = operator (nuxmvValueB flds args cmap f) (nuxmvValueB flds args cmap g) where
    operator = case op of Or -> nuxmv_or_bin; And -> nuxmv_and_bin
nuxmvValueB flds _args cmap (XAppliedToB f gs) = nuxmvValueB flds args' cmap f where
    args' = IM.fromList (zip [0..] gs)
nuxmvValueB flds args cmap (XSelectB s m) = C.unlines $ nuxmv_switch (mapMaybeCase toCase $ Hash.assocs m) where
    toCase (k,f) = (nuxmv_equals (nuxmvValueT [] args cmap s) (pure $ nuxmv_color k), nuxmvValueB flds args cmap f)
nuxmvValueB flds args cmap (XIfThenElseB b t f) = nuxmv_ite (nuxmvValueB [] args cmap b) (nuxmvValueB flds args cmap t) (nuxmvValueB flds args cmap f)

-- | Produce SMV code for the given mfunctionval
nuxmvValueV :: [Text] -> ArgMap -> CMap -> MFunctionVal -> WithApplicative Maybe Text
nuxmvValueV _ _ _ (XConst i) = pure (showT i)
nuxmvValueV flds args cmap (XUnOp op f) = operator $ nuxmvValueV flds args cmap f where
    operator = case op of Neg -> nuxmv_negate
nuxmvValueV flds args cmap (XBinOp op f g) = operator (nuxmvValueV flds args cmap f) (nuxmvValueV flds args cmap g) where
    operator = case op of Plus -> nuxmv_add_bin; Minus -> nuxmv_minus; Mult -> nuxmv_mult_bin; Mod -> nuxmv_mod
nuxmvValueV flds args cmap (XChooseVal name f) = nuxmvValueT (name:flds) args cmap f
nuxmvValueV flds args cmap (XGetFieldVal name f) = nuxmvValueC (name:flds) args cmap f
nuxmvValueV flds args cmap (XIfThenElseV b t f) = nuxmv_ite (nuxmvValueB [] args cmap b) (nuxmvValueV flds args cmap t) (nuxmvValueV flds args cmap f)

-- | Produce SMV code for the given ormfval mfunctiondisj
nuxmvValueTV :: [Text] -> ArgMap -> CMap -> OrMFVal MFunctionDisj -> WithApplicative Maybe Text
nuxmvValueTV flds args cmap (Left f) = nuxmvValueT flds args cmap f
nuxmvValueTV flds args cmap (Right f) = nuxmvValueV flds args cmap f

-- | Produce SMV code for the given ormfval mfunctionstruct
nuxmvValueCV :: [Text] -> ArgMap -> CMap -> OrMFVal MFunctionStruct -> WithApplicative Maybe Text
nuxmvValueCV flds args cmap (Left f) = nuxmvValueC flds args cmap f
nuxmvValueCV flds args cmap (Right f) = nuxmvValueV flds args cmap f

-- | Produce next statements representing transitions in the network
assign :: ColoredNetwork -> IslandSet ChannelID -> IslandSet ChannelID -> (ComponentID, Component) -> Int -> FieldPath -> [Text]
assign net outs ins (node, (Queue baseName size)) i flds = nuxmv_next curVal . nuxmv_switch $
    mapMaybe pushPop (IM.toList ins) ++ mapMaybe push (IM.toList ins) ++ [pop, none] where
        pushPop :: (Int, Island ChannelID) -> Maybe (Text, Text)
        pushPop = exec True shiftVal outs
        push :: (Int, Island ChannelID) -> Maybe (Text, Text)
        push = exec False curVal IM.empty
        exec :: Bool -> Text -> IslandSet ChannelID -> (Int, Island ChannelID) -> Maybe (Text, Text)
        exec pushpop nextVal outIslands (_, inIsland) = maybeCase $
            (nuxmv_and [pure $ nuxmvAnyEnabled net outIslands, pure $ nuxmvEnabled net inIsland, matchesFieldValues flds IM.empty cmap f xType],
             nuxmv_ite (nuxmv_atmost sizeName (pure . showT $ if pushpop then i + 1 else i)) (nuxmvValueT flds IM.empty cmap f) (pure nextVal))
            where
                f = dataPropagation net inIsland x
                x :: ChannelID
                [x] = getInChannels net node
        cmap :: CMap
        cmap = makeArgs net
        pop :: (Text, Text)
        pop = (nuxmvAnyEnabled net outs, shiftVal)
        none :: (Text, Text)
        none = (nuxmv_true, curVal)
        (WA (Just curVal)) = nuxmvValueT flds IM.empty (makeArgsAt i net) (XInput node)
            -- name +++ "[" +++ showT i +++ "]"
        (WA (Just shiftVal)) = nuxmvValueT flds IM.empty (makeArgsAt (min (i+1) (size-1)) net) (XInput node)
            -- name +++ "[" +++ showT (max (i+1) (size-1)) +++ "]"
        -- name = nuxmvQueueVar c flds
        sizeName = nuxmv_qsvar (pure baseName)
        [xOut] = getOutChannels net node
        (_, xType) = getChannel net xOut
assign net outs ins (node, (Buffer baseName size)) i flds = nuxmv_next curVal . nuxmv_switch $
    mapMaybe pushPop (IM.toList ins) ++ mapMaybe push (IM.toList ins) ++ [pop, none] where
        pushPop :: (Int, Island ChannelID) -> Maybe (Text, Text)
        pushPop (_, inIsland) = maybeCase $
                      (nuxmv_and [pure $ nuxmvAnyEnabled net outs, pure $ nuxmvEnabled net inIsland, matchesFieldValues flds IM.empty cmap f xType],
                      nuxmv_ite (nuxmv_atmost sizeName (pure $ showT (i+1))) (nuxmvValueT flds IM.empty cmap f) (nuxmv_ite (nuxmv_gt (pure $ buffer_oracle baseName) (pure $ showT i)) (pure curVal) (pure shiftVal)))
                  where
                      f = dataPropagation net inIsland x
                      x :: ChannelID
                      [x] = getInChannels net node--exec True shiftVal outs
        push :: (Int, Island ChannelID) -> Maybe (Text, Text)
        push (_, inIsland) = maybeCase $
                  (nuxmv_and [pure $ nuxmvAnyEnabled net IM.empty, pure $ nuxmvEnabled net inIsland, matchesFieldValues flds IM.empty cmap f xType],
                  nuxmv_ite (nuxmv_atmost sizeName (pure $ showT i)) (nuxmvValueT flds IM.empty cmap f) (pure curVal))
               where
                  f = dataPropagation net inIsland x
                  x :: ChannelID
                  [x] = getInChannels net node --exec False curVal IM.empty
        {-exec :: Bool -> Text -> IslandSet ChannelID -> (Int, Island ChannelID) -> Maybe (Text, Text)
        exec pushpop nextVal outIslands (_, inIsland) = maybeCase $
            (nuxmv_and [pure $ nuxmvAnyEnabled net outIslands, pure $ nuxmvEnabled net inIsland, matchesFieldValues flds IM.empty cmap f xType],
             nuxmv_ite (nuxmv_atmost sizeName (pure . showT $ if pushpop then i + 1 else i)) (nuxmvValueT flds IM.empty cmap f) (pure nextVal))
            where
                f = dataPropagation net inIsland x
                x :: ChannelID
                [x] = getInChannels net node-}
        cmap :: CMap
        cmap = makeArgs net
        pop :: (Text, Text)
        pop = (nuxmvAnyEnabled net outs, shiftVal)
        none :: (Text, Text)
        none = (nuxmv_true, curVal)
        (WA (Just curVal)) = nuxmvValueT flds IM.empty (makeArgsAt i net) (XInput node)
            -- name +++ "[" +++ showT i +++ "]"
        (WA (Just shiftVal)) = nuxmvValueT flds IM.empty (makeArgsAt (min (i+1) (size-1)) net) (XInput node)
            -- name +++ "[" +++ showT (max (i+1) (size-1)) +++ "]"
        -- name = nuxmvQueueVar c flds
        sizeName = nuxmv_bsvar (pure baseName)
        [xOut] = getOutChannels net node
        (_, xType) = getChannel net xOut
assign net outs ins (node, (GuardQueue baseName size)) i flds = nuxmv_next curVal $ nuxmv_switch [
        (nuxmv_equals "0" (merge_oracle baseName), T.intercalate "" $ nuxmv_switch $ mapMaybe pushPop (IM.toList ins) ++ mapMaybe push (IM.toList ins) ++ [pop, none])
        ,(nuxmv_equals "1" (merge_oracle baseName), curVal)
    ]

    where
        pushPop :: (Int, Island ChannelID) -> Maybe (Text, Text)
        pushPop = exec True shiftVal outs
        push :: (Int, Island ChannelID) -> Maybe (Text, Text)
        push = exec False curVal IM.empty
        exec :: Bool -> Text -> IslandSet ChannelID -> (Int, Island ChannelID) -> Maybe (Text, Text)
        exec pushpop nextVal outIslands (_, inIsland) = maybeCase $
            (nuxmv_and [pure $ nuxmvAnyEnabled net outIslands, pure $ nuxmvEnabled net inIsland, matchesFieldValues flds IM.empty cmap f xType],
             nuxmv_ite (nuxmv_atmost sizeName (pure . showT $ if pushpop then i + 1 else i)) (nuxmvValueT flds IM.empty cmap f) (pure nextVal))
            where
                f = dataPropagation net inIsland x
                x :: ChannelID
                [x,_] = getInChannels net node
        cmap :: CMap
        cmap = makeArgs net
        pop :: (Text, Text)
        pop = (nuxmvAnyEnabled net outs, shiftVal)
        none :: (Text, Text)
        none = (nuxmv_true, curVal)
        (WA (Just curVal)) = nuxmvValueT flds IM.empty (makeArgsAt i net) (XInput node)
            -- name +++ "[" +++ showT i +++ "]"
        (WA (Just shiftVal)) = nuxmvValueT flds IM.empty (makeArgsAt (min (i+1) (size-1)) net) (XInput node)
            -- name +++ "[" +++ showT (max (i+1) (size-1)) +++ "]"
        -- name = nuxmvQueueVar c flds
        sizeName = nuxmv_qsvar (pure baseName)
        [xOut] = getOutChannels net node
        (_, xType) = getChannel net xOut
assign _ _ _ _ _ _ = []

-- | Check if the packet represented by the given mfunctiondisj matches the given colorset
matchesFieldValues :: FieldPath -> ArgMap -> CMap -> MFunctionDisj -> ColorSet -> WithApplicative Maybe Text
matchesFieldValues flds args cmap f t = fldValues flds t <*> nuxmvValueT flds args cmap f where
    fldValues :: FieldPath -> ColorSet -> WithApplicative Maybe (Text -> Text)
    fldValues [] colors = case colorSetKeys colors of
        ["otherwise"] -> pure $ (\_ -> nuxmv_false)
        keys -> pure . flip nuxmv_in . enum_type $ map nuxmv_color keys
    fldValues (disj:flds') colors = either (structValues flds') (bvValues flds') =<< WA (lookupKey disj colors)

    structValues :: FieldPath -> Struct -> WithApplicative Maybe (Text -> Text)
    structValues [] _ = WA Nothing
    structValues (struct:flds') structs = either (fldValues flds') (bvValues flds') =<< WA (lookupStructKey struct structs)

    bvValues :: FieldPath -> BitVector -> WithApplicative Maybe (Text -> Text)
    bvValues [] bv = pure $ flip nuxmv_inrange (0, 2^(bvSize bv) - 1)
    bvValues _ _ = WA Nothing

-- | Maps components to the prefixes and postfixes of their field and bitvec variables
type CMap = Map ComponentID (Maybe (Text, Text))
-- | Maps argument numbers to the mfunctiondisj that represent the values of these arguments
type ArgMap = IM.IntMap MFunctionDisj


--sel <= cap -> pos = sel
--sel > cap -> pos = cap
-- | Make a component map for a given queue position
makeArgsAt :: Int -> ColoredNetwork -> CMap
makeArgsAt at net = foldr f Map.empty (getComponentsWithID net) where
    f :: (ComponentID, Component) -> CMap -> CMap
    f (i, (Queue name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_qvar name, nuxmv_array_pos nuxmv_q_end at))
    f (i, (Buffer name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_bvar name, nuxmv_array_pos nuxmv_q_end at))
    f (i, (GuardQueue name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_qvar name, nuxmv_array_pos nuxmv_q_end at))
    f (i, (Source name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_svar name, nuxmv_s_end))
    f (i, (PatientSource name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_svar name, nuxmv_s_end))
    f _ = id
    dead = emptyColorSet . head . outputTypes net

--((nuxmvBufferSizeVar name) > (buffer_oracle name))? (buffer_oracle name) : 0
-- | Make a component map for queue position 0/buffer position = sel
makeArgs :: ColoredNetwork -> CMap
makeArgs net = foldr f Map.empty (getComponentsWithID net) where
    f :: (ComponentID, Component) -> CMap -> CMap
    f (i, (Queue name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_qvar name, nuxmv_array_pos nuxmv_q_end 0))
    f (i, (Buffer name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_bvar name, (txt "v[(") +++ (nuxmvBufferSizeVar name) +++ (txt " > ") +++ (buffer_oracle name) +++ (txt " )? ") +++ (buffer_oracle name) +++ (txt " : 0") +++ (txt "]")))
    f (i, (GuardQueue name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_qvar name, nuxmv_array_pos nuxmv_q_end 0))
    f (i, (Source name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_svar name, nuxmv_s_end))
    f (i, (PatientSource name _)) = Map.insert i (if dead i then Nothing else Just (nuxmv_svar name, nuxmv_s_end))
    f _ = id
    dead = emptyColorSet . head . outputTypes net

-- | Update the state of queues according to the transfers specified by the given islandset
stateUpdate :: ColoredNetwork -> (ComponentID, Component) -> ColorSet -> IslandSet ChannelID -> [Text]
stateUpdate net (n, c@(Queue _ size)) t islands =
    queueSizeUpdate net c ins outs ++
    concatMap (queuePosUpdate net (n, c) t ins outs) [0..size-1] where
        ins :: IslandSet ChannelID
        ins = IM.filter f' islands
        f :: Island ChannelID -> Bool
        f = any ((== n) . (getInitiator net)) . islandChannels
        outs :: IslandSet ChannelID
        outs = IM.filter f islands
        f' :: Island ChannelID -> Bool
        f' = any ((== n) . (getTarget net)) . islandChannels
stateUpdate net (n, c@(Buffer _ size)) t islands =
    bufferSizeUpdate net c ins outs ++
    concatMap (bufferPosUpdate net (n, c) t ins outs) [0..size-1] where
        ins :: IslandSet ChannelID
        ins = IM.filter f' islands
        f :: Island ChannelID -> Bool
        f = any ((== n) . (getInitiator net)) . islandChannels
        outs :: IslandSet ChannelID
        outs = IM.filter f islands
        f' :: Island ChannelID -> Bool
        f' = any ((== n) . (getTarget net)) . islandChannels
stateUpdate net (cID, Automaton{componentName=name,nrOfStates=n}) _cs isles =
    if (n == 1) then [] else
        nuxmv_next (nuxmv_psvar name) [cases] where
    cases = IM.foldr caseIsle (nuxmv_psvar name) tIsles
    caseIsle isle = nuxmv_ite (nuxmvEnabled net isle) (showT nxtState) where
        _idx :: Int
        (AutomatonT{endState=nxtState}, _idx) = lookupM (src 379) cID (islandTransitions isle)
    tIsles = IM.filter (Map.member cID . islandTransitions) isles
stateUpdate net (n, c@(GuardQueue _ size)) t islands =
    queueSizeUpdate net c ins outs ++
    concatMap (queuePosUpdate net (n, c) t ins outs) [0..size-1] where
        ins :: IslandSet ChannelID
        ins = IM.filter (islandHasChannel ib) islands
        outs :: IslandSet ChannelID
        outs = IM.filter (\i -> (islandHasChannel o i) && (not $ islandHasChannel ig i)) islands

        [ib, ig] = getInChannels net n
        [o] = getOutChannels net n
stateUpdate _ _ _ _ = []

-- | Produce init statements for declared variables (if necessary).
varInit :: Component -> ColorSet -> [Text]
varInit c@(Queue _ size) t = catMaybes $ queueSizeInit c : map (queuePosInit c t) [0..size-1]
varInit c@(Buffer _ size) t = catMaybes $ bufferSizeInit c : map (bufferPosInit c t) [0..size-1]
varInit c@(GuardQueue _ size) t = catMaybes $ queueSizeInit c : map (queuePosInit c t) [0..size-1]
varInit (Automaton{componentName=name,nrOfStates=n}) _ = if (n == 1) then [] else [nuxmv_init (nuxmv_psvar name) "0"]
varInit _ _ = []

-- | Produce a nuxmv model according to synchronous semantics
syncModel :: ReachabilityInput -> String
syncModel (ReachabilityInput net defs spec invs) = T.unpack . T.unlines $
       nuxmv_module "main" varDefinitions
    ++ nuxmv_assign assignments
    ++ invariants
    ++ specification where
    varDefinitions = typesVar ++ concatMap (\cID -> varDefinition net cID (head $ outputTypes net cID)) (getComponentIDs net) ++ litVariables
    typesVar = if null types then [] else [nuxmv_constants $ map nuxmv_color types]
    litVariables = Set.toList . Set.fromList $ concatMap (nuxmvLiteralDecl net) (Map.keys defs)
    assignments = varInits ++ queueAssignments
    varInits = concatMap (\(n, c) -> varInit c (head $ outputTypes net n)) (getComponentsWithID net)
    queueAssignments = concatMap (\(n, c) -> stateUpdate net (n,c) (head $ outputTypes net n) islands) (getComponentsWithID net)
    invariants = generateInvariants net invs ++ map (nuxmvLiteralDef net) (Map.assocs defs)
    specification = case spec of
        Nothing -> []
        Just spec' -> ["", nuxmv_invarspec (nuxmvFormula net spec')]

    types = networkTypes net
    islands = transferIslands contextNet
    contextNet = mapOnChannelsWithID getExtendedContext net
    getExtendedContext :: ChannelID -> a -> ChannelID
    getExtendedContext n _ = n

--[nuxmv_bool State (nuxmv_proc_stvar name i) | i <- [0..n-1]]
--a->b = !a or b. (v[0] in d) -> block(o,d)
--bigwedge_{0 <= i <= cap} (bigwedge_{d \in C} not(v[i] in d) or block(o,a))
-- | Translate a literal to nuxmv
nuxmvLiteral :: ColoredNetwork -> Literal -> [Text]
-- TODO(snnw): FIFO queues
nuxmvLiteral net (BlockSource cID) = [nuxmv_block (getName $ getComponent net cID) (fromData Nothing)]
nuxmvLiteral net (BlockBuffer cID) = case getComponent net cID of
                                        (Buffer name size) -> [nuxmv_and (map (\(i,d) -> nuxmv_or [(nuxmv_equals "0" (typeInBuffer i net cID (Buffer name size) (Just d, 1))),(nuxmv_block (channelName . fst . getChannel net $ (head $ getOutChannels net cID)) (fromData (Just (head $ getColors d))))]) ps)] where
                                          [intype] = inputTypes net cID
                                          ts = map (\x -> toColorSet x) (getColors intype)
                                          ps = [(i,j)| i <- [0..(size -1)],j <- ts]
                                        _ -> fatal 330 "expected buffer"
nuxmvLiteral net (BlockAny _ xID Nothing) = [nuxmv_block name (fromData Nothing)] where
    name = channelName . fst . getChannel net $ xID
nuxmvLiteral net (BlockAny _ xID (Just cs)) = if empty cs
    then [nuxmv_block name "_empty"]
    else map (nuxmv_block name . fromData . Just) (getColors cs) where
    name = channelName . fst . getChannel net $ xID
nuxmvLiteral net (IdleAll _ xID Nothing) = [nuxmv_idle name (fromData Nothing)] where
    name = channelName . fst . getChannel net $ xID
nuxmvLiteral net (IdleAll _ xID (Just cs)) = if empty cs
    then [nuxmv_idle name "_empty"]
    else map (nuxmv_idle name . fromData . Just) (getColors cs) where
    name = channelName . fst . getChannel net $ xID
nuxmvLiteral net (Is_Full i) = case getComponent net i of
    (Queue name cap) -> [nuxmv_equals (showT cap) (nuxmvQueueSizeVar name)]
    (Buffer name cap) -> [nuxmv_equals (showT cap) (nuxmvBufferSizeVar name)]
    (GuardQueue name cap) -> [nuxmv_equals (showT cap) (nuxmvQueueSizeVar name)]
    _ -> fatal 330 "expected queue or guardQueue"
nuxmvLiteral net (Is_Not_Full i) = case getComponent net i of
    (Queue name cap) -> [nuxmv_gt (showT cap) (nuxmvQueueSizeVar name)]
    (Buffer name cap) -> [nuxmv_gt (showT cap) (nuxmvBufferSizeVar name)]
    _ -> fatal 330 "expected queue"
nuxmvLiteral net (Any_At_Head i d) = [nuxmv_atmost "1" (typeAtHead net i c (d, 1))] where
    c = getComponent net i
{-nuxmvLiteral net (Any_In_Buffer i d) = case getComponent net i of
    (Buffer name cap) -> [nuxmv_and (map (\n -> typeInBuffer n net i (Buffer name cap) (d,1)) [0..cap-1])]
    _ -> fatal 330 "expected buffer"-}
nuxmvLiteral net (All_Not_At_Head i d) = [nuxmv_equals "0" (typeAtHead net i c (d, 1))] where
    c = getComponent net i
nuxmvLiteral net (ContainsNone i d) = [nuxmv_equals "0" (typeInQ net i c (d, 1))] where
    c = getComponent net i
nuxmvLiteral _ (Select _ _) = [nuxmv_true] -- TODO(snnw) capture the merge arbiter state in nuxmv
nuxmvLiteral _ (MSelect _ _) = [nuxmv_true] -- TODO(snnw) capture the multimatch arbiter state in nuxmv
nuxmvLiteral _ (TSelect _ _ _) = [nuxmv_true] -- TODO(snnw) capture the automaton arbiter state in nuxmv
nuxmvLiteral net (InState cID s) = [nuxmv_equals (nuxmv_psvar name) (showT s)] where
    Automaton{componentName=name} = getComponent net cID
nuxmvLiteral net (IdleState cID s) = [nuxmv_proc_stvar name s] where
    Automaton{componentName=name} = getComponent net cID
nuxmvLiteral net (DeadTrans cID s) = [nuxmv_proc_deadvar name s] where
    Automaton{componentName=name} = getComponent net cID
nuxmvLiteral _ (Sum_Compare _ _ _) = fatal 322 "Sum Compare is not supported in Nuxmv invarspec (invariants only)"
nuxmvLiteral _ _ = error "The literal is not supported"

-- | Declare variables for block and idle literals
nuxmvLiteralDecl :: ColoredNetwork -> Literal -> [Text]
nuxmvLiteralDecl net l@BlockSource{} = map (nuxmv_bool State) (nuxmvLiteral net l)
nuxmvLiteralDecl net l@BlockAny{} = map (nuxmv_bool State) (nuxmvLiteral net l)
nuxmvLiteralDecl net l@IdleAll{} = map (nuxmv_bool State) (nuxmvLiteral net l)
nuxmvLiteralDecl net l@IdleState{} = map (nuxmv_bool State) (nuxmvLiteral net l)
nuxmvLiteralDecl net l@DeadTrans{} = map (nuxmv_bool State) (nuxmvLiteral net l)
nuxmvLiteralDecl _ _ = fatal 318 "only blocks, idles, state idles, and dead transitions are defined"

-- | Produce an invar statement from a literal definition
nuxmvLiteralDef :: ColoredNetwork -> (Literal, Formula) -> Text
nuxmvLiteralDef net (l, f') = nuxmv_invar $ nuxmv_equals (nuxmvFormula net $ Lit l) (nuxmvFormula net f')

-- | Translate a formula to nuxmv
nuxmvFormula :: ColoredNetwork -> Formula -> Text
nuxmvFormula net (NOT f) = nuxmv_negate $ nuxmvFormula net f
nuxmvFormula net (AND fs) = nuxmv_and $ map (nuxmvFormula net) (Set.elems fs)
nuxmvFormula net (OR fs) = nuxmv_or $ map (nuxmvFormula net) (Set.elems fs)
nuxmvFormula _ (T) = nuxmv_true
nuxmvFormula _ (F) = nuxmv_false
nuxmvFormula net (Lit l@BlockSource{}) = head $ nuxmvLiteral net l
nuxmvFormula net (Lit l@BlockAny{}) = nuxmv_or $ nuxmvLiteral net l --using conjunction for block equations
nuxmvFormula net (Lit l@IdleAll{}) = nuxmv_and $ nuxmvLiteral net l
nuxmvFormula net (Lit l) = head $ nuxmvLiteral net l

-- | Translate network invariants to nuxmv
generateInvariants :: ColoredNetwork -> [Invariant Int] -> [Text]
generateInvariants net invs = mapMaybe invToNuxmv invs where
    invToNuxmv :: Invariant Int -> Maybe Text
    invToNuxmv inv = if emptyInvariant inv
        then Nothing
        else case inv of
            Invariant _ _ _ -> Just $ nuxmv_invar $ nuxmv_equals "0" (nuxmv_add $ invariantClauses inv)
            LeqInvariant _ _ _ -> Just $ nuxmv_invar $ nuxmv_atmost (nuxmv_add $ invariantClauses inv) "0"

    invariantClauses inv = case inv of
        Invariant qMap aMap c -> concatMap (uncurry qToNuxmv) (Map.assocs qMap)
                                 ++ concatMap (uncurry aToNuxmv) (Map.assocs aMap)
                                 ++ [showT c | c /= 0]
        LeqInvariant qMap aMap c -> concatMap (uncurry qToNuxmv) (Map.assocs qMap)
                                 ++ concatMap (uncurry aToNuxmv) (Map.assocs aMap)
                                 ++ [showT c | c /= 0]
    qToNuxmv :: ComponentID -> Map (Maybe Color) Int -> [Text]
    qToNuxmv cID = map (typeInQ net cID $ getComponent net cID) . Map.assocs
    aToNuxmv :: ComponentID -> Map Int Int -> [Text]
    aToNuxmv cID = map inState . Map.assocs where
        inState (s, k) = nuxmv_mult [showT k, nuxmv_toint $ nuxmv_equals (showT s) (nuxmv_psvar name)]
        Automaton{componentName=name} = getComponent net cID
    -- fatal 398 "unimplemented" --todo(tssb, snnw) (0) implement automaton invariant in nuxmv

-- | Calculate the number of packets of the given type at the head of the queue (i.e. 0 or 1),
-- and the total number of packets of the given type in the queue, respectively.
typeAtHead, typeInQ :: IsColorSet a => ColoredNetwork -> ComponentID -> Component -> (Maybe a, Int) -> Text
typeAtHead = typeAtPosition (\_ -> [0])
typeInQ = typeAtPosition (\c -> [0..(capacity c)-1])
--nuxmvLiteral net (ContainsNone cid d) = [nuxmv_equals "0" (typeInQ net cid c (d, 1))] where
--    c = getComponent net cid

typeInBuffer :: IsColorSet a => Int -> ColoredNetwork -> ComponentID -> Component -> (Maybe a, Int) -> Text
typeInBuffer n = typeAtPosition (\_ -> [n])

-- | Calculates the total number of packets of the given type at the given position in the queue
typeAtPosition :: IsColorSet a => (Component -> [Int]) -> ColoredNetwork -> ComponentID -> Component -> (Maybe a, Int) -> Text
typeAtPosition r net q c@Queue{} (Just t, mult) = nuxmv_mult [showT mult, nuxmv_count (map (isType net q t) (r c))]
typeAtPosition r net q c@Buffer{} (Just t, mult) = nuxmv_mult [showT mult, nuxmv_count (map (isTypeB net q t) (r c))]
typeAtPosition r net q c@GuardQueue{} (Just t, mult) = nuxmv_mult [showT mult, nuxmv_count (map (isType net q t) (r c))]
typeAtPosition _ _ _ (Queue name _) (Nothing, mult) = nuxmv_mult [showT mult, nuxmvQueueSizeVar name]
typeAtPosition _ _ _ (Buffer name _) (Nothing, mult) = nuxmv_mult [showT mult, nuxmvBufferSizeVar name]
typeAtPosition _ _ _ (GuardQueue name _) (Nothing, mult) = nuxmv_mult [showT mult, nuxmvQueueSizeVar name]
typeAtPosition _ _ _ _ _ = fatal 276 "invariant on a component that is not a queue"

-- | Check if the packet at the given position of the queue is of the given type
isType :: IsColorSet a => ColoredNetwork -> ComponentID -> a -> Int -> Text
isType net q t i = nuxmv_and $ (nuxmv_gt (nuxmvQueueSizeVar name) (showT i)):(matchesTypeAt i net (XInput q, t)) where
    name = getName $ getComponent net q


-- | Check if the packet at the given position of the buffer is of the given type
isTypeB :: IsColorSet a => ColoredNetwork -> ComponentID -> a -> Int -> Text
isTypeB net q t i = nuxmv_and $ (nuxmv_gt (nuxmvBufferSizeVar name) (showT i)):(matchesTypeAt i net (XInput q, t)) where
    name = getName $ getComponent net q

--toNuxmvAsync :: Network -> Text
--toNuxmvAsync net = undefined where
--    typedNet :: ColoredNetwork
--    typedNet = channelTypes $ unfoldMacros net
--    varDefinitions = undefined
--    transitionConditions = undefined
--    assignments = undefined
--    invariants = ""
--    specification = ""

-- | Reachability analysis is performed using either abc or nuXmv
data ReachabilityEngine = ABC AbcEngine | NUXMV NuxmvEngine deriving (Eq)
-- | The implemented settings for abc
data AbcEngine = PDR | BMC deriving (Eq)
-- | The implemented settings for nuxmv
data NuxmvEngine = BDD | FWD | BWD | FWDBWD | BDDBMC Int | BMCINC Int | IC3 | IC3M deriving (Eq)

-- | Check whether the given engine is an abc engine
isAbcEngine :: ReachabilityEngine -> Bool
isAbcEngine ABC{} = True
isAbcEngine NUXMV{} = False

-- | Options for reachability analysis
data ReachabilityOptions = ReachabilityOptions {
    keepAigerModel :: Bool, -- ^ Specifies whether the produced aiger model should be removed after reachability analysis
    keepNuxmvModel :: Int , -- ^ Specifies the generation mode for the generated nuXmv model.
    reachabilityEngine :: ReachabilityEngine -- ^ Specifies the engine to be used
}

-- | Input to perform reachability analysis on
data ReachabilityInput = ReachabilityInput {
    inputNetwork :: ColoredNetwork, -- ^ The network
    inputLiterals :: Map Literal Formula, -- ^ A map of block/idle literals and their corresponding formula
    inputSpec :: Maybe Formula, -- ^ The formula that should be evaluated
    inputInvariants :: [Invariant Int] -- ^ Invariants of the network
}

-- | Execute a process on a temporary file with the given contents
executeProcess :: String -> String -> String -> IO()
executeProcess process contents handle = withTempFile "." "script.nu" $ \f h -> do
    hPutStrLn h contents
    () <- hClose h
    callProcess "/bin/sh" ["-c", unwords[process, f, "2>/dev/null", handle]]

-- | Call the given engine. Assumes that the file model.nuxmv contains the nuxmv model
callEngine :: ReachabilityEngine -> IO ()
callEngine engine = do
    path <- getEnv "MWB_PATH_NUXMV"
    let abcContents abcEngine = case abcEngine of
            PDR -> "pdr\nquit"
            BMC     -> "bmc3 -v\nquit"
    let nuxmvContents nuxmvEngine = case nuxmvEngine of
            BDD          -> "go\ncheck_invar\nprint_usage\nquit\n"
            FWD          -> "go\ncheck_invar -s forward\nprint_usage\nquit\n"
            BWD          -> "go\ncheck_invar -s backward\nprint_usage\nquit\n"
            FWDBWD       -> "go\ncheck_invar -s forward-backward\nprint_usage\nquit\n"
            BDDBMC depth -> "go\nbuild_boolean_model\nbmc_setup\ncheck_invar -s bdd-bmc -k " ++show depth ++"\nprint_usage\nquit\n"
            BMCINC depth -> "go_bmc\ncheck_invar_bmc_inc -s forward -k "++show depth ++"\nshow_traces -p 4 -o trace.xml\nquit"
            IC3          -> "flatten_hierarchy\nencode_variables\nbuild_boolean_model\ncheck_invar_ic3 -v 1 -a 1 -g\nprint_usage\nquit\n"
            IC3M         -> "go_msat\ncheck_invar_ic3 -i\nprint_usage\nquit\n"
    let contents = case engine of
            NUXMV nuxmvEngine -> "read_model -i model.nuxmv\n" ++ nuxmvContents nuxmvEngine
            ABC abcEngine     -> "read model_invar_0.aig\nfraig\n" ++ abcContents abcEngine

    let process = case engine of
            ABC{} -> "/usr/local/bin/abc -f"
            NUXMV{} -> path++"/nuxmv -source"
    let writeAiger = "read_model -i model.nuxmv\nflatten_hierarchy\nencode_variables\nbuild_boolean_model\nwrite_aiger_model -p model -b\nquit\n"
    when (isAbcEngine engine) $ executeProcess (path++"/nuxmv -source") writeAiger ""
    {-# SCC "ExecuteReachability" #-} executeProcess process contents " | tee result.txt 1>&2"

-- | Write the nuxmv model to the file model.nuxmv
writeModel :: ReachabilityInput -> IO()
writeModel input = do
    writeFile "model.nuxmv" (syncModel input)

-- | Reachability or deadlock check
hasDeadlock :: ReachabilityOptions -> ReachabilityInput -> IO (Either String Bool)
hasDeadlock opts input = do
    writeModel input
    {-# SCC "Reachability" #-} callEngine (reachabilityEngine opts)
    output <- readFile "result.txt"
    when (not (keepAigerModel opts) && (isAbcEngine $ reachabilityEngine opts)) $ removeFile "model_invar_0.aig"
    when ((keepNuxmvModel opts) == 0) $ removeFile "model.nuxmv"
    removeFile "result.txt"
    let true = case reachabilityEngine opts of
            ABC{} -> "Property proved"
            NUXMV{} -> "-- invariant .* is true"
    let false = case reachabilityEngine opts of
            ABC{} -> "Output 0 of miter"
            NUXMV{} -> "-- invariant .* is false"
    return $
        if (output =~ (true::String) :: Bool) then Right False
        else if (output =~ (false::String) :: Bool) then Right True
        else Left output

-- | Helper function to filter cases of which both sides are defined
mapMaybeCase :: (a -> (WithApplicative Maybe b, WithApplicative Maybe b)) -> [a] -> [(WithApplicative Maybe b, WithApplicative Maybe b)]
mapMaybeCase f = filter (\(WA a, WA b) -> isJust a && isJust b) . map f

-- | Helper function to filter cases of which both sides are defined
maybeCase :: (WithApplicative Maybe b, WithApplicative Maybe b) -> Maybe (b, b)
maybeCase (WA (Just x), WA (Just y)) = Just (x, y)
maybeCase _ = Nothing

-- Variable names --
-- queues and sources:
nuxmvQueueVar :: Text -> FieldPath -> Text
nuxmvQueueVar name flds = nuxmv_qvar . T.intercalate "_" $ name : flds ++ [nuxmv_q_end]

nuxmvQueueSizeVar :: Text -> Text
nuxmvQueueSizeVar = nuxmv_qsvar

nuxmvBufferVar :: Text -> FieldPath -> Text
nuxmvBufferVar name flds = nuxmv_bvar . T.intercalate "_" $ name : flds ++ [nuxmv_q_end]

nuxmvBufferSizeVar :: Text -> Text
nuxmvBufferSizeVar = nuxmv_bsvar

nuxmvSourceVar :: Text -> FieldPath -> Text
nuxmvSourceVar name flds = nuxmv_svar . T.intercalate "_" $ name : flds ++ [nuxmv_s_end]

nuxmv_qvar, nuxmv_qsvar, nuxmv_bvar, nuxmv_bsvar, nuxmv_svar, nuxmv_psvar :: (IsString a, Monoid a) => a -> a
nuxmv_qvar = ("Q_" <>)
nuxmv_qsvar = ("Qs_" <>)
nuxmv_bvar = ("B_" <>)
nuxmv_bsvar = ("Bs_" <>)
nuxmv_svar = ("S_" <>)
nuxmv_psvar = ("P_" <>)

nuxmv_ptvar :: (IsString a, Monoid a) => a -> a
nuxmv_ptvar = ("Pt_" <>)

nuxmv_proc_stvar :: Text -> Int -> Text
nuxmv_proc_stvar t n = T.intercalate "_" [txt "StIdle",t,showT n]

nuxmv_proc_deadvar :: Text -> Int -> Text
nuxmv_proc_deadvar t n = T.intercalate "_" [txt "DeadTrans",t,showT n]

nuxmv_q_end, nuxmv_s_end :: IsString a => a
nuxmv_q_end = "v"
nuxmv_s_end = "i"

-- oracles:
source_oracle, sink_oracle, merge_oracle, buffer_oracle, loadbalancer_oracle, mmatch_m_oracle, mmatch_d_oracle :: (IsString a, Monoid a) => a  -> a
source_oracle = ("oracle_S_" <>)
sink_oracle = ("oracle_Z_" <>)
merge_oracle = ("oracle_M_" <>)
buffer_oracle = ("oracle_B_" <>)
loadbalancer_oracle = ("Oracle_L_" <>)
mmatch_m_oracle = ("oracle_MM_m_" <>)
mmatch_d_oracle = ("oracle_MM_d_" <>)

-- literals:
nuxmv_idle, nuxmv_block :: (IsString a, Monoid a) => a -> a -> a
nuxmv_idle = nuxmv_literal "idle_"
nuxmv_block = nuxmv_literal "block_"

nuxmv_literal :: Monoid a => a -> a -> a -> a
nuxmv_literal lit name d = lit <> name <> d

-- data:
fromData :: Maybe Color -> Text
fromData Nothing = ""
fromData (Just color) = "_" +++colorKey color +++ either fromVStruct fromVal (colorContent color) where
    fromVStruct vstruct = if emptyVStruct vstruct then "" else "_C_" +++ T.intercalate "_X_" (fromStruct vstruct) +++ "_P"
    fromStruct = map (\(fld,v') -> fld +++ either fromColor fromVal v') . Hash.assocs . vstructValue
    fromColor c = "_E_" +++ fromData (Just c)
    fromVal :: Value -> Text
    fromVal = showT . valValue

nuxmv_color :: (IsString a, Monoid a) => a -> a
nuxmv_color = ("val_" <>)
