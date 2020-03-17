{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

{-|
Module      : Madl.Deadlock.SMT
Description : SMT model generation.
Copyright   : (c) Freek Verbeek, Sanne Wouda 2015-2016, Tessa Belder 2016

This module generates an SMT model from a colored network. It also contains a parser for SMT output.
-}
module Madl.Deadlock.SMT (
    export_formula_to_SMT, parseSMTOutput,
    export_invariants_to_smt, export_bi_var_to_smt,
    export_literal_to_SMT, SMTModel,
    bi_to_name, showModel
) where

import Data.Foldable (toList)
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes, mapMaybe)

import Utils.Map
import Utils.SMTCode
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes
import Madl.Invariants
import Madl.Network

import Text.Parsec
import Text.Parsec.String

import Madl.Deadlock.Formulas

-- Error function
fileName :: Text
fileName = "SMT"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-- EXPORTING TO SMT
-- | Export an integer to SMT
export_value_to_smt :: Int -> String
export_value_to_smt v = if v > 0 then show v else smt_un_operator "-" (show (-v))

-- | Export the number of packets in the given queue to SMT, multiplied by the given factor
export_q_to_smt :: ColoredNetwork -> (ComponentID, Int) -> String
export_q_to_smt x (q, v) = smt_mult (export_value_to_smt v) (smt_queue x q)

-- | Export the number of packets of the given color in the given queue to SMT, multiplied by the given factor
export_q_color_to_smt :: ColoredNetwork -> (Color -> String) -> ((ComponentID, Maybe Color), Int) -> String
export_q_color_to_smt x show_p_t ((q, d), v) = case d of
    Nothing -> export_q_to_smt x (q, v)
    Just d' -> export_q_data_to_smt x show_p_t ((q, d'), v)

-- | Export the number of packet of all given colors in the given queue to SMT, multiplied by the given factor
export_q_colorset_to_smt :: ColoredNetwork -> (Color -> String) -> ((ComponentID, Maybe ColorSet), Int) -> String
export_q_colorset_to_smt x show_p_t ((q, cs), v) = case cs of
    Nothing -> export_q_to_smt x (q, v)
    Just cs' -> if empty cs' then "0" else smt_add $ map (\c -> export_q_data_to_smt x show_p_t ((q, c), v)) (getColors cs')

-- | Export the number of packets of the given color in the given queue to SMT, multiplied by the given factor
export_q_data_to_smt :: ColoredNetwork -> (Color -> String) -> ((ComponentID, Color), Int) -> String
export_q_data_to_smt x show_p_t ((q, d), v) = smt_mult (export_value_to_smt v) (smt_queue_packet x q d show_p_t)

-- | Export the number of packet of all given colors in the given queue to SMT, multiplied by the given factors
export_q_factor_to_smt :: ColoredNetwork -> (Color -> String) -> ComponentID -> Map (Maybe Color) Int -> [String]
export_q_factor_to_smt x show_p_t i inv = toList $ Map.mapWithKey factor inv where
    factor Nothing v = export_q_to_smt x (i,v)
    factor (Just d) v = export_q_data_to_smt x show_p_t ((i, d), v)

-- | Export the automaton state to SMT, multiplied by the given factors
export_a_factor_to_smt :: ColoredNetwork -> ComponentID -> Map Int Int -> [String]
export_a_factor_to_smt x i inv = toList $ Map.mapWithKey factor inv where
    factor v f = smt_mult (export_value_to_smt f) . smt_bool_to_int $ smt_equals (export_value_to_smt v) (smt_automaton_state x i)

-- | Export an invariant to smt
export_row_to_smt :: ColoredNetwork -> (Color -> String) -> Invariant Int -> String
export_row_to_smt x show_p_t inv = if emptyInvariant inv then "" else case inv of
    Invariant qMap aMap c -> smt_assert $ smt_equals "0" invar where
        invar = smt_add $ concatMap invarQ (Map.assocs qMap) ++ concatMap invarA (Map.assocs aMap) ++ [export_value_to_smt c | c /= 0]
    LeqInvariant qMap aMap c -> smt_assert $ smt_atmost invar "0" where
        invar = smt_add $ concatMap invarQ (Map.assocs qMap) ++ concatMap invarA (Map.assocs aMap) ++ [export_value_to_smt c | c /= 0]
    where
        invarQ = uncurry $ export_q_factor_to_smt x show_p_t
        invarA = uncurry $ export_a_factor_to_smt x

-- | Declare a variable for the number of packets of the given color in the given queue
export_q_data_var_to_smt :: ColoredNetwork -> (Color -> String) -> (ComponentID, Color) -> String
export_q_data_var_to_smt x show_p_t (i,d) = case getComponent x i of
    Queue{}  -> unwords [smt_fun "Int" name, smt_assert (smt_atleast name "0")]
    Buffer{}  -> unwords [smt_fun "Int" name, smt_assert (smt_atleast name "0")]
    GuardQueue{}  -> unwords [smt_fun "Int" name, smt_assert (smt_atleast name "0")]
    _ -> fatal 84 "unreachable"
    where
        name = smt_queue_packet x i d show_p_t

-- | Declare arbiter and size variable(s) for the given component
export_q_var_to_smt :: ColoredNetwork -> ComponentID -> String
export_q_var_to_smt x i = case getComponent x i of
    Queue _ cap -> unwords[smt_fun "Int" name, smt_assert_inrange name (0, cap)] where
        name = smt_queue x i
    Buffer _ cap -> unlines[
                    unwords[smt_fun "Int" name, smt_assert_inrange name (0, cap)],
                    unwords[smt_fun "Int" name, smt_assert_inrange name_a (0, cap - 1)]] where
        name = smt_buffer x i
        name_a = smt_buffer_arbiter x i
    Merge{} -> unwords[smt_fun "Int" name, smt_assert_inrange name (0, getNrInputs x i - 1)] where
        name = smt_merge_arbiter x i
    MultiMatch{} -> unlines[
        unwords[smt_fun "Int" name_m, smt_assert_inrange name_m (0, length matchIns - 1)],
        unwords[smt_fun "Int" name_d, smt_assert_inrange name_d (0, length dataIns - 1)]] where
            name_m = smt_match_arbiter_m x i
            name_d = smt_match_arbiter_d x i
            (matchIns, dataIns) = splitAt (getNrOutputs x i) (getInChannels x i)
    Automaton _ nrIns _ n ts _ -> unlines[
        unwords[smt_fun "Int" name_s, smt_assert_inrange name_s (0, n-1)],
        unwords[smt_fun "Int" name_c, smt_assert_inrange name_c (0, nrIns-1)],
        unwords[smt_fun "Int" name_t, smt_assert_inrange name_t (0, length ts-1)]] where
            name_s = smt_automaton_state x i
            name_c = smt_automaton_arbiter_c x i
            name_t = smt_automaton_arbiter_t x i
    LoadBalancer{} -> unwords[smt_fun "Int" name, smt_assert_inrange name (0, getNrOutputs x i - 1)] where
        name = smt_loadbalancer_arbiter x i
    GuardQueue _ cap -> unlines[
        unwords[smt_fun "Int" name_q, smt_assert_inrange name_q (0, cap)],
        unwords[smt_fun "Int" name_m, smt_assert_inrange name_m (0, getNrInputs x i - 1)]] where
            name_q = smt_guardqueue_q x i
            name_m = smt_guardqueue_m x i
    _ -> fatal 91 "unreachable"

-- | Get the name(s) of the variable(s) representing the given literal
bi_to_name :: ColoredNetwork -> (Color -> String) -> Literal -> [String]
bi_to_name x _show_p_t (BlockSource cID) = [smt_block_source x cID]
bi_to_name x _show_p_t (BlockAny _ xID Nothing) = [smt_block x xID]
bi_to_name x show_p_t (BlockAny _ xID (Just cs)) = if empty cs
    -- JS: why do we generate a variable with an empty set of colours?
    then [smt_block x xID ++ ".empty"]
    else map (\c -> smt_block x xID ++ "." ++ show_p_t c) (getColors cs)
bi_to_name x _show_p_t (IdleAll _ xID Nothing) = [smt_idle x xID]
bi_to_name x show_p_t (IdleAll _ xID (Just cs)) = if empty cs
    then [smt_idle x xID ++ ".empty"]
    else map (\c -> smt_idle x xID ++ "." ++ show_p_t c) (getColors cs)
bi_to_name x _ (IdleState cID p) = [smt_idle_state x cID p]
bi_to_name x _ (DeadTrans cID n) = [smt_dead_trans x cID n]
bi_to_name _ _ _ = fatal 111 "unreachable"

-- | Declare variable(s) to represent the given literal
export_bi_var_to_smt :: ColoredNetwork -> (Color -> String) -> [Literal] -> String
export_bi_var_to_smt x show_p_t lits = intercalate "\n" $ map (\s -> smt_fun "Bool" s) litnames where
    litnames = Set.toList . Set.fromList $ concatMap (bi_to_name x show_p_t) lits

-- | Declare a queue nr of packets invariant
-- Given a queue `q` that can contain packets of all types in `C`, then:
--  `#q = sum_(c in C) #q(c)`, or `#q = 0` if `C` is empty
export_color_info_to_smt :: ColoredNetwork -> (Color -> String) -> ComponentID -> String
export_color_info_to_smt x show_p_t i =
    let ds = getColors . head $ inputTypes x i
        name = smt_queue x i
        dataName = ((name ++ ".") ++) . show_p_t
    in case ds of
        [] -> smt_assert $ smt_equals name "0"
        _ ->  smt_assert . smt_equals name $ smt_add (map dataName ds)

-- | Export the invariants to SMT
-- Assemble all variables in two sets (one for variables q0.d, others for variables q0).
-- Examine the first set to find out which queues are color specific, i.e., have invariants over them with q0.d variables.
-- For those queues, the color derivation is exported to SMT as well.
export_invariants_to_smt :: ColoredNetwork -> (Color -> String) -> [Invariant Int] -> (String, Set ComponentID, (Map ComponentID [Color], Set ComponentID))
-- TODO(snnw) should be ... -> (String, Set ComponentID, (Set (ComponentID, Color), Set ComponentID))
export_invariants_to_smt net show_p_t invs =
    let
        vars :: (Set (ComponentID, Color), Set ComponentID)
        vars  = get_variables_in_invariants invs;
        qs :: Set ComponentID;
        qs    = get_color_specific_queues (fst vars);
        vars' :: (Set (ComponentID, Color), Set ComponentID);
        vars' = add_queues_and_colors vars qs;
        s     = unlines (map (export_q_var_to_smt net) $ Set.toList (snd vars'))
             ++ unlines (map (export_q_data_var_to_smt net show_p_t) $ Set.toList (fst vars'))
             ++ "\n\n"
             ++ unlines (map (export_color_info_to_smt net show_p_t) $ Set.toList qs)
             ++ "\n\n"
             ++ unlines (map (export_row_to_smt net show_p_t) invs)
        vars'' :: (Map ComponentID [Color], Set ComponentID)
        vars'' = mapFst (Map.fromListWith (++) . map (mapSnd (:[])) . Set.toList) vars'
    in (s, qs, vars'')
    where
        get_variables_in_invariants :: [Invariant Int] -> (Set (ComponentID, Color), Set ComponentID);
        get_variables_in_invariants = foldr f (Set.empty,Set.empty);
        f :: Invariant Int -> (Set (ComponentID, Color), Set ComponentID) -> (Set (ComponentID, Color), Set ComponentID);
        f row = mapFst (addKeysWithValue row) . mapSnd (addKeysWithoutValue row);

        addKeysWithValue :: Invariant Int -> Set (ComponentID, Color) -> Set (ComponentID, Color);
        addKeysWithValue invar = Set.union $ keysTypes invar;
        keysTypes :: Invariant Int -> Set (ComponentID, Color);
        keysTypes (Invariant qMap _aMap _c) = Set.fromList . concatMap g $ Map.assocs qMap;
        keysTypes (LeqInvariant qMap _aMap _c) = Set.fromList . concatMap g $ Map.assocs qMap;
        g :: (ComponentID, Map (Maybe Color) Int) -> [(ComponentID, Color)];
        g (i, ts) = zip (repeat i) (catMaybes $ Map.keys ts)

        addKeysWithoutValue :: Invariant Int -> Set ComponentID -> Set ComponentID;
        addKeysWithoutValue (Invariant qMap aMap _c) = Set.union $ Set.union qKeys aKeys where
            qKeys = Map.keysSet $ Map.filter (Map.member Nothing) qMap
            aKeys = Map.keysSet aMap
        addKeysWithoutValue (LeqInvariant qMap aMap _c) = Set.union $ Set.union qKeys aKeys where
            qKeys = Map.keysSet $ Map.filter (Map.member Nothing) qMap
            aKeys = Map.keysSet aMap

        get_color_specific_queues :: Set (ComponentID, Color) -> Set ComponentID;
        get_color_specific_queues vars = Set.map fst vars;
        add_queues_and_colors :: (Set (ComponentID, Color), Set ComponentID) -> Set ComponentID -> (Set (ComponentID, Color), Set ComponentID);
        add_queues_and_colors = Set.foldr h;
        h :: ComponentID -> (Set (ComponentID, Color), Set ComponentID) -> (Set (ComponentID, Color), Set ComponentID);
        h = (\q vars ->
            (Set.union (Set.fromList (map (\color -> (q,color)) (toList (
                head $ map (getColors . snd . getChannel net) (getOutChannels net q)
            )))) (fst vars), Set.insert q (snd vars)))

-- | Declare the value of the given literal in SMT
export_literal_to_SMT :: ColoredNetwork -> (Color -> String) -> Literal -> String
export_literal_to_SMT x _show_p_t (Is_Full q) = case getComponent x q of
                                                Queue _ cap  -> smt_equals (export_value_to_smt cap) (export_q_to_smt x (q,1))
                                                Buffer _ cap  -> smt_equals (export_value_to_smt cap) (export_q_to_smt x (q,1))
                                                GuardQueue _ cap -> smt_equals (export_value_to_smt cap) (export_q_to_smt x (q,1))
                                                _ -> fatal 166 "Is_Full literal is only defined for queues."
export_literal_to_SMT x _show_p_t (Is_Not_Full q) = case getComponent x q of
                                                Queue _ cap  -> smt_bin_operator ">" (export_value_to_smt cap) (export_q_to_smt x (q,1))
                                                Buffer _ cap  -> smt_bin_operator ">" (export_value_to_smt cap) (export_q_to_smt x (q,1))
                                                _ -> fatal 169 "Is_Not_Full literal is only defined for queues."
export_literal_to_SMT x show_p_t (Any_At_Head q cs) = smt_atleast nr_of_packets "1" where
    nr_of_packets = export_q_colorset_to_smt x show_p_t ((q, cs), 1)
export_literal_to_SMT x show_p_t (Any_In_Buffer q cs) = smt_atleast nr_of_packets "1" where
    nr_of_packets = export_q_colorset_to_smt x show_p_t ((q, cs), 1)
export_literal_to_SMT x show_p_t (All_Not_At_Head q cs) = smt_equals nr_of_packets "0" where
    nr_of_packets = export_q_colorset_to_smt x show_p_t ((q, cs), 1)
export_literal_to_SMT x show_p_t (ContainsNone q cs) = smt_equals nr_of_packets "0" where
    nr_of_packets = export_q_colorset_to_smt x show_p_t ((q, cs), 1)
export_literal_to_SMT x show_p_t (Sum_Compare qs cmp n) = smt_bin_operator cmp (smt_add $ map qvar qs) (export_value_to_smt n) where
    qvar (q, d) = export_q_color_to_smt x show_p_t ((q, d), 1)
export_literal_to_SMT x _show_p_t (Select i v)  = smt_equals (export_value_to_smt v) (smt_merge_arbiter x i)
export_literal_to_SMT x _show_p_t (MSelect i (m, d))  = smt_and [match_selected, data_selected] where
    match_selected = smt_equals (export_value_to_smt m) (smt_match_arbiter_m x i)
    data_selected = smt_equals (export_value_to_smt $ d - getNrOutputs x i) (smt_match_arbiter_d x i)
export_literal_to_SMT x _show_p_t (TSelect i c t)  = smt_and[chan_selected, trans_selected] where
    chan_selected = smt_equals (export_value_to_smt c) (smt_automaton_arbiter_c x i)
    trans_selected = smt_equals (export_value_to_smt t) (smt_automaton_arbiter_t x i)
export_literal_to_SMT x _show_p_t (InState i v)  = smt_equals (export_value_to_smt v) (smt_automaton_state x i)
export_literal_to_SMT x _ (IdleState cID p) = smt_idle_state x cID p
export_literal_to_SMT x _ (DeadTrans cID n) = smt_dead_trans x cID n
export_literal_to_SMT x _ (BlockBuffer cID) = case getComponent x cID of
                                                Buffer _ cap  -> smt_equals (export_value_to_smt cap) (export_q_to_smt x (cID,1))
                                                _ -> fatal 166 "buffer expected"
export_literal_to_SMT x show_p_t (lit@BlockSource{}) = head $ bi_to_name x show_p_t lit
export_literal_to_SMT x show_p_t (lit@BlockAny{}) = smt_or $ bi_to_name x show_p_t lit  --using conjunction for block equations
export_literal_to_SMT x show_p_t (lit@IdleAll{})  = smt_and $ bi_to_name x show_p_t lit

-- | Declare a formula in SMT
export_formula_to_SMT :: ColoredNetwork -> (Set ComponentID) -> (Map ComponentID [Color], Set ComponentID) -> (Color -> String) -> Maybe Literal -> Formula -> (String, Set ComponentID, (Map ComponentID [Color], Set ComponentID))
export_formula_to_SMT x qs vars show_p_t bi f = (ret_s,ret_qs,ret_vars) where
    (s,vars',qs') = export_formula_to_SMT_rec $ simplify_singletons f;
    vars'' = Set.difference vars' qs';

    ret_vars = (Map.union (fst vars) (colors_from qs'), Set.union (snd vars) $ Set.union vars' qs');
    ret_qs   = Set.union qs qs';
    ret_s = (Set.fold (++) "" (Set.map (\v -> export_q_var_to_smt x v ++ "\n") vars''))
        ++
        (Set.fold (++) "" (Set.map (\v -> export_q_var_to_smt x v ++ "\n") (Set.difference qs' (snd vars))))
        ++
        (concatMap (\(q, cs) -> concatMap (\c -> export_q_data_var_to_smt x show_p_t (q, c) ++ "\n") cs) (Map.assocs $ Map.difference (colors_from qs') (fst vars)))
        ++
        (Set.fold (++) "" (Set.map (\q -> export_color_info_to_smt x show_p_t q ++ "\n") qs'))
        ++ "\n" ++
        (case bi of
            Nothing -> smt_assert s
            Just bi' -> smt_assert $ smt_equals (export_literal_to_SMT x show_p_t bi') s
        )
        ++ "\n"

    export_formula_to_SMT_rec :: Formula -> (String, Set ComponentID, Set ComponentID)
    export_formula_to_SMT_rec T = ("true",Set.empty,Set.empty)
    export_formula_to_SMT_rec F = ("false",Set.empty, Set.empty)
    export_formula_to_SMT_rec (Lit l) = (export_literal_to_SMT x show_p_t l, fst (new_vars l), snd (new_vars l))
    export_formula_to_SMT_rec (NOT f') = let (s',v,q) = export_formula_to_SMT_rec f' in
                                            (smt_un_operator "not" s', v, q)
    export_formula_to_SMT_rec (AND fs) = let (s',v,q) = unzip3 $ toList $ Set.map export_formula_to_SMT_rec fs in
                                            (smt_and s', foldl Set.union Set.empty v, foldl Set.union Set.empty q)
    export_formula_to_SMT_rec (OR fs)  = let (s',v,q) = unzip3 $ toList $ Set.map export_formula_to_SMT_rec fs in
                                            (smt_or s', foldl Set.union Set.empty v, foldl Set.union Set.empty q)
    -- Returns a tuple (qs0,qs1) with qs0 new queue variables and qs1 new color-specific queue variables
    new_vars :: Literal -> (Set ComponentID, Set ComponentID)
    new_vars l = case l of
                Select i _ -> (if i `Set.notMember` (snd vars) then Set.singleton i else Set.empty, Set.empty)
                MSelect i _ -> (if i `Set.notMember` (snd vars) then Set.singleton i else Set.empty, Set.empty)
                TSelect i _ _ -> (if i `Set.notMember` (snd vars) then Set.singleton i else Set.empty, Set.empty)
                InState i _ -> (if i `Set.notMember` (snd vars) then Set.singleton i else Set.empty, Set.empty)
                IdleState i _ -> (if i `Set.notMember` (snd vars) then Set.singleton i else Set.empty, Set.empty)
                DeadTrans i _ -> (if i `Set.notMember` (snd vars) then Set.singleton i else Set.empty, Set.empty)
                Is_Full q -> (if q `Set.notMember` (snd vars) then Set.singleton q else Set.empty, Set.empty)
                Is_Not_Full q -> (if q `Set.notMember` (snd vars) then Set.singleton q else Set.empty, Set.empty)
                ContainsNone q Nothing -> (if q `Set.notMember` (snd vars) then Set.singleton q else Set.empty, Set.empty)
                ContainsNone q (Just _) -> (Set.empty, if q `Map.notMember` (fst vars) then Set.singleton q else Set.empty)
                Any_At_Head q Nothing -> (if q `Set.notMember` (snd vars) then Set.singleton q else Set.empty, Set.empty)
                Any_At_Head q (Just _) -> (Set.empty, if q `Map.notMember` (fst vars) then Set.singleton q else Set.empty)
                Any_In_Buffer b Nothing -> (if b `Set.notMember` (snd vars) then Set.singleton b else Set.empty, Set.empty)
                Any_In_Buffer b (Just _) -> (Set.empty, if b `Map.notMember` (fst vars) then Set.singleton b else Set.empty)
                All_Not_At_Head q Nothing -> (if q `Set.notMember` (snd vars) then Set.singleton q else Set.empty, Set.empty)
                All_Not_At_Head q (Just _) -> (Set.empty, if q `Map.notMember` (fst vars) then Set.singleton q else Set.empty)
                Sum_Compare qs'' _cmp _v -> foldr (\(q,d) (l',r) -> case d of
                                                                Nothing -> (if q `Set.notMember` (snd vars) then Set.insert q l' else l',r)
                                                                Just _  -> if q `Map.notMember` (fst vars) then (l', Set.insert q r) else (l',r))
                                         (Set.empty, Set.empty) qs''
                BlockSource{} -> (Set.empty, Set.empty)
                BlockBuffer{} -> (Set.empty, Set.empty)
                BlockAny{} -> (Set.empty, Set.empty)
                IdleAll{} -> (Set.empty, Set.empty)
    colors_from :: Set ComponentID -> Map ComponentID [Color]
    colors_from = Map.unions . map (\q -> Map.singleton q (getColors . head $ inputTypes x q)) . Set.toList

-- Constants:
smt_block, smt_idle :: ColoredNetwork -> ChannelID -> String
smt_block net xID = "block_" ++ utxt (channelName . fst . getChannel net $ xID)
smt_idle net xID = "idle_" ++ utxt (channelName . fst . getChannel net $ xID)
smt_block_source :: ColoredNetwork -> ComponentID -> String
smt_block_source net cID = "block_src_" ++ utxt (getName $ getComponent net cID)

smt_idle_state :: ColoredNetwork -> ComponentID -> Int -> String
smt_idle_state net cID p = "idle_state_" ++ show p ++ "_" ++ utxt (getName $ getComponent net cID)

smt_dead_trans :: ColoredNetwork -> ComponentID -> Int -> String
smt_dead_trans net cID n = "dead_trans_" ++ show n ++ "_" ++ utxt (getName $ getComponent net cID)

smt_queue :: ColoredNetwork -> ComponentID -> String
smt_queue x i = case getComponent x i of
                  (Queue _ _) -> "Q___" ++ (utxt . getName $ getComponent x i)
                  (Buffer _ _) -> "B___" ++ (utxt . getName $ getComponent x i) ++ "_state"
                  _ -> error "smt_queue: either queue or buffer expected"

smt_buffer, smt_buffer_arbiter, smt_loadbalancer_arbiter, smt_merge_arbiter, smt_match_arbiter_m, smt_match_arbiter_d, smt_guardqueue_q, smt_guardqueue_m :: ColoredNetwork -> ComponentID -> String
smt_automaton_state, smt_automaton_arbiter_c, smt_automaton_arbiter_t :: ColoredNetwork -> ComponentID -> String
-- For queue variables, we add "Q___" in front to make it easy at the UI level to find queue variables
smt_buffer x i = "B___" ++ (utxt . getName $ getComponent x i) ++ "_state"
smt_buffer_arbiter x i = "B___" ++ (utxt . getName $ getComponent x i) ++ "_a"
smt_loadbalancer_arbiter x i = "M___" ++ (utxt . getName $ getComponent x i)
-- For merge variables, we add "M___" in front to make it easy at the UI level to find merge variables
smt_merge_arbiter x i = "M___" ++ (utxt . getName $ getComponent x i)
smt_match_arbiter_m x i = (utxt . getName $ getComponent x i) ++ "_m"
smt_match_arbiter_d x i = (utxt . getName $ getComponent x i) ++ "_d"
smt_automaton_state x i = "P___" ++ (utxt . getName $ getComponent x i) ++ "_state"
smt_automaton_arbiter_c x i = "P___" ++ (utxt . getName $ getComponent x i) ++ "_c"
smt_automaton_arbiter_t x i = "P___" ++ (utxt . getName $ getComponent x i) ++ "_t"

smt_guardqueue_q x i = "Q___"++ (utxt . getName $ getComponent x i)
smt_guardqueue_m x i = "M___"++ (utxt . getName $ getComponent x i)

smt_queue_packet :: ColoredNetwork -> ComponentID -> Color -> (Color -> String) -> String
smt_queue_packet x i d show_p_t = smt_queue x i ++ "." ++ show_p_t d

-- | An SMT model assigns values to queues.
type SMTModel = Map String Int

-- | Parsing SMT output into a model
parseSMTOutput :: String -> Either ParseError (Maybe SMTModel)
parseSMTOutput s = parse pSMTOutput "(unknown)" s

pSMTUnsat :: Parser (Maybe SMTModel)
pSMTUnsat = do
            _ <- string "unsat"
            return Nothing

pSMTQ_Value :: Parser (String,Int)
pSMTQ_Value = do
            spaces
            _ <- string "(define-fun"
            spaces
            q_name <- manyTill anyChar (Text.Parsec.try (char ' '))
            spaces
            _ <- string "() "
            _ <- (string "Int" <|> string "Bool")
            spaces
            value <- intP
            _ <- string ")\n"
            return (q_name,value)
    where
        intP = (char '0' >> return 0) <|>
               (string "false" >> return 0) <|>
               (string "true" >> return 1) <|>
               parsePositiveValue <|>
               parseNegativeValue

parseNegativeValue :: Parser Int
parseNegativeValue = do
    _ <- string "(- "
    val <- parsePositiveValue
    _ <- char ')'
    return $ -1 * val

parsePositiveValue :: Parser Int
parsePositiveValue = do
    firstDigit <- satisfy (\ ch -> '1' <= ch && ch <= '9')
    restDigits <- many digit
    return $ read $ firstDigit : restDigits

pSMTModel :: Parser (Maybe SMTModel)
pSMTModel = do
            spaces
            _ <- string "(model"
            ret <- manyTill pSMTQ_Value (char ')')
            return $ Just $ Map.fromList ret

pSMTSat :: Parser (Maybe SMTModel)
pSMTSat = do
            _ <- string "sat\n"
            pSMTModel

pSMTOutput :: Parser (Maybe SMTModel)
pSMTOutput = pSMTUnsat <|> pSMTSat

-- | Print an SMT model
showModel :: SMTModel -> String
showModel = unlines . mapMaybe (uncurry showVariable) . Map.assocs where
    showVariable var val
        | val == 0 = Nothing --don't show variables with value 0 (the default value)
        | isPrefixOf ("block_") var = if (val == 1) then Just $ var ++ " := true" else Nothing -- show block variables that are true
        | isPrefixOf ("idle_") var = if (val == 1) then Just $ var ++ " := true" else Nothing --don't show idle variables
        | elem '!' var = Nothing --don't show z3 generated variables (see http://stackoverflow.com/questions/10983067/z3-4-0-extra-output-in-model)
        | otherwise = Just $ var ++ " := " ++ show val
