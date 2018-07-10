{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.ReorderTestNetwork
Description : Predefined network: rtn.
Copyright   : (c) Tessa Belder 2015-2016.

Predefined network: rtn. Reorder test network.
-}
module Examples.ReorderTestNetwork (rtn) where

import qualified Data.HashMap as Hash
import qualified Data.Text as T (concat)

import Madl.MsgTypes
import Madl.Network
import Examples.TypesAndFunctions
import Examples.Macros

import Utils.Text

-- | Macro idTracker. Tracks ids.
id_tracker :: Int -> Macro Channel
id_tracker idSize = mkMacro (id_tracker_network idSize) ("idTracker"+++showT idSize) (id_tracker_interface idSize)

id_tracker_network :: Int -> MadlMacroNetwork
id_tracker_network idSize = mkMacroNetwork (NSpec components channels ports) where
    lb = LoadBalancer "LoadBalancer"
    regs = map ( register . ("reg" +++)) ids
    forks = map (Fork . ("fork" +++)) ids
    funcs = map (\s -> Function ("fun" +++ s) (regFunction s) (regReturnType s)) ids
    merge = Merge {componentName="merge"}

    -- Interface channels
    idIn = "idIn"
    trackOut = "trackOut"
    idOut s = ("idOut"+++s)
    -- Internal channels
    lbFork s = ("lb_fork"+++s)
    forkReg s = T.concat["fork",s,"_reg",s]
    forkFun s = T.concat["fork",s,"_fun",s]
    funMerge s = T.concat["fun",s,"_merge"]

    lb_i = (idIn, "LoadBalancer")
    lb_o s = ("LoadBalancer", lbFork s)
    regs_i s = (forkReg s, "reg"+++s)
    regs_o s = ("reg"+++s, idOut s)
    fork_i s = (lbFork s, "fork"+++s)
    fork_o0 s = ("fork"+++s, forkReg s)
    fork_o1 s = ("fork"+++s, forkFun s)
    fun_i s = (forkFun s, "fun"+++s)
    fun_o s = ("fun"+++s, funMerge s)
    merge_i s = (funMerge s, "merge")
    merge_o = ("merge", trackOut)

    components = map C $ [lb, merge] ++ regs ++ forks ++ funcs
    channels = map Channel $ [idIn, trackOut] ++ concatMap (\f -> map f ids) [idOut, lbFork, forkReg, forkFun, funMerge]
    ports :: [(Text, Text)]
    ports = [lb_i, merge_o] ++ concatMap (\f -> map f ids) [lb_o, regs_i, regs_o, fork_i, fork_o0, fork_o1, fun_i, fun_o, merge_i]

    regFunction i = XChoice ("slot" +++ i) . Left $ XConcat Hash.empty
    regReturnType i = constColorSet ("slot" +++ i)
    ids = map showT [0..idSize-1]

id_tracker_interface :: Int -> [Text]
id_tracker_interface idSize = ["idIn", "trackOut"] ++ (map (("idOut"+++) . showT) [0..idSize-1])

-- | Component register: queue of size 1.
register :: Text -> Component
register = flip Queue 1

-- | Macro reorder-buffer. Consumes data and reorders it according to tracker input.
rob_macro :: Int -> Macro Channel
rob_macro idSize = mkMacro (rob_network idSize) ("rob"+++showT idSize) (rob_interface idSize)

rob_network :: Int -> MadlMacroNetwork
rob_network idSize = mkMacroNetwork (NSpec components channels ports) where
    switch = Switch "switch" (map (isType . ("slot" +++)) ids)
    reg = register . ("reg"+++)
    join = ControlJoin . ("cjoin"+++)
    merge = Merge "merge"

    -- Interface channels
    trackIn = "trackIn"
    dataIn s = ("dataIn"+++s)
    dataOut = "dataOut"
    -- Internal channels
    regJoin s = T.concat["reg",s,"_cjoin",s]
    switchJoin s = "switch_cjoin"+++s
    joinMerge s = T.concat["cjoin",s,"_merge"]

    sw_i = (trackIn, "switch")
    sw_o s = ("switch", switchJoin s)
    reg_i s = (dataIn s, "reg"+++s)
    reg_o s = ("reg"+++s, regJoin s)
    join_i0 s = (regJoin s, "cjoin"+++s)
    join_i1 s = (switchJoin s, "cjoin"+++s)
    join_o s = ("cjoin"+++s, joinMerge s)
    merge_i s = (joinMerge s, "merge")
    merge_o = ("merge", dataOut)

    components = map C $ [switch, merge] ++ concatMap (\f -> map f ids) [reg, join]
    channels = map Channel $ [trackIn, dataOut] ++ concatMap (\f -> map f ids) [dataIn, regJoin, switchJoin, joinMerge]
    ports :: [(Text, Text)]
    ports = [sw_i, merge_o] ++ concatMap (\f -> map f ids) [sw_o, reg_i, reg_o, join_i0, join_i1, join_o, merge_i]

    ids = map showT [0..idSize-1]

rob_interface :: Int -> [Text]
rob_interface idSize = ["trackIn"] ++ (map (("dataIn"+++) . showT) [0..idSize-1]) ++ ["dataOut"]

-- | Macro reorder buffer. Uses a match and a no-match loop to reorder.
reorder_buffer :: Int -> Int -> MFunctionBool -> Macro Channel
reorder_buffer idSize returnSize mf =
    mkMacro (reorder_buffer_network idSize returnSize mf) ("reorder_buffer_" +++ showT idSize +++ "_" +++ showT returnSize) reorder_buffer_interface

reorder_buffer_network :: Int -> Int -> MFunctionBool -> MadlMacroNetwork
reorder_buffer_network idSize returnSize mf = mkMacroNetwork (NSpec components channels ports) where
    db =  C Queue{ componentName = "dataBuffer", capacity=idSize}
    idb =  C Queue{ componentName = "idBuffer", capacity=idSize}
    rb =  C Queue{ componentName = "returnBuffer", capacity=1}
    buffer = C Queue{ componentName = "noMatchBuffer", capacity=returnSize - 1}
    merge = C Merge {componentName = "merge"}
    match = C Match {componentName = "match", matchFunction = mf}

    -- Interface channels
    dataIn = Channel {channelName = "dataIn"}
    idIn = Channel {channelName = "idIn"}
    toNet = Channel {channelName = "toNetwork"}
    fromNet = Channel {channelName = "fromNetwork"}
    dataOut = Channel {channelName = "dataOut"}
    -- Internal channels
    idb_match = Channel {channelName = "idBuffer_match"}
    rb_match = Channel {channelName = "returnBuffer_match"}
    match_buffer = Channel {channelName = "match_noMatchBuffer"}
    buffer_merge = Channel {channelName = "noMatchBuffer_merge"}
    merge_rb = Channel {channelName = "merge_returnBuffer"}

    db_i = ("dataIn", "dataBuffer")
    db_o = ("dataBuffer", "toNetwork")
    idb_i = ("idIn", "idBuffer")
    idb_o = ("idBuffer", "idBuffer_match")
    rb_i = ("merge_returnBuffer", "returnBuffer")
    rb_o = ("returnBuffer", "returnBuffer_match")
    buffer_i = ("match_noMatchBuffer", "noMatchBuffer")
    buffer_o = ("noMatchBuffer", "noMatchBuffer_merge")
    merge_i0 = ("fromNetwork", "merge")
    merge_i1 = ("noMatchBuffer_merge", "merge")
    merge_o = ("merge", "merge_returnBuffer")
    match_i0 = ("idBuffer_match", "match")
    match_i1 = ("returnBuffer_match", "match")
    match_o0 = ("match", "dataOut")
    match_o1 = ("match", "match_noMatchBuffer")


    components = [db, idb, rb, buffer, merge, match]
    channels = [dataIn, idIn, toNet, fromNet, dataOut, idb_match, rb_match, match_buffer, buffer_merge, merge_rb]
    ports :: [(Text, Text)]
    ports = [db_i, db_o, idb_i, idb_o, rb_i, rb_o, buffer_i, buffer_o, merge_i0, merge_i1, merge_o, match_i0, match_i1, match_o0, match_o1]

reorder_buffer_interface :: [Text]
reorder_buffer_interface = ["dataIn", "idIn", "fromNetwork", "toNetwork", "dataOut"]

-- | Macro reorder buffer 2. Uses an idTracker, a multimatch with multiple match-inputs and 1 data-input, and a ROB to reorder.
reorder_buffer2 :: Int -> MFunctionBool -> Macro Channel
reorder_buffer2 idSize mf =
    mkMacro (reorder_buffer2_network idSize mf) ("reorder_buffer2_" +++ showT idSize) reorder_buffer2_interface

reorder_buffer2_network :: Int -> MFunctionBool -> MadlMacroNetwork
reorder_buffer2_network idSize mf = mkMacroNetwork (NSpec components channels ports) where
    db =  C $ Queue "dataBuffer" idSize
    rb =  C $ register "returnBuffer"
    tracker = C $ Queue "tracker" idSize
    match = C $ MultiMatch "match" mf
    idtracker = M $ MacroInstance "idTracker" (id_tracker idSize)
    rob = M $ MacroInstance "ROB" (rob_macro idSize)

    -- Interface channels
    dataIn = "dataIn"
    idIn = "idIn"
    toNet = "toNetwork"
    fromNet = "fromNetwork"
    dataOut = "dataOut"
    -- Internal channels
    id_track = "idTracker_tracker"
    track_rob = "tracker_ROB"
    id_match s = T.concat["idTracker",s,"_match",s]
    match_rob s = T.concat["match",s,"_ROB",s]
    rb_match = "returnBuffer_match"

    db_i = (dataIn, "dataBuffer")
    db_o = ("dataBuffer", toNet)
    rb_i = (fromNet, "returnBuffer")
    rb_o = ("returnBuffer", rb_match)
    tracker_i = (id_track, "tracker")
    tracker_o = ("tracker", track_rob)
    match_mIn s = (id_match s, "match")
    match_dIn = (rb_match, "match")
    match_out s = ("match", match_rob s)
    idtracker_i = (idIn, "idTracker")
    idtracker_tOut = ("idTracker", id_track)
    idtracker_idOut s = ("idTracker", id_match s)
    rob_tIn = (track_rob, "ROB")
    rob_dIn s = (match_rob s, "ROB")
    rob_dOut = ("ROB", dataOut)

    components = [db, rb, tracker, match, idtracker, rob]
    channels = map Channel $ [dataIn, idIn, toNet, fromNet, dataOut, id_track, track_rob, rb_match] ++ concatMap (\f -> map f ids) [id_match, match_rob]
    ports :: [(Text, Text)]
    ports = [db_i, db_o, rb_i, rb_o, tracker_i, tracker_o, idtracker_i, idtracker_tOut, rob_tIn, rob_dOut]
            ++ (concatMap (\f -> map f ids) [match_mIn, match_out, idtracker_idOut, rob_dIn]) ++ [match_dIn]

    ids = map showT [0..idSize-1]

reorder_buffer2_interface :: [Text]
reorder_buffer2_interface = ["dataIn", "idIn", "fromNetwork", "toNetwork", "dataOut"]

-- Reorder buffer 3: Uses a multimatch with 1 match-input and multiple data-inputs.
reorder_buffer3 :: Int -> Int -> MFunctionBool -> Macro Channel
reorder_buffer3 idSize returnSize mf =
    mkMacro (reorder_buffer3_network idSize returnSize mf) ("reorder_buffer3_" +++ showT idSize +++ "_" +++ showT returnSize) reorder_buffer3_interface

reorder_buffer3_network :: Int -> Int -> MFunctionBool -> MadlMacroNetwork
reorder_buffer3_network idSize returnSize mf = mkMacroNetwork (NSpec components channels ports) where
    db =  Queue{ componentName = "dataBuffer", capacity=idSize}
    idb =  Queue{ componentName = "idBuffer", capacity=idSize}
    lb = LoadBalancer "loadBalancer"
    reg = register . ("returnRegister" +++)
    match = MultiMatch {componentName = "match", matchFunction = mf}

    -- Interface channels
    dataIn = "dataIn"
    idIn = "idIn"
    toNet = "toNetwork"
    fromNet = "fromNetwork"
    dataOut = "dataOut"
    -- Internal channels
    idb_match = "idBuffer_match"
    lb_reg s = T.concat["loadBalancer_returnRegister",s]
    reg_match s = T.concat["returnRegister",s,"_match"]

    db_i = ("dataIn", "dataBuffer")
    db_o = ("dataBuffer", "toNetwork")
    idb_i = ("idIn", "idBuffer")
    idb_o = ("idBuffer", "idBuffer_match")
    lb_i = ("fromNetwork", "loadBalancer")
    lb_o s = ("loadBalancer", lb_reg s)
    reg_i s = (lb_reg s, "returnRegister" +++ s)
    reg_o s = ("returnRegister" +++ s, reg_match s)
    match_mIn = ("idBuffer_match", "match")
    match_dIn s = (reg_match s, "match")
    match_o = ("match", "dataOut")

    components = map C $ [db, idb, lb, match] ++ map reg returns
    channels = map Channel $ [dataIn, idIn, toNet, fromNet, dataOut, idb_match] ++ concatMap (\f -> map f returns) [lb_reg, reg_match]
    ports :: [(Text, Text)]
    ports = [db_i, db_o, idb_i, idb_o, lb_i, match_mIn, match_o] ++ concatMap (\f -> map f returns) [lb_o, reg_i, reg_o, match_dIn]

    returns = map showT [0..returnSize-1]

reorder_buffer3_interface :: [Text]
reorder_buffer3_interface = ["dataIn", "idIn", "fromNetwork", "toNetwork", "dataOut"]

-- | Macro network implentation.
network_implementation :: MadlMacroNetwork -> Macro Channel
network_implementation network = mkMacro network "network" network_implementation_interface

-- | Abstract network implementation: no reordering
no_reordering_network :: MadlMacroNetwork
no_reordering_network = mkMacroNetwork (NSpec components channels ports) where
    queue = C Queue {componentName = "queue", capacity = 2}

    -- Interface channels
    dataIn = Channel {channelName="dataIn"}
    dataOut = Channel {channelName="dataOut"}

    queue_i = ("dataIn", "queue")
    queue_o = ("queue", "dataOut")

    components = [queue]
    channels = [dataIn, dataOut]
    ports :: [(Text, Text)]
    ports = [queue_i, queue_o]

-- | Abstract network implementation: reordering
reordering_network :: MadlMacroNetwork
reordering_network = mkMacroNetwork (NSpec components channels ports) where
    switch = C Switch {componentName="switch", switching = [isReq, isRsp]}
    reqQ = C Queue {componentName = "requestQueue", capacity = 2}
    reqDel = M MacroInstance {instanceName = "requestDelay", instanceMacro = delay}
    rspQ = C Queue {componentName = "responseQueue", capacity = 2}
    rspDel = M MacroInstance {instanceName = "responseDelay", instanceMacro = delay}
    merge = C Merge {componentName="merge"}

    -- Interface channels
    dataIn = Channel {channelName="dataIn"}
    dataOut = Channel {channelName="dataOut"}
    -- Internal channels
    sw_reqQ = Channel {channelName="switch_requestQueue"}
    reqQ_reqD = Channel {channelName="requestQueue_requestDelay"}
    reqD_merge = Channel {channelName="requestDelay_merge"}
    sw_rspQ = Channel {channelName="switch_responseQueue"}
    rspQ_rspD = Channel {channelName="responseQueue_responseDelay"}
    rspD_merge = Channel {channelName="responseDelay_merge"}

    switch_i = ("dataIn", "switch")
    switch_o0 = ("switch", "switch_requestQueue")
    switch_o1 = ("switch", "switch_responseQueue")
    reqQ_i = ("switch_requestQueue", "requestQueue")
    reqQ_o = ("requestQueue", "requestQueue_requestDelay")
    reqD_i = ("requestQueue_requestDelay","requestDelay")
    reqD_o = ("requestDelay","requestDelay_merge")
    rspQ_i = ("switch_responseQueue", "responseQueue")
    rspQ_o = ("responseQueue", "responseQueue_responseDelay")
    rspD_i = ("responseQueue_responseDelay","responseDelay")
    rspD_o = ("responseDelay","responseDelay_merge")
    merge_i0 = ("requestDelay_merge", "merge")
    merge_i1 = ("responseDelay_merge", "merge")
    merge_o = ("merge", "dataOut")

    components = [switch, reqQ, reqDel, rspQ, rspDel, merge]
    channels = [dataIn, dataOut, sw_reqQ, reqQ_reqD, reqD_merge, sw_rspQ, rspQ_rspD, rspD_merge]
    ports :: [(Text, Text)]
    ports = [switch_i, switch_o0, switch_o1, reqQ_i, reqQ_o, reqD_i, reqD_o, rspQ_i, rspQ_o, rspD_i, rspD_o, merge_i0, merge_i1, merge_o]

network_implementation_interface :: [Text]
network_implementation_interface = ["dataIn", "dataOut"]

-- | Network rtn. @rtn version idSize returnSize reordering@ constructs a network where:
-- 1. The reorder buffer with the given version number is used. Valid version numbers: 1, 2, 3.
-- 2. The number of ids that can be stored is equal to @idSize@.
-- 3. The number of returning packets that can be stored is equal to @returnSize@. (Not applicable for version 2).
-- 4. The abstract network is a reordering network if @reordering = True@.
rtn :: Int -> Int -> Int -> Bool -> MadlNetwork
rtn version idSize returnSize reordering = mkNetwork (NSpec components channels ports) where
    rbuffer = M MacroInstance {instanceName = "reorderBuffer", instanceMacro = rb}
    rb = case version of
        1 -> reorder_buffer idSize returnSize (XMatch (XVar 0) (XVar 1))
        2 -> reorder_buffer2 idSize (XMatch (XVar 0) (XVar 1))
        3 -> reorder_buffer3 idSize returnSize (XMatch (XVar 0) (XVar 1))
        _ -> error "Invalid version number"
    -- Reorder Buffer input
    source =  C Source{ componentName = "source", messages = reqAndRsp}
    fork =  C Fork{ componentName = "fork"}
    -- Reorder Buffer output
    sink = C Sink {componentName = "sink"}
    -- Reordering network
    net = M MacroInstance {instanceName = "network", instanceMacro = network_implementation (if reordering then reordering_network else no_reordering_network)}

    source_fork = Channel {channelName="source_fork"}
    fork_dataIn = Channel {channelName="fork_dataIn"}
    fork_idIn = Channel {channelName="fork_idIn"}
    rb_net = Channel {channelName="reorderBuffer_network"}
    net_rb = Channel {channelName="network_reorderBuffer"}
    rb_sink = Channel {channelName="reorderBuffer_sink"}

    source_o = ("source", "source_fork")
    fork_i = ("source_fork", "fork")
    fork_o0 = ("fork", "fork_dataIn")
    fork_o1 = ("fork", "fork_idIn")
    rb_i0 = ("fork_dataIn", "reorderBuffer")
    rb_i1 = ("fork_idIn", "reorderBuffer")
    rb_i2 = ("network_reorderBuffer", "reorderBuffer")
    rb_o0 = ("reorderBuffer", "reorderBuffer_network")
    rb_o1 = ("reorderBuffer", "reorderBuffer_sink")
    sink_i = ("reorderBuffer_sink", "sink")
    net_i = ("reorderBuffer_network", "network")
    net_o = ("network", "network_reorderBuffer")

    components = [rbuffer, source, fork, sink, net]
    channels = [source_fork, fork_dataIn, fork_idIn, rb_net, net_rb, rb_sink]
    ports :: [(Text, Text)]
    ports = [source_o, fork_i, fork_o0, fork_o1, rb_i0, rb_i1, rb_i2, rb_o0, rb_o1, sink_i, net_i, net_o]