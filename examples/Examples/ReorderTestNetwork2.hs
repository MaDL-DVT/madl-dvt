{-# LANGUAGE OverloadedStrings #-}

module Examples.ReorderTestNetwork (
    rtn2, rtn2_flattened, rtn2_typed
) where

import Madl.MsgTypes
import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- Reorder buffer
reorder_buffer_network :: Int -> Int -> MFunctionDisj -> MadlMacroNetwork
reorder_buffer_network idSize returnSize matchFunction = mkMacroNetwork components channels ports
    where
        db =  C Queue{ componentName = "dataBuffer", capacity=idSize}
        idb =  C Queue{ componentName = "idBuffer", capacity=idSize}
        rb =  C Queue{ componentName = "returnBuffer", capacity=returnSize}
        merge = C Merge {componentName = "merge"}
        match = C Match {componentName = "match", matchFunctions = [matchFunction]}

        -- Interface channel
        dataIn = Channel {channelName = "dataIn"}
        idIn = Channel {channelName = "idIn"}
        toNet = Channel {channelName = "toNetwork"}
        fromNet = Channel {channelName = "fromNetwork"}
        dataOut = Channel {channelName = "dataOut"}
        -- Internal channels
        idb_match = Channel {channelName = "idBuffer_match"}
        rb_match = Channel {channelName = "returnBuffer_match"}
        match_merge = Channel {channelName = "match_merge"}
        merge_rb = Channel {channelName = "merge_returnBuffer"}

        db_i = ("dataIn", "dataBuffer")
        db_o = ("dataBuffer", "toNetwork")
        idb_i = ("idIn", "idBuffer")
        idb_o = ("idBuffer", "idBuffer_match")
        rb_i = ("merge_returnBuffer", "returnBuffer")
        rb_o = ("returnBuffer", "returnBuffer_match")
        merge_i0 = ("fromNetwork", "merge")
        merge_i1 = ("match_merge", "merge")
        merge_o = ("merge", "merge_returnBuffer")
        match_i0 = ("returnBuffer_match", "match")
        match_i1 = ("idBuffer_match", "match")
        match_o0 = ("match", "match_merge")
        match_o1 = ("match", "dataOut")

        components = [db, idb, rb, merge, match]
        channels = [dataIn, idIn, toNet, fromNet, dataOut, idb_match, rb_match, match_merge, merge_rb]
        ports :: [(Text, Text)]
        ports = [db_i, db_o, idb_i, idb_o, rb_i, rb_o, merge_i0, merge_i1, merge_o, match_i0, match_i1, match_o0, match_o1]

reorder_buffer_interface :: [Text]
reorder_buffer_interface = ["dataIn", "idIn", "fromNetwork", "toNetwork", "dataOut"]

reorder_buffer :: Int -> Int -> MFunctionDisj -> Macro Channel
reorder_buffer idSize returnSize matchFunction = 
    mkMacro (reorder_buffer_network idSize returnSize matchFunction) ("reorder_buffer_" +++ showT idSize +++ "_" +++ showT returnSize) reorder_buffer_interface

rtn2 :: MadlNetwork
rtn2 = mkNetwork components channels ports
    where
        rbuffer = M MacroInstance {instanceName = "reorderBuffer", instanceMacro = reorder_buffer 2 3 (XMatch (XVar 0) (XVar 1))}
        -- Reorder Buffer input
        source =  C Source{ componentName = "source", messages = reqAndRsp}
        fork =  C Fork{ componentName = "fork"}
        -- Reorder Buffer output
        sink = C Sink {componentName = "sink"}
        -- Reordering network
        -- The network delays responses by going through 3 queues. Requests have only 1 queue in their path. 
        q$req = C Queue {componentName = "q$req", capacity = 2}
        q0$rsp = C Queue {componentName = "q0$rsp", capacity = 2}
        q1$rsp = C Queue {componentName = "q1$rsp", capacity = 2}
        q2$rsp = C Queue {componentName = "q2$rsp", capacity = 2}
        -- the delay network starts with a switch and ends with a merge
        NwMerge = C Merge {componentName = "NwMerge"}
        NwSwitch = C Switch {componentName = "NwSwitch", switching = [req,rsp]} 

        source_fork = Channel {channelName="source_fork"}
        fork_dataIn = Channel {channelName="fork_dataIn"}
        fork_idIn = Channel {channelName="fork_idIn"}
        rb_queue = Channel {channelName="reorderBuffer_queue"}
        queue_rb = Channel {channelName="queue_reorderBuffer"}
        rb_sink = Channel {channelName="reorderBuffer_sink"}

        source_o = ("source", "source_fork")
        fork_i = ("source_fork", "fork")
        fork_o0 = ("fork", "fork_dataIn")
        fork_o1 = ("fork", "fork_idIn")
        rb_i0 = ("fork_dataIn", "reorderBuffer")
        rb_i1 = ("fork_idIn", "reorderBuffer")
        rb_i2 = ("queue_reorderBuffer", "reorderBuffer")
        rb_o0 = ("reorderBuffer", "reorderBuffer_queue")
        rb_o1 = ("reorderBuffer", "reorderBuffer_sink")
        sink_i = ("reorderBuffer_sink", "sink")
        queue_i = ("reorderBuffer_queue", "queue")
        queue_o = ("queue", "queue_reorderBuffer")

        components = [rbuffer, source, fork, sink, queue]
        channels = [source_fork, fork_dataIn, fork_idIn, rb_queue, queue_rb, rb_sink]
        ports :: [(Text, Text)]
        ports = [source_o, fork_i, fork_o0, fork_o1, rb_i0, rb_i1, rb_i2, rb_o0, rb_o1, sink_i, queue_i, queue_o]

rtn2_flattened :: FlattenedNetwork
rtn2_flattened = unflatten rtn_flat where
    rtn_flat :: FlatFlattenedNetwork
    rtn_flat = unfoldMacros rtn2

rtn2_typed :: ColoredNetwork
rtn2_typed = channelTypes rtn2_flattened
