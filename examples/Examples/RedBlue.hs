{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.RedBlue
Description : Predefined network: redblue.
Copyright   : (c) Julien Schmaltz 2015

Predefined network: redblue.
-}
module Examples.RedBlue (redblue) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Network redblue. The well-known red-blue example
redblue :: Bool -> MadlNetwork
redblue dl = mkNetwork (NSpec components channels ports) where
    src0   = Source      "src0"     req
    src1   = Source      "src1"     rsp
    fork   = Fork        "fork"
    merge0 = Merge       "merge0"
    queue0 = Queue       "queue0"   2
    queue1 = Queue       "queue1"   2
    queue2 = Queue       "queue2"   2
    switch0 = Switch      "switch0"  (if dl then [isRsp, isReq] else [isReq,isRsp])
    switch1 = Switch      "switch1"  [isReq,isRsp]
    join0   = ControlJoin "join0"
    join1   = ControlJoin "join1"
    sink0   = Sink        "sink0"
    sink1   = Sink        "sink1"

    src0_merge0     = "src0_merge0"
    src1_merge0     = "src1_merge0"
    merge0_queue0   = "merge0_queue0"
    queue0_fork     = "queue0_fork"
    fork_queue1     = "fork_queue1"
    fork_queue2     = "fork_queue2"
    queue2_switch0  = "queue2_switch0"
    queue1_switch1  = "queue1_switch1"
    switch1_join1   = "switch1_join1"
    switch1_join0   = "switch1_join0"
    switch0_join1   = "switch0_join1"
    switch0_join0   = "switch0_join0"
    join0_sink0     = "join0_sink0"
    join1_sink1     = "join1_sink1"

    src0_o    = ("src0"          , "src0_merge0")
    src1_o    = ("src1"          , "src1_merge0")
    merge0_a  = ("src0_merge0"   , "merge0")
    merge0_b  = ("src1_merge0"   , "merge0")
    merge0_o  = ("merge0"        , "merge0_queue0")
    queue0_i  = ("merge0_queue0" , "queue0")
    queue0_o  = ("queue0"        , "queue0_fork")
    fork_i    = ("queue0_fork"    , "fork")
    fork_a    = ("fork"          , "fork_queue1")
    fork_b    = ("fork"          , "fork_queue2")
    queue1_i  = ("fork_queue1"   , "queue1")
    queue2_i  = ("fork_queue2"   , "queue2")
    queue1_o  = ("queue1"        , "queue1_switch1")
    queue2_o  = ("queue2"        , "queue2_switch0")
    switch0_i = ("queue2_switch0", "switch0")
    switch0_a = ("switch0"       , "switch0_join1")
    switch0_b = ("switch0"       , "switch0_join0")
    switch1_i = ("queue1_switch1", "switch1")
    switch1_a = ("switch1"       , "switch1_join1")
    swicth1_b = ("switch1"       , "switch1_join0")
    join1_a   = ("switch0_join1" , "join1")
    join1_b   = ("switch1_join1" , "join1")
    join1_o   = ("join1"         , "join1_sink1")
    join0_a   = ("switch0_join0" , "join0")
    join0_b   = ("switch1_join0" , "join0")
    join0_o   = ("join0"         , "join0_sink0")
    sink0_i   = ("join0_sink0"   , "sink0")
    sink1_i   = ("join1_sink1"   , "sink1")

    components =
        map C [src0, src1, fork, merge0, queue0, queue1, queue2, switch0, switch1, join0, join1, sink0, sink1]
    channels =
        map Channel [src0_merge0, src1_merge0, merge0_queue0, queue0_fork, fork_queue1, fork_queue2, queue2_switch0, queue1_switch1, switch1_join1, switch1_join0, switch0_join1, switch0_join0, join0_sink0, join1_sink1]
    ports :: [(Text, Text)]
    ports = [ src0_o, src1_o, merge0_a, merge0_b, merge0_o, queue0_i, queue0_o, fork_i, fork_a, fork_b, queue1_i, queue2_i, queue1_o, queue2_o, switch0_i, switch0_a, switch0_b, switch1_i, switch1_a, swicth1_b, join1_a, join1_b, join1_o, join0_a, join0_b, join0_o, sink0_i, sink1_i]