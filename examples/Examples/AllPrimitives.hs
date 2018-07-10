{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.AllPrimitives
Description : Predefined network: allPrimitives.
Copyright   : (c) Sanne Woude 2015

Predefined network: allPrimitives.
-}
module Examples.AllPrimitives (allPrimitives) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | The allPrimitives network, with or without a deadlock.
allPrimitives :: Bool -> MadlNetwork
allPrimitives dl = mkNetwork (NSpec components channels ports) where
    src0   = Source      "src0"     (if dl then reqAndRsp else rsp)
    src1   = Source      "src1"     req
    fork   = Fork        "fork"
    merge0 = Merge       "merge0"
    queue0 = Queue       "queue0"   2
    queue1 = Queue       "queue1"   2
    switch = Switch      "switch"   [isRsp, isReq]
    join   = ControlJoin "join"
    merge1 = Merge       "merge1"
    sink   = Sink        "sink"

    src0_fork     = "src0_fork"
    fork_queue0   = "fork_queue0"
    fork_merge0   = "fork_merge0"
    src1_merge0   = "src1_merge0"
    merge0_queue1 = "merge0_queue1"
    queue0_join   = "queue0_join"
    queue1_switch = "queue1_switch"
    switch_join   = "switch_join"
    join_merge1   = "join_merge1"
    switch_merge1 = "switch_merge1"
    merge1_sink   = "merge1_sink"

    src0_o    = ("src0"          , "src0_fork")
    src1_o    = ("src1"          , "src1_merge0")
    fork_i    = ("src0_fork"     , "fork")
    fork_a    = ("fork"          , "fork_queue0")
    fork_b    = ("fork"          , "fork_merge0")
    merge0_a  = ("fork_merge0"   , "merge0")
    merge0_b  = ("src1_merge0"   , "merge0")
    merge0_o  = ("merge0"        , "merge0_queue1")
    queue0_i  = ("fork_queue0"   , "queue0")
    queue0_o  = ("queue0"        , "queue0_join")
    queue1_i  = ("merge0_queue1" , "queue1")
    queue1_o  = ("queue1"        , "queue1_switch")
    switch_i  = ("queue1_switch" , "switch")
    switch_a  = ("switch"        , "switch_join")
    switch_b  = ("switch"        , "switch_merge1")
    join_a    = ("queue0_join"   , "join")
    join_b    = ("switch_join"   , "join")
    join_o    = ("join"          , "join_merge1")
    merge1_a  = ("join_merge1"   , "merge1")
    merge1_b  = ("switch_merge1" , "merge1")
    merge1_o  = ("merge1"        , "merge1_sink")
    sink_i    = ("merge1_sink"   , "sink")

    components =
        map C [src0, src1, fork, merge0, queue0, queue1, switch, join, merge1, sink]
    channels =
        map Channel [src0_fork, fork_queue0, fork_merge0, src1_merge0, merge0_queue1, queue0_join, queue1_switch, switch_join, join_merge1, switch_merge1, merge1_sink]
    ports :: [(Text, Text)]
    ports = [src0_o, src1_o, fork_i, fork_a, fork_b, merge0_a, merge0_b, merge0_o, queue0_i, queue0_o, queue1_i, queue1_o, switch_i, switch_a, switch_b, join_a, join_b, join_o, merge1_a, merge1_b, merge1_o, sink_i]
