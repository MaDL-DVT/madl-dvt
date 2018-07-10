{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.MergeBlock
Description : Predefined network: mergeblock.
Copyright   : (c) Tessa Belder 2015

Predefined network: mergeblock.
-}
module Examples.MergeBlock (mergeBlock) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Network mergeblock: Contains a merge and a switch directly behind it. Is deadlockfree, but could easily be mistaken for having a deadlock.
mergeBlock :: MadlNetwork
mergeBlock = mkNetwork (NSpec components channels ports) where
    src0 = PatientSource "src0" nul
    src1 = Source "src1" req
    merge = Merge "merge"
    switch = Switch "switch" [isReq, isRsp]
    sink0 = Sink "sink0"
    sink1 = DeadSink "sink1"

    src0_merge = "src0_merge"
    src1_merge = "src1_merge"
    merge_switch = "merge_switch"
    switch_sink0 = "switch_sink0"
    switch_sink1 = "switch_sink1"

    src0_o = ("src0", "src0_merge")
    src1_o = ("src1", "src1_merge")
    merge_a = ("src0_merge", "merge")
    merge_b = ("src1_merge", "merge")
    merge_o = ("merge", "merge_switch")
    switch_i = ("merge_switch", "switch")
    switch_a = ("switch", "switch_sink0")
    switch_b = ("switch", "switch_sink1")
    sink0_i = ("switch_sink0", "sink0")
    sink1_i = ("switch_sink1", "sink1")

    components = map C [src0, src1, merge, switch, sink0, sink1]
    channels = map Channel [src0_merge, src1_merge, merge_switch, switch_sink0, switch_sink1]
    ports :: [(Text, Text)]
    ports = [src0_o, src1_o, merge_a, merge_b, merge_o, switch_i, switch_a, switch_b, sink0_i, sink1_i]