{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.MergeSwitchNetwork
Description : Predefined network: msn.
Copyright   : (c) Tessa Belder 2015

Predefined network: Merge switch network.
-}
module Examples.MergeSwitchNetwork (msn) where

import Madl.Network
import Examples.TypesAndFunctions
import Examples.Macros

import Utils.Text

-- | Network msn. Contains 2 source, a merge, a switch, and two sinks, as well as two creditcounter loops. Contains a deadlock.
msn :: MadlNetwork
msn = mkNetwork (NSpec components channels ports)
    where
        source0 =  C Source{componentName = "Source0", messages = req}
        queue0 = C Queue{componentName="QType0", capacity = 2}
        cc0 = M MacroInstance{instanceName="CCType0", instanceMacro=cc 2}
        join0 = C ControlJoin{componentName="CJoin0"}
        secQueue0 = C Queue{componentName="SecQType0", capacity=2}
        fork0 = C Fork{componentName="Fork0"}
        sink0 = C DeadSink{componentName="Sink0"}
        source1 =  C Source{componentName="Source1", messages = rsp}
        queue1 = C Queue{componentName="QType1", capacity = 2}
        cc1 = M MacroInstance{instanceName="CCType1", instanceMacro=cc 2}
        join1 = C ControlJoin{componentName="CJoin1"}
        secQueue1 = C Queue{componentName="SecQType1", capacity=2}
        fork1 = C Fork{componentName="Fork1"}
        sink1 = C Sink{componentName="Sink1"}
        merge = C Merge{componentName="Merge"}
        switch = C Switch{componentName="Switch", switching = [isReq, isRsp]}

        source0_queue0 = Channel{channelName="source0_queue0"}
        queue0_cjoin0 = Channel{channelName="queue0_cjoin0"}
        cc0_cjoin0 = Channel{channelName="cc0_cjoin0"}
        cjoin0_merge = Channel{channelName="cjoin0_merge"}
        switch_secQueue0 = Channel{channelName="switch_secQueue0"}
        secQueue0_fork0 = Channel{channelName="secQueue0_fork0"}
        fork0_cc0 = Channel{channelName="fork0_cc0"}
        fork0_sink0 = Channel{channelName="fork0_sink0"}
        source1_queue1 = Channel{channelName="source1_queue1"}
        queue1_cjoin1 = Channel{channelName="queue1_cjoin1"}
        cc1_cjoin1 = Channel{channelName="cc1_cjoin1"}
        cjoin1_merge = Channel{channelName="cjoin1_merge"}
        switch_secQueue1 = Channel{channelName="switch_secQueue1"}
        secQueue1_fork1 = Channel{channelName="secQueue1_fork1"}
        fork1_cc1 = Channel{channelName="fork1_cc1"}
        fork1_sink1 = Channel{channelName="fork1_sink1"}
        merge_switch = Channel{channelName="merge_switch"}

        source0_o = ("Source0", "source0_queue0")
        queue0_i = ("source0_queue0", "QType0")
        queue0_o = ("QType0", "queue0_cjoin0")
        cc0_i = ("fork0_cc0", "CCType0")
        cc0_o = ("CCType0", "cc0_cjoin0")
        join0_i0 = ("queue0_cjoin0", "CJoin0")
        join0_i1 = ("cc0_cjoin0", "CJoin0")
        join0_o = ("CJoin0", "cjoin0_merge")
        secQueue0_i = ("switch_secQueue0", "SecQType0")
        secQueue0_o = ("SecQType0", "secQueue0_fork0")
        fork0_i = ("secQueue0_fork0", "Fork0")
        fork0_o0 = ("Fork0", "fork0_cc0")
        fork0_o1 = ("Fork0", "fork0_sink0")
        sink0_i = ("fork0_sink0", "Sink0")
        source1_o = ("Source1", "source1_queue1")
        queue1_i = ("source1_queue1", "QType1")
        queue1_o = ("QType1", "queue1_cjoin1")
        cc1_i = ("fork1_cc1", "CCType1")
        cc1_o = ("CCType1", "cc1_cjoin1")
        join1_i0 = ("queue1_cjoin1", "CJoin1")
        join1_i1 = ("cc1_cjoin1", "CJoin1")
        join1_o = ("CJoin1", "cjoin1_merge")
        secQueue1_i = ("switch_secQueue1", "SecQType1")
        secQueue1_o = ("SecQType1", "secQueue1_fork1")
        fork1_i = ("secQueue1_fork1", "Fork1")
        fork1_o0 = ("Fork1", "fork1_cc1")
        fork1_o1 = ("Fork1", "fork1_sink1")
        sink1_i = ("fork1_sink1", "Sink1")
        merge_i0 = ("cjoin0_merge", "Merge")
        merge_i1 = ("cjoin1_merge", "Merge")
        merge_o = ("Merge", "merge_switch")
        switch_i = ("merge_switch", "Switch")
        switch_o0 = ("Switch", "switch_secQueue0")
        switch_o1 = ("Switch", "switch_secQueue1")


        components = [source1, queue0, cc0, join0, secQueue0, fork0, sink0, source0, queue1, cc1, join1, secQueue1, fork1, sink1, merge, switch]
        channels = [source0_queue0, queue0_cjoin0, cc0_cjoin0, cjoin0_merge, switch_secQueue0, secQueue0_fork0, fork0_cc0, fork0_sink0,
                    source1_queue1, queue1_cjoin1, cc1_cjoin1, cjoin1_merge, switch_secQueue1, secQueue1_fork1, fork1_cc1, fork1_sink1,
                    merge_switch]
        ports :: [(Text, Text)]
        ports = [source0_o, queue0_i, queue0_o, cc0_i, cc0_o, join0_i0, join0_i1, join0_o, secQueue0_i, secQueue0_o, fork0_i, fork0_o0, fork0_o1, sink0_i,
                 source1_o, queue1_i, queue1_o, cc1_i, cc1_o, join1_i0, join1_i1, join1_o, secQueue1_i, secQueue1_o, fork1_i, fork1_o0, fork1_o1, sink1_i,
                 merge_i0, merge_i1, merge_o, switch_i, switch_o0, switch_o1]