{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.TwoAgents
Description : Predefined network: two agents.
Copyright   : (c) Tessa Belder 2015.

Predefined networks: two agents. The well known two agents example.
-}
module Examples.TwoAgents (fabric,agent,two_agents) where

import Madl.Network
import Examples.Macros
import Examples.TypesAndFunctions

import Utils.Text

-- | Macro Fabric: the fabric between the two agents. @fabric size@ produces a network where the queues have size @size@.
fabric :: Int -> Macro Channel
fabric size = mkMacro (fabric_network size) "Fabric" fabric_interface

fabric_network :: Int -> MadlMacroNetwork
fabric_network size = mkMacroNetwork (NSpec components channels ports)
    where
        dx1 = C Queue{ componentName = "dx1", capacity = size}
        cx1 = C Queue{ componentName = "cx1", capacity = size}
        cx2 = C Queue{ componentName = "cx2", capacity = size}
        dx2 = C Queue{ componentName = "dx2", capacity = size}
        cx3 = C Queue{ componentName = "cx3", capacity = size}
        cx4 = C Queue{ componentName = "cx4", capacity = size}

        i0 = Channel{ channelName = "i0"}
        i1 = Channel{ channelName = "i1"}
        i2 = Channel{ channelName = "i2"}
        i3 = Channel{ channelName = "i3"}
        i4 = Channel{ channelName = "i4"}
        i5 = Channel{ channelName = "i5"}
        o0 = Channel{ channelName = "o0"}
        o1 = Channel{ channelName = "o1"}
        o2 = Channel{ channelName = "o2"}
        o3 = Channel{ channelName = "o3"}
        o4 = Channel{ channelName = "o4"}
        o5 = Channel{ channelName = "o5"}

        dx1_i = ("i0", "dx1")
        cx1_i = ("i1", "cx1")
        cx2_i = ("i2", "cx2")
        dx2_i = ("i3", "dx2")
        cx3_i = ("i4", "cx3")
        cx4_i = ("i5", "cx4")
        dx1_o = ("dx1", "o0")
        cx1_o = ("cx1", "o1")
        cx2_o = ("cx2", "o2")
        dx2_o = ("dx2", "o3")
        cx3_o = ("cx3", "o4")
        cx4_o = ("cx4", "o5")

        components = [dx1, cx1, cx2, dx2, cx3, cx4]
        channels = [i0, i1, i2, i3, i4, i5, o0, o1, o2, o3, o4, o5]
        ports :: [(Text, Text)]
        ports = [dx1_i, cx1_i, cx2_i, dx2_i, cx3_i, cx4_i, dx1_o, cx1_o, cx2_o, dx2_o, cx3_o, cx4_o]

fabric_interface :: [Text]
fabric_interface = ["i0", "i1", "i2", "i3", "i4", "i5", "o0", "o1", "o2", "o3", "o4", "o5"]

-- | Macro Agent: a single agent. @agent dataSize creditSize@ produces a network where:
-- 1. The queues have size @dataSize@.
-- 2. The credit counters have size @creditSize@.
agent :: Int -> Int -> Macro Channel
agent dataSize creditSize = mkMacro (agent_network dataSize creditSize) ("Agent") agent_interface

agent_network :: Int -> Int -> MadlMacroNetwork
agent_network dataSize creditSize = mkMacroNetwork (NSpec components channels ports)
    where
        cq1 = C Queue{ componentName = "cq1", capacity = dataSize}
        cq2 = C Queue{ componentName = "cq2", capacity = dataSize}
        dq1 = C Queue{ componentName = "dq1", capacity = dataSize}
        dq2 = C Queue{ componentName = "dq2", capacity = dataSize}
        func = C Function{ componentName = "function", function = toRSP, returnType = rsp}
        source = C Source{ componentName = "source", messages = req}
        sink = C Sink{ componentName = "sink"}
        fork1 = C Fork{ componentName = "fork1"}
        fork2 = C Fork{ componentName = "fork2"}
        cjoin1 = C ControlJoin{ componentName = "cjoin1"}
        cjoin2 = C ControlJoin{ componentName = "cjoin2"}
        switch = C Switch{ componentName = "switch", switching = [isReq, isRsp]}
        merge = C Merge{ componentName = "merge"}
        del = M MacroInstance{ instanceName = "delay", instanceMacro = delay}
        cc1 = M MacroInstance{ instanceName = "cc1", instanceMacro = cc creditSize}
        cc2 = M MacroInstance{ instanceName = "cc2", instanceMacro = cc creditSize}

        i0 = Channel{ channelName = "i0"}
        i1 = Channel{ channelName = "i1"}
        i2 = Channel{ channelName = "i2"}
        o0 = Channel{ channelName = "o0"}
        o1 = Channel{ channelName = "o1"}
        o2 = Channel{ channelName = "o2"}
        source_cjoin1 = Channel{ channelName = "source_cjoin1"}
        cq1_cjoin_1 = Channel{ channelName = "cq1_cjoin_1"}
        cjoin1_merge = Channel{ channelName = "cjoin1_merge"}
        function_cjoin2 = Channel{ channelName = "function_cjoin2"}
        cq2_cjoin2 = Channel{ channelName = "cq2_cjoin2"}
        cjoin2_merge = Channel{channelName = "cjoin2_merge"}
        delay_function = Channel{ channelName = "delay_function"}
        switch_dq1 = Channel{ channelName = "switch_dq1"}
        dq1_fork1 = Channel{ channelName = "dq1_fork1"}
        fork1_cc1 = Channel{ channelName = "fork1_cc1"}
        fork1_delay = Channel{ channelName = "fork1_delay"}
        switch_dq2 = Channel{ channelName = "switch_dq2"}
        dq2_fork2 = Channel{ channelName = "dq2_fork2"}
        fork2_cc2 = Channel{ channelName = "fork2_cc2"}
        fork2_sink = Channel{ channelName = "fork2_sink"}

        cq1_i = ("i1", "cq1")
        cq1_o = ("cq1", "cq1_cjoin_1")
        cq2_i = ("i2", "cq2")
        cq2_o = ("cq2", "cq2_cjoin2")
        dq1_i = ("switch_dq1", "dq1")
        dq1_o = ("dq1", "dq1_fork1")
        dq2_i = ("switch_dq2", "dq2")
        dq2_o = ("dq2", "dq2_fork2")
        function_i = ("delay_function", "function")
        function_o = ("function", "function_cjoin2")
        source_o = ("source", "source_cjoin1")
        sink_i = ("fork2_sink", "sink")
        fork1_i = ("dq1_fork1", "fork1")
        fork1_o0 = ("fork1", "fork1_delay")
        fork1_o1 = ("fork1", "fork1_cc1")
        fork2_i = ("dq2_fork2", "fork2")
        fork2_o0 = ("fork2", "fork2_sink")
        fork2_o1 = ("fork2", "fork2_cc2")
        cjoin1_i0 = ("source_cjoin1", "cjoin1")
        cjoin1_i1 = ("cq1_cjoin_1", "cjoin1")
        cjoin1_o = ("cjoin1", "cjoin1_merge")
        cjoin2_i0 = ("function_cjoin2", "cjoin2")
        cjoin2_i1 = ("cq2_cjoin2", "cjoin2")
        cjoin2_o = ("cjoin2", "cjoin2_merge")
        switch_i = ("i0", "switch")
        switch_o0 = ("switch", "switch_dq1")
        switch_o1 = ("switch", "switch_dq2")
        merge_i0 = ("cjoin1_merge", "merge")
        merge_i1 = ("cjoin2_merge", "merge")
        merge_o = ("merge", "o0")
        delay_i = ("fork1_delay", "delay")
        delay_o = ("delay", "delay_function")
        cc1_i = ("fork1_cc1", "cc1")
        cc1_o = ("cc1", "o1")
        cc2_i = ("fork2_cc2", "cc2")
        cc2_o = ("cc2", "o2")

        components = [cq1, cq2, dq1, dq2, func, source, sink, fork1, fork2, cjoin1, cjoin2, switch, merge, del, cc1, cc2]
        channels = [i0, i1, i2, o0, o1, o2, source_cjoin1, cq1_cjoin_1, cjoin1_merge, function_cjoin2, cq2_cjoin2, cjoin2_merge, delay_function, switch_dq1, dq1_fork1, fork1_cc1, fork1_delay, switch_dq2, dq2_fork2, fork2_cc2, fork2_sink]
        ports :: [(Text, Text)]
        ports = [cq1_i, cq1_o, cq2_i, cq2_o, dq1_i, dq1_o, dq2_i, dq2_o, function_i, function_o, source_o, sink_i, fork1_i, fork1_o0, fork1_o1, fork2_i, fork2_o0, fork2_o1, cjoin1_i0, cjoin1_i1, cjoin1_o, cjoin2_i0, cjoin2_i1, cjoin2_o, switch_i, switch_o0, switch_o1, merge_i0, merge_i1, merge_o, delay_i, delay_o, cc1_i, cc1_o, cc2_i, cc2_o]

agent_interface :: [Text]
agent_interface = ["i0", "i1", "i2", "o0", "o1", "o2"]

-- | Network consisting of two agents and a fabric. @two_agents dataSize creditSize fabricSize@ produces a network where:
-- 1. The queues in the agents have size @dataSize@.
-- 2. The credit counters in the agents have size @creditSize@.
-- 3. The queues in the fabric have size @fabricSize@.
two_agents :: Int -> Int -> Int -> MadlNetwork
two_agents dataSize creditSize fabricSize = mkNetwork (NSpec components channels ports)
    where
        agentP = M MacroInstance{ instanceName = "agentP", instanceMacro = agent dataSize creditSize}
        agentQ = M MacroInstance{ instanceName = "agentQ", instanceMacro = agent dataSize creditSize}
        fabricPQ = M MacroInstance{ instanceName = "fabric", instanceMacro = fabric fabricSize}

        agentP_o0_fabric_i0 = Channel{ channelName = "agentP_o0_fabric_i0"}
        agentP_o1_fabric_i4 = Channel{ channelName = "agentP_o1_fabric_i4"}
        agentP_o2_fabric_i5 = Channel{ channelName = "agentP_o2_fabric_i5"}
        agentQ_o0_fabric_i3 = Channel{ channelName = "agentQ_o0_fabric_i3"}
        agentQ_o1_fabric_i1 = Channel{ channelName = "agentQ_o1_fabric_i1"}
        agentQ_o2_fabric_i2 = Channel{ channelName = "agentQ_o2_fabric_i2"}
        fabric_o0_agentQ_i0 = Channel{ channelName = "fabric_o0_agentQ_i0"}
        fabric_o1_agentP_i1 = Channel{ channelName = "fabric_o1_agentP_i1"}
        fabric_o2_agentP_i2 = Channel{ channelName = "fabric_o2_agentP_i2"}
        fabric_o3_agentP_i0 = Channel{ channelName = "fabric_o3_agentP_i0"}
        fabric_o4_agentQ_i1 = Channel{ channelName = "fabric_o4_agentQ_i1"}
        fabric_o5_agentQ_i2 = Channel{ channelName = "fabric_o5_agentQ_i2"}

        agentP_i0 = ("fabric_o3_agentP_i0", "agentP")
        agentP_i1 = ("fabric_o1_agentP_i1", "agentP")
        agentP_i2 = ("fabric_o2_agentP_i2", "agentP")
        agentP_o0 = ("agentP", "agentP_o0_fabric_i0")
        agentP_o1 = ("agentP", "agentP_o1_fabric_i4")
        agentP_o2 = ("agentP", "agentP_o2_fabric_i5")
        agentQ_i0 = ("fabric_o0_agentQ_i0", "agentQ")
        agentQ_i1 = ("fabric_o4_agentQ_i1", "agentQ")
        agentQ_i2 = ("fabric_o5_agentQ_i2", "agentQ")
        agentQ_o0 = ("agentQ", "agentQ_o0_fabric_i3")
        agentQ_o1 = ("agentQ", "agentQ_o1_fabric_i1")
        agentQ_o2 = ("agentQ", "agentQ_o2_fabric_i2")
        fabric_i0 = ("agentP_o0_fabric_i0", "fabric")
        fabric_i1 = ("agentQ_o1_fabric_i1", "fabric")
        fabric_i2 = ("agentQ_o2_fabric_i2", "fabric")
        fabric_i3 = ("agentQ_o0_fabric_i3", "fabric")
        fabric_i4 = ("agentP_o1_fabric_i4", "fabric")
        fabric_i5 = ("agentP_o2_fabric_i5", "fabric")
        fabric_o0 = ("fabric", "fabric_o0_agentQ_i0")
        fabric_o1 = ("fabric", "fabric_o1_agentP_i1")
        fabric_o2 = ("fabric", "fabric_o2_agentP_i2")
        fabric_o3 = ("fabric", "fabric_o3_agentP_i0")
        fabric_o4 = ("fabric", "fabric_o4_agentQ_i1")
        fabric_o5 = ("fabric", "fabric_o5_agentQ_i2")

        components = [agentP, agentQ, fabricPQ]
        channels = [agentP_o0_fabric_i0, agentP_o1_fabric_i4, agentP_o2_fabric_i5, agentQ_o0_fabric_i3, agentQ_o1_fabric_i1, agentQ_o2_fabric_i2, fabric_o0_agentQ_i0, fabric_o1_agentP_i1, fabric_o2_agentP_i2, fabric_o3_agentP_i0, fabric_o4_agentQ_i1, fabric_o5_agentQ_i2]
        ports :: [(Text, Text)]
        ports = [agentP_i0, agentP_i1, agentP_i2, agentP_o0, agentP_o1, agentP_o2, agentQ_i0, agentQ_i1, agentQ_i2, agentQ_o0, agentQ_o1, agentQ_o2, fabric_i0, fabric_i1, fabric_i2, fabric_i3, fabric_i4, fabric_i5, fabric_o0, fabric_o1, fabric_o2, fabric_o3, fabric_o4, fabric_o5]