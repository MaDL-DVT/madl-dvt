{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.InvariantTestNetwork
Description : Predefined networks: itn and itn2.
Copyright   : (c) Tessa Belder 2015

Predefined networks: itn and itn2. Networks to test invariant generation.
-}
module Examples.InvariantTestNetwork (itn, itn2) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Network itn. Forks messages, distributes them over a different amount of queues on both sides, and joins the messages again.
itn :: MadlNetwork
itn = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = reqAndRsp}
        fork =  C Fork{ componentName = "fork"}
        q1 =  C Queue{ componentName = "q1", capacity=2}
        q2 =  C Queue{ componentName = "q2", capacity=3}
        q3 =  C Queue{ componentName = "q3", capacity=3}
        cjoin = C ControlJoin{ componentName = "cjoin"}
        sink = C Sink{ componentName = "sink"}

        source_fork = Channel{ channelName = "source_fork"}
        fork_q1 = Channel{ channelName = "fork_q1"}
        fork_q2 = Channel{ channelName = "fork_q2"}
        q1_cjoin = Channel{ channelName = "q1_cjoin"}
        q2_q3 = Channel{ channelName = "q2_q3"}
        q3_cjoin = Channel{ channelName = "q3_cjoin"}
        cjoin_sink = Channel{ channelName = "cjoin_sink"}

        source_o = ("source", "source_fork")
        fork_i = ("source_fork", "fork")
        fork_o0 = ("fork", "fork_q1")
        fork_o1 = ("fork", "fork_q2")
        q1_i = ("fork_q1", "q1")
        q1_o = ("q1", "q1_cjoin")
        q2_i = ("fork_q2", "q2")
        q2_o = ("q2", "q2_q3")
        q3_i = ("q2_q3", "q3")
        q3_o = ("q3", "q3_cjoin")
        cjoin_i0 = ("q1_cjoin", "cjoin")
        cjoin_i1 = ("q3_cjoin", "cjoin")
        cjoin_o = ("cjoin", "cjoin_sink")
        sink_i = ("cjoin_sink", "sink")

        components = [source, fork, q1, q2, q3, cjoin, sink]
        channels = [source_fork, fork_q1, fork_q2, q1_cjoin, q2_q3, q3_cjoin, cjoin_sink]
        ports :: [(Text, Text)]
        ports = [source_o, fork_i, fork_o0, fork_o1, q1_i, q1_o, q2_i, q2_o, q3_i, q3_o, cjoin_i0, cjoin_i1, cjoin_o, sink_i]

-- | Network itn2. Tests the usage of a function component.
itn2 :: MadlNetwork
itn2 = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = reqAndRsp}
        fork =  C Fork{ componentName = "fork"}
        q1 =  C Queue{ componentName = "q1", capacity=2}
        q2 =  C Function{ componentName = "q2", function=idFunction, returnType = reqAndRsp}
        q3 =  C Queue{ componentName = "q3", capacity=3}
        cjoin = C ControlJoin{ componentName = "cjoin"}
        sink = C Sink{ componentName = "sink"}

        source_fork = Channel{ channelName = "source_fork"}
        fork_q1 = Channel{ channelName = "fork_q1"}
        fork_q2 = Channel{ channelName = "fork_q2"}
        q1_cjoin = Channel{ channelName = "q1_cjoin"}
        q2_q3 = Channel{ channelName = "q2_q3"}
        q3_cjoin = Channel{ channelName = "q3_cjoin"}
        cjoin_sink = Channel{ channelName = "cjoin_sink"}

        source_o = ("source", "source_fork")
        fork_i = ("source_fork", "fork")
        fork_o0 = ("fork", "fork_q1")
        fork_o1 = ("fork", "fork_q2")
        q1_i = ("fork_q1", "q1")
        q1_o = ("q1", "q1_cjoin")
        q2_i = ("fork_q2", "q2")
        q2_o = ("q2", "q2_q3")
        q3_i = ("q2_q3", "q3")
        q3_o = ("q3", "q3_cjoin")
        cjoin_i0 = ("q1_cjoin", "cjoin")
        cjoin_i1 = ("q3_cjoin", "cjoin")
        cjoin_o = ("cjoin", "cjoin_sink")
        sink_i = ("cjoin_sink", "sink")

        components = [source, fork, q1, q2, q3, cjoin, sink]
        channels = [source_fork, fork_q1, fork_q2, q1_cjoin, q2_q3, q3_cjoin, cjoin_sink]
        ports :: [(Text, Text)]
        ports = [source_o, fork_i, fork_o0, fork_o1, q1_i, q1_o, q2_i, q2_o, q3_i, q3_o, cjoin_i0, cjoin_i1, cjoin_o, sink_i]