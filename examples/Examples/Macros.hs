{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.Macros
Description : Defines macros for use in predefined networks.
Copyright   : (c) Tessa Belder 2015

Defines macros for use in predefined networks.
-}
module Examples.Macros (delay, cc, mswitch, singleChannel)where

import Madl.Network
import Utils.Text

import Examples.TypesAndFunctions

-- | Macro Delay: delays a packet
delay :: Macro Channel
delay = mkMacro delay_network "Delay" delay_interface

delay_network :: MadlMacroNetwork
delay_network = mkMacroNetwork (NSpec components channels ports)
    where
        fork = C Fork{ componentName = "fork"}
        sink = C Sink{componentName = "sink"}

        input = Channel{ channelName = "input"}
        output = Channel{ channelName = "output"}
        fork_sink = Channel{ channelName = "fork_sink"}

        fork_i = ("input", "fork")
        fork_o0 = ("fork", "output")
        fork_o1 = ("fork", "fork_sink")
        sink_i = ("fork_sink", "sink")

        components = [fork, sink]
        channels = [input, output, fork_sink]
        ports :: [(Text, Text)]
        ports = [fork_i, fork_o0, fork_o1, sink_i]

delay_interface :: [Text]
delay_interface = ["input", "output"]

-- | Macro Credit counter with variable size
cc :: Int -> Macro Channel
cc size = mkMacro (cc_network size) ("credit_counter" .> showT size) cc_interface

cc_network :: Int -> MadlMacroNetwork
cc_network size = mkMacroNetwork (NSpec components channels ports)
    where
        source = C PatientSource{ componentName = "source", messages = token}
        fork =  C Fork{ componentName = "fork"}
        queue =  C Queue{ componentName = "queue", capacity = size}
        cjoin = C ControlJoin{ componentName = "cjoin"}
        sink = C Sink{ componentName = "sink"}

        input = Channel{ channelName = "input"}
        output = Channel{ channelName = "output"}
        source_fork = Channel{ channelName = "source_fork"}
        fork_queue = Channel{ channelName = "fork_queue"}
        queue_cjoin = Channel{ channelName = "queue_cjoin"}
        cjoin_sink = Channel{ channelName = "cjoin_sink"}

        source_o = ("source", "source_fork")
        fork_i = ("source_fork", "fork")
        fork_o0 = ("fork", "output")
        fork_o1 = ("fork", "fork_queue")
        queue_i = ("fork_queue", "queue")
        queue_o = ("queue", "queue_cjoin")
        cjoin_i0 = ("input", "cjoin")
        cjoin_i1 = ("queue_cjoin", "cjoin")
        cjoin_o = ("cjoin", "cjoin_sink")
        sink_i = ("cjoin_sink", "sink")

        components = [source, fork, queue, cjoin, sink]
        channels = [input, output, source_fork, fork_queue, queue_cjoin, cjoin_sink]
        ports :: [(Text, Text)]
        ports = [source_o, fork_i, fork_o0, fork_o1, queue_i, queue_o, cjoin_i0, cjoin_i1, cjoin_o, sink_i]

cc_interface :: [Text]
cc_interface = ["input", "output"]

-- | Macro mswitch: Switch packets and merges them again. Takes types @req@ and @rsp@ as input.
mswitch :: Macro Channel
mswitch = mkMacro mswitch_network "mswitch" mswitch_interface

mswitch_network :: MadlMacroNetwork
mswitch_network = mkMacroNetwork (NSpec components channels ports)
    where
        switch = C Switch{ componentName = "switch", switching = [isReq, isRsp]}
        merge = C Merge{ componentName = "merge"}

        input = Channel{ channelName = "input"}
        output = Channel{ channelName = "output"}
        switch0_merge0 = Channel{ channelName = "switch0_merge0"}
        switch1_merge1 = Channel{ channelName = "switch1_merge1"}

        switch_i = ("input", "switch")
        switch_o0 = ("switch", "switch0_merge0")
        switch_o1 = ("switch", "switch1_merge1")
        merge_i0 = ("switch0_merge0", "merge")
        merge_i1 = ("switch1_merge1", "merge")
        merge_o = ("merge", "output")

        components = [switch, merge]
        channels = [input, output, switch0_merge0, switch1_merge1]
        ports :: [(Text, Text)]
        ports = [switch_i, switch_o0, switch_o1, merge_i0, merge_i1, merge_o]

mswitch_interface :: [Text]
mswitch_interface = ["input", "output"]

-- | Macro consisting of a single channel. Currently not supported, as 'unfoldMacros' fails on this macro.
singleChannel :: Macro Channel
singleChannel = mkMacro singleChannel_network "singleChannel" singleChannel_interface

singleChannel_network :: MadlMacroNetwork
singleChannel_network = mkMacroNetwork (NSpec components channels ports)
    where
        chan = Channel{channelName = "channel"}
        components = []
        channels = [chan]
        ports :: [(Text, Text)]
        ports = []

singleChannel_interface :: [Text]
singleChannel_interface = ["channel"]