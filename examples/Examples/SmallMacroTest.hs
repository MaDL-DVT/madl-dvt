{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.SmallMacroTest
Description : Predefined networks: smt, smt2, smt3, sct.
Copyright   : (c) Tessa Belder 2015.

Predefined networks: smt, smt2, smt3 en sct. Small macro test 1, 2, 3, and single channel test.
-}
module Examples.SmallMacroTest (smt, smt2, smt3, sct) where

import Madl.Network
import Examples.Macros
import Examples.TypesAndFunctions

import Utils.Text

-- | Small network containing a macro, consisting of source -\> delay -\> sink
smt :: MadlNetwork
smt = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = req}
        del =  M MacroInstance{ instanceName = "delay", instanceMacro = delay}
        -- ^ InstanceChannels are determined by mkNetwork
        sink =  C Sink{ componentName = "sink"}

        source_delay = Channel{ channelName = "source_delay"}
        delay_sink = Channel{ channelName = "delay_snk"}

        source_o = ("source", "source_delay")
        delay_i = ("source_delay", "delay")
        delay_o = ("delay", "delay_snk")
        sink_i = ("delay_snk", "sink")

        components = [source, sink, del]
        channels = [source_delay, delay_sink]
        ports :: [(Text, Text)]
        ports = [source_o, delay_i, delay_o, sink_i]

-- | Small network containing a macro, consisting of source -\> mswitch -\> sink
smt2 :: MadlNetwork
smt2 = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = req}
        msw =  M MacroInstance{ instanceName = "mswitch", instanceMacro = mswitch}
        -- ^ InstanceChannels are determined by mkNetwork
        sink =  C Sink{ componentName = "sink"}

        source_mswitch = Channel{ channelName = "source_mswitch"}
        mswitch_sink = Channel{ channelName = "mswitch_sink"}

        source_o = ("source", "source_mswitch")
        mswitch_i = ("source_mswitch", "mswitch")
        mswitch_o = ("mswitch", "mswitch_sink")
        sink_i = ("mswitch_sink", "sink")

        components = [source, sink, msw]
        channels = [source_mswitch, mswitch_sink]
        ports :: [(Text, Text)]
        ports = [source_o, mswitch_i, mswitch_o, sink_i]

-- | Small network containing two macros, consisting of source -\> switch -\> (delay1 -\> sink1, delay2 -\> sink2)
smt3 :: MadlNetwork
smt3 = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = reqAndRsp}
        switch =  C Switch{ componentName = "switch", switching = [isReq, isRsp]}
        delay1 =  M MacroInstance{ instanceName = "delay1", instanceMacro = delay}
        -- ^ InstanceChannels are determined by mkNetwork
        sink1 =  C Sink{ componentName = "sink1"}
        delay2 =  M MacroInstance{ instanceName = "delay2", instanceMacro = delay}
        -- ^ InstanceChannels are determined by mkNetwork
        sink2 =  C Sink{ componentName = "sink2"}

        source_switch = Channel{ channelName = "source_switch"}
        switch_delay1 = Channel{ channelName = "switch_delay1"}
        delay1_sink1 = Channel{ channelName = "delay1_sink1"}
        switch_delay2 = Channel{ channelName = "switch_delay2"}
        delay2_sink2 = Channel{ channelName = "delay2_sink2"}

        source_o = ("source", "source_switch")
        switch_i = ("source_switch", "switch")
        switch_o0 = ("switch", "switch_delay1")
        switch_o1 = ("switch", "switch_delay2")
        delay1_i = ("switch_delay1", "delay1")
        delay1_o = ("delay1", "delay1_sink1")
        sink1_i = ("delay1_sink1", "sink1")
        delay2_i = ("switch_delay2", "delay2")
        delay2_o = ("delay2", "delay2_sink2")
        sink2_i = ("delay2_sink2", "sink2")

        components = [source, switch, sink1, delay1, sink2, delay2]
        channels = [source_switch, switch_delay1, delay1_sink1, switch_delay2, delay2_sink2]
        ports :: [(Text, Text)]
        ports = [source_o, switch_i, switch_o0, switch_o1, delay1_i, delay1_o, sink1_i, delay2_i, delay2_o, sink2_i]

-- | SingleChannelTest: Small network containing a macro, consisting of source -\> singleChannel -\> sink
sct :: MadlNetwork
sct = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = req}
        channelMacro =  M MacroInstance{ instanceName = "channel", instanceMacro = singleChannel}
        -- ^ InstanceChannels are determined by mkNetwork
        sink =  C Sink{ componentName = "sink"}

        source_channel = Channel{ channelName = "source_channel"}
        channel_sink = Channel{ channelName = "channel_snk"}

        source_o = ("source", "source_channel")
        channel_i = ("source_channel", "channel")
        channel_o = ("channel", "channel_snk")
        sink_i = ("channel_snk", "sink")

        components = [source, sink, channelMacro]
        channels = [source_channel, channel_sink]
        ports :: [(Text, Text)]
        ports = [source_o, channel_i, channel_o, sink_i]