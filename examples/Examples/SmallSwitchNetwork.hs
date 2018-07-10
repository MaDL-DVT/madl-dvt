{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.SmallSwitchNetwork
Description : Predefined network: ssn.
Copyright   : (c) Tessa Belder 2015.

Predefined networks: ssn. Small switch network.
-}
module Examples.SmallSwitchNetwork (ssn) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Small network containing a switch, consisting of source -\> switch -\> (sink1, sink2)
ssn :: MadlNetwork
ssn = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = reqAndRsp}
        switch =  C Switch{componentName = "switch", switching = [isReq, isRsp]}
        sink1 =  C Sink{ componentName = "sink1"}
        sink2 =  C Sink{ componentName = "sink2"}

        source_switch = Channel{ channelName = "source_switch"}
        switch_sink1 = Channel{ channelName = "switch_sink1"}
        switch_sink2 = Channel{ channelName = "switch_sink2"}

        source_o = ("source", "source_switch")
        switch_i = ("source_switch", "switch")
        switch_o0 = ("switch", "switch_sink1")
        switch_o1 = ("switch", "switch_sink2")
        sink1_i = ("switch_sink1", "sink1")
        sink2_i = ("switch_sink2", "sink2")

        components = [source, sink1, sink2, switch]
        channels = [source_switch, switch_sink1, switch_sink2]
        ports :: [(Text, Text)]
        ports = [source_o, switch_i, switch_o0, switch_o1, sink1_i, sink2_i]