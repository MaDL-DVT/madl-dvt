{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.SmallTestNetwork
Description : Predefined network: stn.
Copyright   : (c) Tessa Belder 2015.

Predefined networks: stn. Small test network.
-}
module Examples.SmallTestNetwork (stn) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Small network without macros, consisting of source -\> queue -\> sink
stn :: MadlNetwork
stn = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = req}
        queue =  C Queue{componentName = "queue", capacity = 2}
        sink =  C Sink{ componentName = "sink"}

        source_queue = Channel{ channelName = "source_queue"}
        queue_sink = Channel{ channelName = "queue_sink"}

        source_o = ("source", "source_queue")
        queue_i = ("source_queue", "queue")
        queue_o = ("queue", "queue_sink")
        sink_i = ("queue_sink", "sink")

        components = [source, sink, queue]
        channels = [source_queue, queue_sink]
        ports :: [(Text, Text)]
        ports = [source_o, queue_i, queue_o, sink_i]