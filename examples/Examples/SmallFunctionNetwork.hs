{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.SmallFunctionNetwork
Description : Predefined network: sfn.
Copyright   : (c) Tessa Belder 2015.

Predefined network: sfn. Small function network.
-}
module Examples.SmallFunctionNetwork (sfn) where

import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Small network without macros, consisting of source -\> function -\> sink
sfn :: MadlNetwork
sfn = mkNetwork (NSpec components channels ports)
    where
        source =  C Source{ componentName = "source", messages = reqAndRspAndAD}
        func =  C Function{componentName = "function", function = aToReq, returnType = reqAndRspD}
        sink =  C Sink{ componentName = "sink"}

        source_function = Channel{ channelName = "source_function"}
        function_sink = Channel{ channelName = "function_sink"}

        source_o = ("source", "source_function")
        function_i = ("source_function", "function")
        function_o = ("function", "function_sink")
        sink_i = ("function_sink", "sink")

        components = [source, sink, func]
        channels = [source_function, function_sink]
        ports :: [(Text, Text)]
        ports = [source_o, function_i, function_o, sink_i]