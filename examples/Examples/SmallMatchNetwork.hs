{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.SmallMatchNetwork
Description : Predefined network: smn.
Copyright   : (c) Tessa Belder 2015.

Predefined networks: smn. Small match network.
-}
module Examples.SmallMatchNetwork (smn) where

import Madl.MsgTypes
import Madl.Network
import Examples.TypesAndFunctions

import Utils.Text

-- | Small network containing a match, consisting of (source1, source2) -\> match -\> (sink1, sink2)
smn :: MadlNetwork
smn = mkNetwork (NSpec components channels ports)
    where
        source1 =  C Source{ componentName = "source1", messages = nul}
        source2 =  C Source{ componentName = "source2", messages = reqAndRsp}
        match =  C Match{componentName = "match", matchFunction = XMatch (XVar 0) (XVar 1)}
        sink1 =  C Sink{ componentName = "sink1"}
        sink2 =  C Sink{ componentName = "sink2"}

        source1_match = Channel{ channelName = "source1_match"}
        source2_match = Channel{ channelName = "source2_match"}
        match_sink1 = Channel{ channelName = "match_sink1"}
        match_sink2 = Channel{ channelName = "match_sink2"}

        source1_o = ("source1", "source1_match")
        source2_o = ("source2", "source2_match")
        match_i0 = ("source1_match", "match")
        match_i1 = ("source2_match", "match")
        match_o0 = ("match", "match_sink1")
        match_o1 = ("match", "match_sink2")
        sink1_i = ("match_sink1", "sink1")
        sink2_i = ("match_sink2", "sink2")

        components = [source1, source2, sink1, sink2, match]
        channels = [source1_match, source2_match, match_sink1, match_sink2]
        ports :: [(Text, Text)]
        ports = [source1_o, source2_o, match_i0, match_i1, match_o0, match_o1, sink1_i, sink2_i]