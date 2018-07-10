{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.SmallAutomatonNetwork
Description : Predefined network: san.
Copyright   : (c) Tessa Belder 2016.

Predefined network: san. Small automaton network.
-}
module Examples.SmallAutomatonNetwork (san) where

import Madl.Network
import Madl.MsgTypes
import Examples.TypesAndFunctions

import Utils.Text

-- Error function
fileName :: Text
fileName = "Examples.SmallAutomatonNetwork"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function



-- | Small network containing automata.
san :: MadlNetwork
san = mkNetwork (NSpec components channels ports) where
    sourceS = C $ Source "sourceS" token
    sourceT = C $ Source "sourceT" token
    reqQ = C $ Queue "requestQ" 2
    rspQ = C $ Queue "responseQ" 2
    automatonS = C $ Automaton "automatonS" 2 1 2 transitionsS
    automatonT = C $ Automaton "automatonT" 2 1 2 transitionsT

    transitionsS = [AutomatonT 0 1 0 (fatal 28 "unimplemented") (\i _ -> i == 0) (Just 0) (fatal 29 "unimplemented") (\ _ _ -> Just (0, head $ getColors req))
        , AutomatonT 1 0 1 (fatal 30 "unimplemented") (\i _ -> i == 1) Nothing (fatal 31 "unimplemented") (\_ _ -> Nothing)]
    transitionsT = [AutomatonT 1 0 0 (fatal 32 "unimplemented") (\i _ -> i == 0) (Just 0) (fatal 33 "unimplemented") (\ _ _ -> Just (0, head $ getColors rsp))
        , AutomatonT 0 1 1 (fatal 34 "unimplemented") (\i _ -> i == 1) Nothing (fatal 35 "unimplemented") (\_ _ -> Nothing)]

    sourceS_automatonS = Channel "sourceS_automatonS"
    sourceT_automatonT = Channel "sourceT_automatonT"
    automatonS_reqQ = Channel "automatonS_requestQ"
    automatonT_rspQ = Channel "automatonT_responseQ"
    reqQ_automatonT = Channel "requestQ_automatonT"
    rspQ_automatonS = Channel "responseQ_automatonS"

    sourceS_o = ("sourceS", "sourceS_automatonS")
    sourceT_o = ("sourceT", "sourceT_automatonT")
    reqQ_i = ("automatonS_requestQ", "requestQ")
    reqQ_o = ("requestQ", "requestQ_automatonT")
    rspQ_i = ("automatonT_responseQ", "responseQ")
    rspQ_o = ("responseQ", "responseQ_automatonS")
    aS_i0 = ("sourceS_automatonS", "automatonS")
    aS_i1 = ("responseQ_automatonS", "automatonS")
    aS_o = ("automatonS", "automatonS_requestQ")
    aT_i0 = ("sourceT_automatonT", "automatonT")
    aT_i1 = ("requestQ_automatonT", "automatonT")
    aT_o = ("automatonT", "automatonT_responseQ")

    components = [sourceS, sourceT, reqQ, rspQ, automatonS, automatonT]
    channels = [sourceS_automatonS, sourceT_automatonT, automatonS_reqQ, automatonT_rspQ, reqQ_automatonT, rspQ_automatonS]
    ports :: [(Text, Text)]
    ports = [sourceS_o, sourceT_o, reqQ_i, reqQ_o, rspQ_i, rspQ_o, aS_i0, aS_i1, aS_o, aT_i0, aT_i1, aT_o]