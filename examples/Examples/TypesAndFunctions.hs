{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Examples.TypesAndFunctions
Description : Predefined types and functions for use in predefined networks.
Copyright   : (c) Tessa Belder 2015-2016.

Predefined types and functions for use in predefined networks.
-}
module Examples.TypesAndFunctions (
    -- * From Madl.MsgTypes:
    bitT, bitvecT,
    nul, one,
    -- * Data types
    req, rsp, aPacket,
    reqAndRsp, reqAndRspAndA,
    reqD, rspD, aPacketD,
    reqAndRspD, reqAndRspAndAD,
    dataA, dataB, 
    complex,
    reqWithAdress, req32bit, reqAndRsp',
    struct_ab_grby, struct_A_green,
    constBlue, struct_A_blue, constRed,  
    constB, struct_B_red, constYellow, struct_B_yellow,
    struct_A_blue_B_yellow, struct_A_B,
    token,
    -- * Functions
    idFunction, toToken,
    toREQ, toRSP, toA, toType,
    reqToRsp, switchReqRsp, aToReq, reqToA,
    hfunction, h',
    mkAGreen, mkGreenBlue_RedYellow,
    -- * Predicates
    sameType, isReq, isRsp, isType,
    -- * Arguments
    defaultArguments, h'args
) where

import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM

import Utils.Text

import Madl.MsgTypes

------------------------------
-- Types
------------------------------

-- | A request
req :: ColorSet
req = constColorSet "req"

-- | A response
rsp :: ColorSet
rsp = constColorSet "rsp"

-- | A token
token :: ColorSet
token = constColorSet "tok"

-- | A packet of type @a@
aPacket :: ColorSet
aPacket = constColorSet "a"

-- -- | A packet of type @green@
-- green :: ColorSet
-- green = constColorSet "green"

-- -- | A packet of type @red@
-- red :: ColorSet
-- red = constColorSet "red"

-- -- | A packet of type @blue@
-- blue :: ColorSet
-- blue = constColorSet "blue"

-- -- | A packet of type @yellow@
-- yellow :: ColorSet
-- yellow = constColorSet "yellow"


-- | Requests and responses
reqAndRsp :: ColorSet
reqAndRsp = typeUnion rsp req

-- | Requests and responses and packets of type @a@
reqAndRspAndA :: ColorSet
reqAndRspAndA = typeUnion reqAndRsp aPacket

-- | A struct with a @data@ field of 1 bit, and an @adress@ field of 2 bits
packetData :: Struct
packetData = makeBitStruct [("data", 1), ("adress", 2)]

-- | A request containing data
reqD :: ColorSet
reqD = makeColorSet [("req", Left packetData)]

-- | A response containing data
rspD :: ColorSet
rspD = makeColorSet [("rsp", Left packetData)]

-- | A packet of type @a@ containing data
aPacketD :: ColorSet
aPacketD = makeColorSet [("a", Left packetData)]

-- | Requests and repsonses containing data
reqAndRspD :: ColorSet
reqAndRspD = typeUnion rspD reqD

-- | Requests and responses and packets of type @a@ containing data
reqAndRspAndAD :: ColorSet
reqAndRspAndAD = typeUnion reqAndRspD aPacketD

-- | A packet of type @a@ containing a @data@ field of 2 bits
dataA :: ColorSet
dataA = makeColorSet [("a", Left $ makeBitStruct [("data", 2)])]

-- | A packet of type @b@ containing a @data@ field of 2 bits
dataB :: ColorSet
dataB = makeColorSet [("b", Left $ makeBitStruct [("data", 2)])]

-- | Packets of type @a@ containing the 2-bit fields @x@, @y@ and @z@,
-- and packets of type @b@ containing a @head@ field which contains an @opagueType@ field of 1 bit.
complex :: ColorSet
complex = makeColorSet [
      ("a", Left $ makeBitStruct [("x", 2), ("y", 2), ("z", 2)])
    , ("b", Left $ makeStruct [("head", Left $ makeColorSet [("", Left $ makeBitStruct [("opagueType", 1)])])])
    ]

-- | Requests containing a @data@ field of either 2 or 4 bits
reqWithAdress :: ColorSet
reqWithAdress = makeColorSet [("req", Left $ makeStruct [("data", Left dataColors)])] where
    dataColors = makeColorSet [("2bit", Right $ bitvecT 2), ("4bit", Right $ bitvecT 4)]

-- | Requests containing a 2-bit @data@ field
req32bit :: ColorSet
req32bit = makeColorSet [("req", Left $ makeStruct [("data", Left $ makeColorSet [("2bit", Right $ bitvecT 2)])])]

-- | Requests containing a 2-bit @data@ field, and responses without content
reqAndRsp' :: ColorSet
reqAndRsp' = typeUnion rsp reqWithAdress

-- | Enumeration types with values green, red, blue, and yellow
grby_t :: ColorSet
grby_t = enumColorSet ["green","red","blue","yellow"] 

-- | Enumeration type with values A and B
ab_t :: ColorSet
ab_t = enumColorSet ["A","B"]

-- | Struct type with two fields: one of @ab_t@ and the other of @grby_t@
struct_ab_grby :: ColorSet
struct_ab_grby = makeColorSet [("", 
                                Left $ makeStruct [("id",    Left ab_t),
                                                   ("color", Left grby_t)])]

-- | Constant type "A"
constA :: ColorSet
constA = constColorSet "A"

-- | Constant type "green"
constGreen :: ColorSet
constGreen = constColorSet "green"

-- | Struct type <id=A, color = green>
struct_A_green :: ColorSet
struct_A_green = makeColorSet [("", 
                                Left $ makeStruct [("id", Left constA), 
                                                   ("color", Left constGreen)])]

-- | Constant type "blue"
constBlue :: ColorSet
constBlue= constColorSet "blue"

-- | Struct type <id=A, color = blue>
struct_A_blue :: ColorSet
struct_A_blue = makeColorSet [("", 
                                Left $ makeStruct [("id", Left constA), 
                                                   ("color", Left constBlue)])]
-- | Constant type "red"
constRed :: ColorSet
constRed= constColorSet "red"

-- | Constant type "B"
constB :: ColorSet
constB = constColorSet "B"

-- | Struct type <id=B, color = red>
struct_B_red :: ColorSet
struct_B_red = makeColorSet [("", 
                                Left $ makeStruct [("id", Left constB), 
                                                   ("color", Left constRed)])]

-- | Constant type "yellow"
constYellow :: ColorSet
constYellow= constColorSet "yellow"

-- | Struct type <id=B, color = red>
struct_B_yellow :: ColorSet
struct_B_yellow = makeColorSet [("", 
                                Left $ makeStruct [("id", Left constB), 
                                                   ("color", Left constYellow)])]

-- | A, Green | blue and B, Red | Yellow
struct_A_B :: ColorSet
struct_A_B = makeColorSet 
                            [("", 
                              Left $ makeStruct [("id", Left constA), 
                                                 ("color", Left constGreen)]),
                             ("", 
                              Left $ makeStruct [("id", Left constA), 
                                                 ("color", Left constBlue)]),
                             ("", 
                              Left $ makeStruct [("id", Left constB), 
                                                 ("color", Left constRed)]),
                             ("", 
                              Left $ makeStruct [("id", Left constB), 
                                                 ("color", Left constYellow)])
                            ]

-- | A, blue and B,yellow
struct_A_blue_B_yellow :: ColorSet
struct_A_blue_B_yellow = makeColorSet 
                            [("", 
                              Left $ makeStruct [("id", Left constA), 
                                                 ("color", Left constYellow)]),
                             ("", 
                              Left $ makeStruct [("id", Left constA), 
                                                 ("color", Left constBlue)]),
                             ("", 
                              Left $ makeStruct [("id", Left constB), 
                                                 ("color", Left constYellow)])
                            ]
------------------------------
-- Functions
------------------------------

-- | The identity function
idFunction :: MFunctionDisj
idFunction = XVar 0

-- | Produces a packet of the given type without content
toType :: Text -> MFunctionDisj
toType t = XChoice t . Left $ XConcat Hash.empty

-- | Produces a token pakcet
toToken :: MFunctionDisj
toToken = toType "" -- NOTE: cannot make nul

-- | Produces a request without content
toREQ :: MFunctionDisj
toREQ = toType "req"

-- | Produces a response without content
toRSP :: MFunctionDisj
toRSP = toType "rsp"

-- | Produces a packet of type @a@ without content
toA :: MFunctionDisj
toA = toType "a"

-- | Change the type of a packet to the given type, but keep the contents
changeType :: Text -> Text -> MFunctionDisj
changeType from to = XChoice to  . Left $ XChooseStruct from (XVar 0)

-- | Transform a request to a response. Keep packet contents
reqToRsp :: MFunctionDisj
reqToRsp = XSelect (XVar 0) (Hash.fromList [("req", changeType "req" "rsp"), ("rsp", XVar 0)])

-- | Transform a request to a packet of type @a@. Keep packet contents.
reqToA :: MFunctionDisj
reqToA = XSelect (XVar 0) (Hash.fromList [("req", changeType "req" "a"), ("rsp", XVar 0)])

-- | Transform requests to responses, and responses to requests. Keep packet contents.
switchReqRsp :: MFunctionDisj
switchReqRsp = XSelect (XVar 0) (Hash.fromList [("req", changeType "req" "rsp"), ("rsp", changeType "rsp" "req")])

-- | Transform a packet of type @a@ to a request.
aToReq :: MFunctionDisj
aToReq = XSelect (XVar 0) (Hash.fromList [("a", changeType "a" "req"), ("req", XVar 0), ("rsp", XVar 0)])

-- | Merge two packets into a single packet.
hfunction :: MFunctionDisj
hfunction = XChoice "joined" . Left $ XConcat (Hash.fromList [("a", Left $ XVar 0), ("b", Left $ XVar 1)])

-- | Add the data of two packets together, and store this data in a new packet.
h':: MFunctionDisj
h'= XChoice "c" . Left . XConcat $ Hash.singleton "data" (
        Right $
        XBinOp Plus
            (XGetFieldVal "data" $ XChooseStruct "a" (XVar 0))
            (XGetFieldVal "data" $ XChooseStruct "b" (XVar 1))
    )

-- | Make a struct id<A>, color<green>
mkAGreen :: MFunctionDisj
mkAGreen = 
 XChoice "" (Left (XConcat (Hash.fromList [("id",Left (XChoice "A" (Left (XConcat (Hash.fromList []))))),
                                      ("color",Left (XChoice "green" (Left (XConcat (Hash.fromList [])))))])))


-- | Make struct by no replacing the id field but replacing red by yellow and green with blue
mkGreenBlue_RedYellow :: MFunctionDisj
mkGreenBlue_RedYellow =
    XChoice "" 
        (Left 
            (XConcat 
                (Hash.fromList 
                    [("id",
                        Left (XGetFieldDisj "id" 
                            (XChooseStruct "" (XVar 0)))),
                    ("color",
                        Left (XIfThenElseD (XMatch (XGetFieldDisj "color" 
                            (XChooseStruct "" (XVar 0))) 
                        (XChoice "green" (Left (XConcat (Hash.fromList []))))) 
                        (XChoice "blue" (Left (XConcat (Hash.fromList [])))) 
                        (XChoice "yellow" (Left (XConcat (Hash.fromList []))))))])))

------------------------------
-- Predicates
------------------------------

-- | Check if two packets have the same type (on top-level).
sameType :: MFunctionBool
sameType = XMatch (XVar 0) (XVar 1)

-- | Check if a packet is a request
isReq :: MFunctionBool
isReq = isType "req"

-- | Check if a packet is a response
isRsp :: MFunctionBool
isRsp = isType "rsp"

-- | Check if a packet is of the given type
isType :: Text -> MFunctionBool
isType t = XMatch (toType t) (XVar 0)

------------------------------
-- Arguments
------------------------------

-- | Two arguments, both of containing requests and responses
defaultArguments :: Arguments
defaultArguments = IM.fromList [(0, reqAndRsp), (1, reqAndRsp)]

-- | Arguments for the 'h'' function. Contains one packet of type @a@ and one packet of type @b@.
h'args :: Arguments
h'args = IM.fromList [(0, dataA), (1, dataB)]