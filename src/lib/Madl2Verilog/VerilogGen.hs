{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}

{-|
Module      : Madl2Verilog.VerilogGen
Description : Verilog code generation
Copyright   : (c) Tessa Belder 2015-2016

Verilog code generation.
-}
module Madl2Verilog.VerilogGen (
    VerilogCode, indent, indents,
    Range, rSize, intersectRange, choiceRange, contentRange, disjRange, conjRange,
    choiceRangeSize, contentRangeSize, disjRangeSize,
    conjRangeSize,
    TypeEncoding(..), DisjMap, ConjMap, DisjType, ConjType,
    typeEncoding, conjEncoding, disjEncoding,
    mkParentheses,
    declareWire, declareEmptyWire, assignWire,
    declareEmptyRangedWire,
    declareRangedWire, assignRangedWire,
    declareRegister, assignRegister,
    assignBlock, assignNonBlock, declareAlwaysBlock,
    declareCaseStatement, declareCaseItem,
    declareRangedLogic, declareParams,
    declareParams2,declarePosEdgeClk,
    declareRange, 
    declareMadlChannel, declareChannel,
    VModule(..), declareModule,
    VChannelType(..),
    VModuleInstance(..), instantiateModule, instantiatePort,
    ifThen, (>.), esc, commentHeader,
    VBindModule(..), bindModule,
    SVAssertion(..), SVAssertionMode(..), svPos, svNeg, createAssertion,
    vlog_or, vlog_and, vlog_equals, vlog_not, vlog_band, vlog_bor,
    vlog_number, vlog_ite, vlog_true, vlog_false,
    vlog_comment
) where


import qualified Data.HashMap as Hash
import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T

import Utils.Concatable(IsString, (<>))
import qualified Utils.Concatable as C
import Utils.Text

import Madl.MsgTypes

import Madl2Verilog.VerilogConstants

-- Error function
fileName :: Text
fileName = "Madl2Verilog.VerilogGen"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

--------------------------------
-- TypeUtils ::
-------------------------------

-- | The size of range
rSize :: Range -> Int
rSize (l, h) = h-l

-- | Intersect two ranges
intersectRange :: Range -> Maybe Range -> Range
intersectRange r Nothing = r
intersectRange r@(l, h) (Just r'@(l', h')) = if l < rSize r' then (l + l', min h' (h + l'))
    else fatal 67 $ "Illegal intersection: " +++ showT r +++ " on " +++ showT r'

-- | Determines the range of the choicepart of a disjunction
choiceRange :: DisjMap -> Range
choiceRange dmap = if null dmap then (0, 0) else r where
    (_, r, _, _) = head $ Hash.elems dmap

-- | Determines the size of the choicepart of a disjunction
choiceRangeSize :: DisjMap -> Int
choiceRangeSize = rSize . choiceRange

-- | Determines the range of the contentpart of a disjunction
contentRange :: DisjMap -> Range
contentRange dmap = if null dmap then (0, 0) else (low, maximum high) where
    (_, (_, low), _, _) = head $ Hash.elems dmap
    high = map (\(_, _, _, (_, h)) -> h) (Hash.elems dmap)

-- | Determines the size of the contentpart of a disjunction
contentRangeSize :: DisjMap -> Int
contentRangeSize = rSize . contentRange

-- | Determines the range of a disjunction
disjRange :: DisjMap -> Range
disjRange dmap = if null dmap then (0, 0) else (low, maximum high) where
    (_, (low, _), _, _) = head $ Hash.elems dmap
    high = map (\(_, _, _, (_, h)) -> h) (Hash.elems dmap)

-- | Determines the size of a disjunction
disjRangeSize :: DisjMap -> Int
disjRangeSize = rSize . disjRange

-- | Determines the range of a conjuction
conjRange :: ConjMap -> Range
conjRange cmap = if null cmap then (0, 0) else
    (minimum (map fst fields), maximum (map snd fields)) where
        fields = map fst (Hash.elems cmap)

-- | Determines the size of a conjuction
conjRangeSize :: ConjMap -> Int
conjRangeSize = rSize . conjRange

-- | A typeencoding is a disjunction map
data TypeEncoding = TE DisjMap deriving (Show, Ord, Eq)
-- | A disjunction map maps text values to an int value, the choice range, a conjunction map and its content range
type DisjMap = Hash.Map Text DisjType
-- | Type of 'DisjMap' elements
type DisjType = (Int, Range, ConjMap, Range)
-- | A conjuction map maps text values to a range and a disjunction map
type ConjMap = Hash.Map Text ConjType
-- | Type of 'ConjMap' elements
type ConjType = (Range, TypeEncoding)

-- | Calculate the type encoding for a specific type
typeEncoding :: ColorSet -> TypeEncoding
typeEncoding cs = TE $ Hash.fromList hashlist where
    hashlist = [ (k, (i, (0, n), c, (n, h))) | (i, (k, v)) <- zip [0..] (colorSetAssocs cs), let (c, h) = either (conjEncoding n) (bitvecEncoding n) v]
    n = nrBits $ colorSetKeySize cs
-- | Calculate the encoding for a conjunction
conjEncoding :: Int -> Struct -> (ConjMap, Int)
conjEncoding low struct = (cmap, h) where
    (h, cmap) = foldr f (low, Hash.empty) (structAssocs struct)
    f :: (Text, OrBitVector ColorSet) -> (Int, ConjMap) -> (Int, ConjMap)
    f (name, msg) (low', c) = (high', Hash.insert name (range, TE djenc) c) where
        (djenc, high') = either (disjEncoding low') (bitvecEncoding low') msg
        range = (low', high')
-- | Calculate the encoding for a disjunction
disjEncoding :: Int -> ColorSet -> (DisjMap, Int)
disjEncoding low cs = (Hash.fromList (map fst hashlist), maximum (map snd hashlist)) where
    hashlist = [ ((k, (i, (low, n), cjenc, (n, h))), h) | (i, (k, v)) <- zip [0..] (colorSetAssocs cs), let (cjenc, h) = either (conjEncoding n) (bitvecEncoding n) v]
    n = low + nrBits (colorSetKeySize cs)
-- | Calculate the encoding for a bitvector
bitvecEncoding :: Int -> BitVector -> (Hash.Map Text a, Int)
bitvecEncoding low bv = (Hash.empty, low + max 1 (bvSize bv))

-------------------------------
-- Code generation ::
-------------------------------


-- | Put parentheses around text
mkParentheses :: Text -> Text
mkParentheses t = "("+++t+++")"

-- | Declare of wire of size 1, including an assignment
declareWire :: Text -> Text -> VerilogCode
declareWire name assignment = [T.unwords ["wire", esc name, "=", assignment, ";"] ]

-- | Declare of wire of size 1
declareEmptyWire :: Text -> VerilogCode
declareEmptyWire name = [T.unwords ["wire", esc name, ";"] ]

-- | Assign a wire of size 1
assignWire :: Text -> Text -> VerilogCode
assignWire name assignment = [T.unwords ["assign", esc name, "=", assignment, ";"] ]

-- | Declare a wire with a range, including an assignment
declareRangedWire :: (Text, Int) -> Range -> Text -> Text -> VerilogCode
declareRangedWire loc r name assignment = [T.unwords ["wire" +++ declareRange loc r, esc name, "=", assignment, ";"] ]

-- | Declare a wire with a range
declareEmptyRangedWire :: (Text, Int) -> Range -> Text -> VerilogCode
declareEmptyRangedWire loc r name = [T.unwords ["wire" +++ declareRange loc r, esc name, ";"] ]

-- | Assign a wire with a range
assignRangedWire :: (Text, Int) -> Range -> Text -> Text -> VerilogCode
assignRangedWire loc r name assignment = [T.unwords ["assign", esc name +++ declareRange loc r, "=", assignment, ";"] ]

-- | Declare a register with a range
declareRegister :: (Text, Int) -> Range -> Text -> VerilogCode
declareRegister loc r name = [T.unwords ["reg" +++ declareRange loc r, esc name, ";"] ]

-- | Assign a register
assignRegister :: Text -> Text -> VerilogCode
assignRegister name assignment = [T.unwords [esc name, "<= rst ? 0 :", assignment, ";"] ] -- todo (js) make rst a parameter

-- | Non-blocking assignment
assignNonBlock :: Text -> Text -> VerilogCode
assignNonBlock name assignment = [T.unwords [esc name, "<=", assignment, ";"] ] 

-- | Blocking assignment
assignBlock :: Text -> Text -> Text
assignBlock name assignment = T.unwords [esc name, "=", assignment, ";"] 

-- | Always statement
declareAlwaysBlock :: Text -> [Text] -> VerilogCode  
declareAlwaysBlock _at _body = 
    [txt "always @("+++_at+++") begin"]++
    _body++
    [txt "end"]

-- | Declare posedge clock sensivity 
declarePosEdgeClk :: Text -> Text    
declarePosEdgeClk _clk = (txt "posedge ")+++esc _clk

-- | Declare a Verilog case statement
declareCaseStatement :: Text -> [Text] -> VerilogCode
declareCaseStatement _switch _body  = 
    [txt "case ("+++_switch+++")"]
    ++
    _body
    ++
    [txt "endcase"]

-- | Declare one case item in a case statement.
-- General form:
-- <case> : begin
--    _item_body
-- end
declareCaseItem :: Text -> [Text] -> VerilogCode
declareCaseItem case_it _body = 
    [case_it+++": begin"]
    ++
    indents _body
    ++
    [txt "end"]

-- | Declare logic with a range, including an assignment
declareRangedLogic :: (Text, Int) -> Range -> Text -> Text -> VerilogCode
declareRangedLogic loc r name assignment = [T.unwords ["logic" +++ declareRange loc r, esc name, "=", assignment, ";"] ]

-- | Declare a madl channel (irdy, trdy and data wires) with a size
declareMadlChannel :: Bool -> Int -> Text -> VerilogCode
declareMadlChannel useInterface size name = if useInterface
    then [declareChannel True size name]
    else [
          declareChannel False 1    (vIrdy False name)
        , declareChannel False size (vData False name)
        , declareChannel False 1    (vTrdy False name)
        ]

-- | Declare a channel with a size
declareChannel :: Bool -> Int -> Text -> Text
declareChannel useInterface size name = if useInterface
    then T.unwords [vChannel, "#(" +++ showT size +++ ")", esc name +++ "();"]
    else if size < 2 then T.unwords ["wire", esc name, ";"]
        else T.unwords ["wire", declareRange (src 203) (0, size), esc name, ";"]

-- | Data type for verilog code generation of a module declaration
data VModule = VModule {
    vmoduleName :: Text,
    vmoduleParams :: [VParameter],
    vmoduleHasTime :: Bool,
    vmoduleHasRst :: Bool,
    vmoduleInterface :: [VInterfacePort],
    vmoduleBody :: VerilogCode
}

-- | Generate verilog code for the declaration of a module
declareModule :: Bool -> VModule -> VerilogCode
declareModule useInterface vmodule = (if null (vmoduleParams vmodule) then
       ["module " +++ esc (vmoduleName vmodule) +++ "("]
    else
       ["module " +++ esc (vmoduleName vmodule) +++ "#("]
    ++ indents (declareParams $ vmoduleParams vmodule)
    ++ indent [") ("]
    )
    ++ indent (declareInterface useInterface (vmoduleHasRst vmodule) (vmoduleHasTime vmodule) (vmoduleInterface vmodule))
    ++ indent (vmoduleBody vmodule)
    ++ ["endmodule", ""]

-- | Generate verilog code for the declaration of an interface
declareInterface :: Bool -> Bool -> Bool -> [VInterfacePort] -> VerilogCode
declareInterface useInterface hasrst hastime portlist =
       indents [T.intercalate ", " . map (declarePort useInterface) $ vDefaultInterface hasrst hastime]
    ++ indent (map ((", " +++) . declarePort useInterface) portlist)
    ++ [ ");" ]

-- | Generate verilog code for the declaration of a port
declarePort :: Bool -> VInterfacePort -> Text
declarePort useInterface port = case vinterfaceType port of
    Left Nothing -> T.unwords [direction, esc name]
    Left (Just (Left s)) -> T.unwords [direction, declareRange (src 242) (0, s), esc name]
    Left (Just (Right s)) -> T.unwords [direction, declareTextRange s, esc name]
    Right ptype -> modPortName useInterface ptype dir name
    where
        dir = vinterfaceDirection port
        direction = vDirection $ fromMaybe (fatal 189 "Wire must have direction") dir
        name = vinterfaceName port

-- | Generate verilog code for the declaration of parameters
declareParams :: [VParameter] -> VerilogCode
declareParams [] = []
declareParams ( (p, v):ps ) =
    [p' +++ " = " +++ v' +++ "," | (p', v') <- ps] ++ [p +++ " = " +++ v]

-- | Generate verilog code for the declaration of parameters
declareParams2 :: [VParameter] -> VerilogCode
declareParams2 [] = []
declareParams2 ( (p, v):ps ) =
    [p' +++ " = " +++ v' +++ "," | (p', v') <- ps] ++ [p +++ " = " +++ v +++ ";"]


-- | Data type for channel type
data VChannelType = SingleChannel | MadlData | MadlBus deriving (Show)

-- | Data type for verilog code generation of a module instantiation
data VModuleInstance = VModuleInstance {
    vinstanceModule :: Text,
    vinstancePrimitive :: Bool,
    vinstanceName :: Text,
    vinstanceParams :: [VParameter],
    vinstanceHasTime :: Bool,
    vinstanceHasRst :: Bool,
    vinstanceInterface :: [(VPortName, VChannelName, VChannelType)]
}

-- | Generate verilog code for the instantiation of a module
instantiateModule :: Bool -> VModuleInstance -> VerilogCode
instantiateModule useInterface vinstance = (
    if null $ vinstanceParams vinstance then
       [T.unwords [vinstMod, name, "("]]
    else
       [vinstMod +++ " #("]
    ++ indent (instantiateParams $ vinstanceParams vinstance)
    ++ [T.unwords [")", name, "("]]
    )
    -- ++ (instantiateInterface useInterface (vinstancePrimitive vinstance) (vinstanceHasTime vinstance) (vinstanceHasRst vinstance) (vinstanceInterface vinstance))
    ++ (instantiateInterface useInterface False (vinstanceHasTime vinstance) (vinstanceHasRst vinstance) (vinstanceInterface vinstance))
    ++ [""] where
        name = esc $ vinstanceName vinstance
        vinstMod = if False --vinstancePrimitive vinstance
            then vinstanceModule vinstance
            else esc $ vinstanceModule vinstance

-- | Generate verilog code for the instantiation of parameters
instantiateParams :: [VParameter] -> [Text]
instantiateParams [] = []
instantiateParams ( (p, v):ps ) =
    ["." +++ p' +++ "(" +++ v' +++ ")," | (p', v') <- ps] ++ ["." +++ p +++ "(" +++ v +++ ")"]

-- | Generate verilog code for the instantiation of an interface
instantiateInterface :: Bool -> Bool -> Bool -> Bool -> [(VPortName, VChannelName, VChannelType)] -> VerilogCode
instantiateInterface useInterface isPrim hastime hasrst portlist =
       indents [T.intercalate ", " $ concatMap (instantiatePort useInterface isPrim) defaultPorts]
    ++ indent (concatMap (map (", " +++) . instantiatePort useInterface isPrim) portlist)
    ++ [ ");" ] where
    defaultPorts = map ((\x -> (x, x, SingleChannel)) . vinterfaceName) $ vDefaultInterface hasrst hastime

-- | Generate verilog code for the instantiation of a port
instantiatePort :: Bool -> Bool -> (VPortName, VChannelName, VChannelType) -> VerilogCode
instantiatePort useInterface isPrim (port, channel, ctype) = if useInterface
    then ["." +++ maybeEsc port +++ "(" +++ esc channel +++ ")"]
    else case ctype of
        SingleChannel -> ["." +++ maybeEsc port +++ "(" +++ esc channel +++ ")"]
        MadlData -> ["." +++ maybeEsc (vData False port) +++ "(" +++ esc (vData False channel) +++ ")"]
        MadlBus ->  [ "." +++ maybeEsc (vIrdy False port) +++ "(" +++ esc (vIrdy False channel) +++ ")"
                    , "." +++ maybeEsc (vData False port) +++ "(" +++ esc (vData False channel) +++ ")"
                    , "." +++ maybeEsc (vTrdy False port) +++ "(" +++ esc (vTrdy False channel) +++ ")"
                    ]
    where
        maybeEsc = if isPrim then id else esc

-- | Data type for verilog code generation of a module bind
data VBindModule = VBindModule {
    vbindTargetModule :: Text,
    vbindTargetPrimitive :: Bool,
    vbindModule :: Text,
    vbindPrimitive :: Bool,
    vbindModuleName :: Text,
    vbindHasTime :: Bool,
    vbindHasRst :: Bool,
    vbindInterface :: [(VPortName, VChannelName, VChannelType)]
}

-- | Generate verilog code for a module bind
bindModule :: Bool -> VBindModule -> VerilogCode
bindModule useInterface vbind = (T.unwords
    ["bind", vbindTargetMod, vbindMod, (esc $ vbindModuleName vbind), "("]) :
    (instantiateInterface useInterface (vbindPrimitive vbind) (vbindHasTime vbind) (vbindHasRst vbind) (vbindInterface vbind))
     where
        vbindTargetMod = if vbindTargetPrimitive vbind
            then vbindTargetModule vbind
            else esc $ vbindTargetModule vbind
        vbindMod = if vbindPrimitive vbind
            then vbindModule vbind
            else esc $ vbindModule vbind

-- | Data type for system verilog code generation of a system verilog assertion
data SVAssertion = SVAssertion {
    svassertionName :: Text,
    svassertionType :: Text,
    svassertionBody :: Text,
    svassertionMode :: SVAssertionMode
}

-- | Mode of assertion
data SVAssertionMode =
      None   -- ^ No assertion
    | Assert -- ^ Assertion statement is asserted
    | Assume -- ^ Assertion statement is assumed
    deriving (Eq)

-- | Assertion/assumption on the positive edge of the clock
svPos :: SVAssertionMode -> Text
svPos None = ""
svPos Assert = svAssertionPos
svPos Assume = svAssumptionPos

-- | Assertion/assumption on the negative edge of the clock
svNeg :: SVAssertionMode -> Text
svNeg None = ""
svNeg Assert = svAssertionNeg
svNeg Assume = svAssumptionNeg

-- | Generate system verilog code for a system verilog assertion
createAssertion :: SVAssertion -> VerilogCode
createAssertion sva = case svassertionMode sva of
    None -> []
    _ -> (svassertionName sva +++ ":") :
        indent ["`" +++ svassertionType sva +++ "(" +++ svassertionBody sva +++ ");"]

-- | Generate verilog code for an if-then construction
ifThen :: Text -> Text -> Text
ifThen check value = T.unwords [check, "?", value, ": "]

-- | Generate verilog code for an if-then-else construction
vlog_ite :: Text -> Text -> Text -> Text
vlog_ite check value elsevalue = T.unwords ["(", check, "?", value, ":", elsevalue, ")"]

-- unary operators:
-- | Boolean negation operator
vlog_not :: (IsString a, Monoid a) => a -> a
vlog_not = vlog_un_operator "!"

-- | An arbitrary unary operator
vlog_un_operator :: (IsString a, Monoid a) => a -> a -> a
vlog_un_operator op arg = "(" <> op <> arg <> ")"

-- binary operators:
-- | Equality operator
vlog_equals :: (IsString a, Monoid a) => a -> a -> a
vlog_equals = vlog_bin_operator "=="

-- | An arbitrary binary operator
vlog_bin_operator :: (IsString a, Monoid a) => a -> a -> a -> a
vlog_bin_operator op arg1 arg2 = vlog_n_operator op [arg1, arg2]

-- n-ary operators:
-- | Disjunction operator
vlog_or :: (IsString a, Monoid a) => [a] -> a
vlog_or = vlog_n_operator "||"
-- | Conjunction operator
vlog_and :: (IsString a, Monoid a) => [a] -> a
vlog_and = vlog_n_operator "&&"
-- | Bitwise disjunction operator
vlog_bor :: (IsString a, Monoid a) => [a] -> a
vlog_bor = vlog_n_operator "|"
-- | Bitwise conjunction operator
vlog_band :: (IsString a, Monoid a) => [a] -> a
vlog_band = vlog_n_operator "&"

-- | Arbitrary n-ary operator
vlog_n_operator :: (IsString a, Monoid a) => a -> [a] -> a
vlog_n_operator _ [] = ""
vlog_n_operator _ [x] = x
vlog_n_operator op xs = "(" <> C.unwords (intersperse op xs) <> ")"

-- | A decimal number
vlog_number :: (IsString a, Monoid a) => Int -> Int -> a
vlog_number size val = C.show size <> "'d" <> C.show val

-- | True
vlog_true :: (IsString a, Monoid a) => a
vlog_true = vlog_number 1 1
-- | False
vlog_false :: (IsString a, Monoid a) => a
vlog_false = vlog_number 1 0

-- | A verilog comment
vlog_comment :: (IsString a, Monoid a) => a -> a
vlog_comment = ("// " <>)

-- | Creates a three-line comment header with body, or nothing if the body is empty
commentHeader :: Text -> [Text] -> [Text]
commentHeader header body = if null body
    then []
    else
        [ ""
          , "//"
          , "// " +++ header
          , "//"
        ] ++ body