{-# LANGUAGE CPP, OverloadedStrings, FlexibleContexts #-}

module Main(main) where

import System.Console.GetOpt

import qualified Data.HashMap as Hash
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Utils.Executable
import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes
import Madl.Network

import Examples

-- | Error function
fileName :: Text
fileName = "m2madl.Main"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-------------------------
-- CommandLine Options
-------------------------

data CommandLineOptions = CommandLineOptions {
    optOut :: String,
    argNetwork :: Text
}

defaultOptions :: CommandLineOptions
defaultOptions = CommandLineOptions {
    optOut = "out.madl",
    argNetwork = ""
}

exeOptions :: [OptDescr (CommandLineOptions -> CommandLineOptions)]
exeOptions =
    [ Option "o" ["out"]
        (ReqArg (\o opts -> opts {optOut = o}) "OUTFILE")
        "Verilog output file name (default is 'out.madl')."
    , Option "x" ["network"]
        (ReqArg (\x opts -> opts {argNetwork = txt x}) "MaDLNETWORK")
        "MaDL network name (mandatory)."
    ]

-------------------------
-- Main entry point
-------------------------

-- Main entry point
main :: IO ()
main = do
    cmdLine <- parseArgs exeOptions defaultOptions
    if T.null $ argNetwork cmdLine
        then ioError $ userError $ "No network provided, use -x to pick one of: "++show (Hash.keys Examples.networkMap)
        else do
            case Hash.lookup (argNetwork cmdLine) networkMap of
                Nothing -> ioError $ userError $ "Unknown network "++T.unpack (argNetwork cmdLine)++", pick one of: "++show (Hash.keys Examples.networkMap)
                Just network -> TIO.writeFile (optOut cmdLine) $ network2madl network -- Assume that each predefined network is valid.

-------------------------
-- m2madl
-------------------------

data Context = Context {
    colorSetMap  :: ColorSetMap,
    functionMap  :: FunctionMap,
    predicateMap :: PredicateMap
}
type ColorSetMap = Map ColorSet Text
type FunctionMap = Map MFunctionDisj (Text, [Text], Text)
type PredicateMap = Map MFunctionBool (Text, [Text])

emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty

addColorSet :: ColorSet -> Text -> Context -> Context
addColorSet newcolor name context = case Map.lookup newcolor $ colorSetMap context of
    Nothing -> context{colorSetMap = Map.insert newcolor (colorName name newcolor) $ colorSetMap context}
    Just _ -> context

addFunction :: [ColorSet] -> MFunctionDisj -> Text -> ColorSet -> Context -> Context
addFunction inputtypes newfunction name outputtype context = case Map.lookup newfunction $ functionMap context of
    Just{} -> context
    Nothing -> context{functionMap = Map.insert newfunction (name, inputnames, outputname) $ functionMap context, colorSetMap = colorSetMap'} where
        colorSetMap' = colorSetMap $ foldr (\(cs, n) cntxt -> addColorSet cs n cntxt) context colorsToAdd
        colorsToAdd = zip inputtypes (map ((name +++) . ("_param" +++) . showT) ([0..] :: [Int])) ++ [(outputtype, name +++ "_output")]
        inputnames = map (flip (lookupM $ src 106) colorSetMap') inputtypes
        outputname = lookupM (src 105) outputtype colorSetMap'

addPredicate ::[ColorSet] -> MFunctionBool -> Text -> Context -> Context
addPredicate inputtypes newpredicate name context = case Map.lookup newpredicate $ predicateMap context of
    Just{} -> context
    Nothing -> context{predicateMap = Map.insert newpredicate (name, inputnames) $ predicateMap context, colorSetMap = colorSetMap'} where
        colorSetMap' = colorSetMap $ foldr (\(cs, n) cntxt -> addColorSet cs n cntxt) context colorsToAdd
        colorsToAdd = zip inputtypes (map ((name +++) . ("_param" +++) . showT) ([0..] :: [Int]))
                   ++ zip (getPredicateColors newpredicate) (map ((name +++) . ("_color" +++) . showT) ([0..] :: [Int]))
        inputnames = map (flip (lookupM $ src 106) colorSetMap') inputtypes

getPredicateColors :: MFunctionBool -> [ColorSet]
getPredicateColors = getBoolColors where
    getBoolColors bool = case bool of
        XCompare _ val1 val2 -> getValColors val1 ++ getValColors val2
        XMatch disj1 disj2 -> getDisjColors disj1 ++ getDisjColors disj2
        XTrue -> []
        XFalse -> []
        XUnOpBool _ bool1 -> getBoolColors bool1
        XBinOpBool _ bool1 bool2 -> getBoolColors bool1 ++ getBoolColors bool2
        XAppliedToB{} -> []
        XSelectB disj boolmap -> getDisjColors disj ++ concatMap getBoolColors (Hash.elems boolmap)
        XIfThenElseB{} -> []
    getValColors val = case val of
        XConst{} -> []
        XUnOp _ val1 -> getValColors val1
        XBinOp _ val1 val2 -> getValColors val1 ++ getValColors val2
        XChooseVal _ disj -> getDisjColors disj
        XGetFieldVal _ struct -> getStructColors struct
        XIfThenElseV{} -> []
    getDisjColors disj = case disj of
        XChoice fld _ -> [constColorSet fld]
        XSelect{} -> []
        XIfThenElseD{} -> []
        XInput{} -> []
        XAppliedTo{} -> []
        XVar{} -> []
        XGetFieldDisj _ struct -> getStructColors struct
    getStructColors struct = case struct of
        XConcat{} -> []
        XChooseStruct _ disj -> getDisjColors disj
        XIfThenElseC{} -> []

getContext :: ColoredNetwork -> [Text] -> ComponentOrMacro Channel -> Context -> Context
getContext colorednet prefix component context = case component of
    M (MacroInstance name (Macro _ _ mnet)) -> foldr (getContext colorednet $ name : prefix) context (getComponents mnet)
    C (Source _ msg) -> addColorSet msg (cname +++ "_msg") context
    C (PatientSource _ msg) -> addColorSet msg (cname +++ "_msg") context
    C Sink{} -> context
    C DeadSink{} -> context
    C ControlJoin{} -> context
    C (FControlJoin _ f) -> addPredicate intypes f (cname +++ "_pred") context
    C Fork{} -> context
    C Merge{} -> context
    C (Switch _ preds) -> foldr (uncurry (addPredicate intypes)) context . zip preds $ map ((cname +++) . ("_pred" +++) . showT) ([0..]::[Int])
    C Queue{} -> context
    C Vars{} -> context
    C Cut{} -> context
    C (Function _ f _) -> addFunction intypes f (cname +++ "_fun") (head outtypes) context
    C (Match _ f) -> addPredicate (reverse intypes) f (cname +++ "_pred") context
    C (MultiMatch _ f) -> addPredicate [intypes !! length outtypes, intypes !! 0] f (cname +++ "_pred") context
    C LoadBalancer{} -> context
    C Automaton{} -> fatal 118 "unimplemented" --todo(tssb) (0) declare automaton colors.
    C (Joitch _ preds) -> foldr (uncurry (addPredicate intypes)) context . zip preds $ map ((cname +++) . ("_pred" +++) . showT) ([0..]::[Int])
    C (GuardQueue{}) -> context
    where
        intypes = inputTypes colorednet node
        outtypes = outputTypes colorednet node
        node = fromMaybe (fatal 163 $ "component not found: " +++ cname) $ findComponentID colorednet cname
        cname = T.intercalate "_" . reverse $ getName component : prefix

network2madl :: MadlNetwork -> Text
network2madl network = T.unlines $ paragraphs [
        colordeclarations,
        functiondeclarations,
        predicatedeclarations,
        macrodeclarations,
        channeldeclarations,
        componentinstantiations
        ] where
    colordeclarations = paragraphs $ map (uncurry declareColorSet) (Map.assocs $ colorSetMap context)
    functiondeclarations = map (uncurry declareFunction) (Map.assocs $ functionMap context)
    predicatedeclarations = map (uncurry $ declarePredicate context) (Map.assocs $ predicateMap context)
    context = foldr (getContext colorednet []) emptyContext (getComponents network)
    channeldeclarations = map declareChannel (getChannels network)
    componentinstantiations = map (declareComponent network context) (getComponentsWithID network)
    macrodeclarations = map (declareMacro context) (getMacros network)

    colorednet :: ColoredNetwork
    colorednet = channelTypes . unflatten $ (unfoldMacros network :: FlatFlattenedNetwork)

declareChannel :: Channel -> Text
declareChannel = ("chan " +++) . (+++ ";") . getName

declareComponent :: IMadlNetwork n => TMadlNetwork n -> Context -> (ComponentID, ComponentOrMacro Channel) -> Text
declareComponent network (Context colormap functionmap predicatemap) (node, comp) = declareComponent' comptype outchans params where
    (comptype, params) = case comp of
        M (MacroInstance _ macro) -> (getName macro, inchans)
        C (Source _ msg) -> ("Source", [lookupM (src 134) msg colormap])
        C (PatientSource _ msg) -> ("PatientSource", [lookupM (src 135) msg colormap])
        C Sink{} -> ("Sink", inchans)
        C DeadSink{} -> ("DeadSink", inchans)
        C ControlJoin{} -> ("CtrlJoin", inchans)
        C (FControlJoin _ fun) -> ("FCtrlJoin", [fst (lookupM (src 140) fun predicatemap :: (Text, [Text]))] ++ inchans)
        C Fork{} -> ("Fork", inchans)
        C Merge{} -> ("Merge", inchans)
        C (Switch _ preds) -> ("Switch", inchans ++ map (\p -> fst (lookupM (src 213) p predicatemap :: (Text, [Text]))) preds)
        C (Queue _ cap ) -> ("Queue", [showT cap] ++ inchans)
        C Vars{} -> ("Vars", inchans)
        C Cut{} -> ("Vars", inchans)
        C (Function _ fun _) -> ("Function", [fst3 (lookupM (src 156) fun functionmap :: (Text, [Text], Text))] ++ inchans)
        C (Match _ fun) -> ("Match", [fst (lookupM (src 157) fun predicatemap :: (Text, [Text]))] ++ inchans)
        C (MultiMatch _ fun) -> ("MultiMatch", [fst (lookupM (src 158) fun predicatemap :: (Text, [Text]))] ++ inchans)
        C LoadBalancer{} -> ("LoadBalancer", inchans)
        C Automaton{} -> fatal 138 "unimplemented" -- TODO(tssb, snnw, wgrw) (0) Add automata to madl language. (and parser)
        C (Joitch _ preds) -> ("Joitch", inchans ++ map (\p -> fst (lookupM (src 213) p predicatemap :: (Text, [Text]))) preds)
        C (GuardQueue _ cap) -> ("GuardQueue", [showT cap]++inchans)
    inchans = map (getName . (getChannel network)) (getInChannels network node)
    outchans = map (getName . (getChannel network)) (getOutChannels network node)

declareComponent' :: Text -> [Text] -> [Text] -> Text
declareComponent' comptype outchans params = if null outchans then
    T.unwords [comptype +++ params' +++ ";"] else
    T.unwords ["let", out', ":=", comptype +++ params' +++ ";"] where
        out' = T.intercalate ", " outchans
        params' = "(" +++ T.intercalate ", " params +++ ")"

declareMacro :: Context -> Macro Channel -> Text
declareMacro context macro = T.unlines $
       header
    ++ indent body
    ++ ["};"] where
        header = [T.unwords ["macro", getName macro +++ "(" +++ inchans +++ ")", "=>", outchans, "{"]]
        inchans = T.intercalate ", " $ map (("chan " +++) . getName . (getChannel network)) inInterface
        outchans = T.intercalate ", " $ map (("chan " +++) . getName . (getChannel network)) outInterface
        (inInterface, outInterface) = splitInterface macro
        network = macroNetwork macro

        body = channeldeclarations ++ [""] ++ componentinstantiations
        channeldeclarations = map declareChannel (map snd $ filter ((`notElem` macroInterface macro) . fst) $ getChannelsWithID network)
        componentinstantiations = map (declareComponent network context) (getComponentsWithID network)

declareColorSet :: ColorSet -> Text -> [Text]
declareColorSet cs name
    | isConstant cs = ["const " +++ (head $ colorSetKeys cs) +++ ";"]
    | isEnum cs = T.unwords["enum",name,"{"] : indent (map (+++";") $ colorSetKeys cs) ++ ["};"]
    | otherwise = T.unwords["union",name,"{"] : indent (concatMap (uncurry declareField) $ colorSetAssocs cs) ++ ["};"] where
        declareField k (Left struct) = declareStruct k struct
        declareField k (Right bv) = declareBitVector k bv

declareStruct :: Text -> Struct -> [Text]
declareStruct key struct
    | emptyStruct struct = [T.unwords [key, ":", "struct{};"]]
    | otherwise = T.unwords [key, ":", "struct", "{"] : indents (concatMap (uncurry declareField) $ structAssocs struct) ++ indent ["};"] where
        declareField k (Left cs) = declareDisjunction k cs
        declareField k (Right bv) = declareBitVector k bv

declareDisjunction :: Text -> ColorSet -> [Text]
declareDisjunction key cs
    | emptyColorSet cs = [T.unwords [key, ":", "union{};"]]
    | otherwise = T.unwords [key, ":", "union", "{"] : indents (concatMap (uncurry declareField) $ colorSetAssocs cs) ++ indent ["};"] where
        declareField k (Left struct) = declareStruct k struct
        declareField k (Right bv) = declareBitVector k bv

declareBitVector :: Text -> BitVector -> [Text]
declareBitVector key bv = [T.unwords [key, ":", "[" +++ showT (bvSize bv-1) +++ ":0];"]]

colorName :: Text -> ColorSet -> Text
colorName name cs
    | isConstant cs = head $ colorSetKeys cs
    | otherwise = name

declarePredicate :: Context -> MFunctionBool -> (Text, [Text]) -> Text
declarePredicate context predicate (name, inputtypes) = T.unlines $
       header
    ++ indent [boolToBody predicate]
    ++ ["};"] where
        header = [T.unwords ["pred", name +++ "(" +++ params +++ ")", "{"]]
        params = T.intercalate ", " . map (uncurry getParam) $ zip [0..] inputtypes
        getParam :: Int -> Text -> Text
        getParam i t = T.unwords["var" +++ showT i, ":", t]

        boolToBody boolean = case boolean of
            XCompare op val1 val2 -> T.unwords[valToBody val1, op', valToBody val2] where
                op' = case op of Eq -> "=="; Gt -> ">";
            XMatch disj1 disj2 -> T.unwords [disjToBody disj1, "==", disjToBody disj2]
            XTrue -> "true"
            XFalse -> "false"
            XUnOpBool op bool1 -> T.unwords[op', boolToBody bool1] where
                op' = case op of Not -> "!";
            XBinOpBool op bool1 bool2 -> T.unwords[boolToBody bool1, op', boolToBody bool2] where
                op' = case op of Or ->  "||"; And -> "&&";
            XAppliedToB{} -> fatal 232 "XAppliedToB not allowed"
            XSelectB disj boolmap -> T.unwords ["switch", disjToBody disj, "{", T.concat . map (uncurry getCase) $ Hash.assocs boolmap, "}"] where
                getCase key bool = T.unwords["case", key, ":", boolToBody bool, ";"]
            XIfThenElseB bool true false -> T.unwords["if", "(", boolToBody bool, ")", "{", boolToBody true, "}", "else", "{", boolToBody false, "}"]

        valToBody val = case val of
            XConst val1 -> showT val1
            XUnOp op val1 -> T.unwords[op', valToBody val1] where
                op' = case op of Neg -> fatal 239 "Neg not allowed";
            XBinOp op val1 val2 -> T.unwords[valToBody val1, op', valToBody val2] where
                op' = case op of Plus ->  "+"; Minus -> "-"; Mult -> "*"; Mod -> "%";
            XChooseVal fld disj -> disjToBody disj +++ "." +++ fld
            XGetFieldVal fld struct -> structToBody struct +++ "." +++ fld
            XIfThenElseV{} -> fatal 304 "XIfThenElseV not allowed"

        disjToBody disjunction = case disjunction of
            XChoice fld _ -> lookupM (src 246) (constColorSet fld) (colorSetMap context)
            XSelect{} -> fatal 247 "XSelect not allowed"
            XIfThenElseD{} -> fatal 248 "XIfThenElseD not allowed"
            XInput{} -> fatal 249 "XInput not allowed"
            XAppliedTo{} -> fatal 250 "XAppliedTo not allowed"
            XVar i -> "var" +++ showT i
            XGetFieldDisj fld struct -> structToBody struct +++ "." +++ fld

        structToBody struct = case struct of
            XConcat{} -> fatal 255 "XConcat not allowed"
            XChooseStruct fld disj -> disjToBody disj +++ "." +++ fld
            XIfThenElseC{} -> fatal 317 "XIfThenElseC not allowed"

declareFunction :: MFunctionDisj -> (Text, [Text], Text) -> Text
declareFunction func (name, inputtypes, outputtype) = T.unlines $
       header
    ++ indent [disjToBody func]
    ++ ["};"] where
        header = [T.unwords ["function", name, "(", params, ")", ":", outputtype, "{"]]
        params = T.intercalate ", " . map (uncurry getParam) $ zip [0..] inputtypes
        getParam :: Int -> Text -> Text
        getParam i t = T.unwords["var" +++ showT i, ":", t]

        boolToBody boolean = case boolean of
            XCompare op val1 val2 -> T.unwords[valToBody val1, op', valToBody val2] where
                op' = case op of Eq -> "=="; Gt -> ">";
            XMatch disj1 disj2 -> T.unwords [disjToBody disj1, "==", disjToBody disj2]
            XTrue -> "true"
            XFalse -> "false"
            XUnOpBool op bool1 -> T.unwords[op', boolToBody bool1] where
                op' = case op of Not -> "!";
            XBinOpBool op bool1 bool2 -> T.unwords[boolToBody bool1, op', boolToBody bool2] where
                op' = case op of Or ->  "||"; And -> "&&";
            XAppliedToB{} -> fatal 232 "XAppliedToB not allowed"
            XSelectB disj boolmap -> T.unwords ["switch", disjToBody disj, "{", T.concat . map (uncurry getCase) $ Hash.assocs boolmap, "}"] where
                getCase key bool = T.unwords["case", key, ":", boolToBody bool, ";"]
            XIfThenElseB bool true false -> T.unwords["if", "(", boolToBody bool, ")", "{", boolToBody true, "}", "else", "{", boolToBody false, "}"]

        valToBody val = case val of
            XConst val1 -> showT val1
            XUnOp op val1 -> T.unwords[op', valToBody val1] where
                op' = case op of Neg -> fatal 239 "Neg not allowed";
            XBinOp op val1 val2 -> T.unwords[valToBody val1, op', valToBody val2] where
                op' = case op of Plus ->  "+"; Minus -> "-"; Mult -> "*"; Mod -> "%";
            XChooseVal fld disj -> disjToBody disj +++ "." +++ fld
            XGetFieldVal fld struct -> structToBody struct +++ "." +++ fld
            XIfThenElseV bool true false -> T.unwords["if", "(", boolToBody bool, ")", "{", valToBody true, "}", "else", "{", valToBody false, "}"]

        disjToBody disjunction = case disjunction of
            XChoice fld structOrVal -> T.unwords [fld, "{", either structToBody valToBody structOrVal, "}"]
            XSelect disj cases -> T.unwords ["switch", disjToBody disj, "{", T.concat . map (uncurry getCase) $ Hash.assocs cases, "}"] where
                getCase key disj' = T.unwords["case", key, ":", disjToBody disj', ";"]
            XIfThenElseD bool true false -> T.unwords["if", "(", boolToBody bool, ")", "{", disjToBody true, "}", "else", "{", disjToBody false, "}"]
            XInput{} -> fatal 330 "XInput not allowed"
            XAppliedTo{} -> fatal 331 "XAppliedTo not allowed"
            XVar i -> "var" +++ showT i
            XGetFieldDisj fld struct -> structToBody struct +++ "." +++ fld

        structToBody struct = case struct of
            XConcat assignments -> T.concat . map (uncurry getAssignment) $ Hash.assocs assignments where
                getAssignment fld disjOrVal = T.unwords[fld, "=", either disjToBody valToBody disjOrVal, ";"]
            XChooseStruct fld disj -> disjToBody disj +++ "." +++ fld
            XIfThenElseC bool true false -> T.unwords["if", "(", boolToBody bool, ")", "{", structToBody true, "}", "else", "{", structToBody false, "}"]

indent :: [Text] -> [Text]
indent = map ("    " +++)

indents :: [Text] -> [Text]
indents = indent . indent

paragraphs :: [[Text]] -> [Text]
paragraphs = intercalate [""] . filter (not . null)