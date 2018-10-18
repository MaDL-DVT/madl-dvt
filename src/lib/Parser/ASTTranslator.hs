{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Parser.ASTTranslator
Description : Translates madl AST to a madl network
Copyright   : (c) Wieger Wesselink 2015, Tessa Belder 2015-2016

This module translates madl AST to a madl network.
-}
module Parser.ASTTranslator (
    translateNetwork,
    NetworkSpecification, NetworkSpecificationSrc(..),
    printNetworkSpecification
    ) where

import Text.Regex.Posix

import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T

-- import Debug.Trace

import Data.Text (intercalate)
import Data.Either.Unwrap (mapBoth)
import Data.Maybe
import Data.Monoid

import Utils.Map
import Utils.Text
import Utils.Tuple

import qualified Madl.Network as M
import Madl.Network (Specification(..), SpecificationSource(..), emptySpecificationSource, getNameList)
import qualified Madl.MsgTypes as Types
import Madl.SourceInformation

import Parser.MadlAST

--------------------------------------------------------------------------------
-- Error function
--------------------------------------------------------------------------------

-- | The name of this module
fileName :: Text
fileName = "Parser.ASTTranslator"

-- | Produces an error message with the given error code
fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

-- | Pairs the module name with an error code
src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src

--------------------------------------------------------------------------------
-- NetworkSpecification
--------------------------------------------------------------------------------

-- | A madl network specification contains components, channels and ports
type NetworkSpecification = M.Specification ComponentOrMacro M.Channel Text

-- The node type of the network specification.
type ComponentOrMacro = M.ComponentOrMacro M.Channel
type Macro = M.Macro M.Channel

-- | An empty network specification
emptySpecification :: NetworkSpecification
emptySpecification = NSpec [] [] []

-- | A madl network specification paired with a specification source
data NetworkSpecificationSrc = NSpecSrc {
    networkSpecification :: NetworkSpecification,
    sourceContext :: SpecificationSource
    }

-- | An empty network specification with an empty specification source
emptySpecificationSrc :: NetworkSpecificationSrc
emptySpecificationSrc = NSpecSrc {
    networkSpecification = emptySpecification,
    sourceContext = emptySpecificationSource
    }

-- | Adds a component to a network specification
addComponents :: [(ComponentOrMacro, SourceInformation)] -> NetworkSpecificationSrc -> NetworkSpecificationSrc
addComponents comps (NSpecSrc nspec source) = NSpecSrc nspec' source' where
    nspec' = nspec{specComponents = map fst comps ++ specComponents nspec}
    source' = source{componentSource = Hash.unionWith err (Hash.fromList $ map (mapFst getNameList) comps) $ componentSource source}
    err _ _ = fatal 69 "No duplicate keys should be present"

-- | Adds channels to a network specification. The channels are specified as strings
addChannels :: [(Text, SourceInformation)] -> NetworkSpecificationSrc -> NetworkSpecificationSrc
addChannels chans (NSpecSrc nspec source) = NSpecSrc nspec' source' where
    nspec' = nspec{specChannels = map (M.Channel . fst) chans ++ specChannels nspec}
    source' = source{channelSource = Hash.unionWith err (Hash.fromList $ map (mapFst (\x -> [x])) chans) $ channelSource source}
    err _ _ = fatal 74 "No duplicate keys should be present"

-- | Adds ports to a network specification. The ports are specified as pairs of strings
addPorts :: [(Text, Text)] -> NetworkSpecificationSrc -> NetworkSpecificationSrc
addPorts ports (NSpecSrc nspec source) = NSpecSrc nspec' source where
    nspec' = nspec{specPorts = specPorts nspec ++ ports}

-- | Joins two network specifications
joinNetworkSpecifications :: NetworkSpecificationSrc -> NetworkSpecificationSrc -> NetworkSpecificationSrc
joinNetworkSpecifications (NSpecSrc nspec1 source1) (NSpecSrc nspec2 source2) = NSpecSrc nspec' source' where
    nspec' = NSpec {
        specComponents = specComponents nspec1 ++ specComponents nspec2,
        specChannels = specChannels nspec1 ++ specChannels nspec2,
        specPorts = specPorts nspec1 ++ specPorts nspec2
        }

    source' = SpecSrc {
        componentSource = Hash.unionWith err (componentSource source1) (componentSource source2),
        channelSource = Hash.unionWith err (channelSource source1) (channelSource source2)
        }

    err _ _ = fatal 92 $ "No duplicate keys should be present."

-- | Add source information for channels and components inside a macro instance to the source information
addMacroSource :: Text -> SpecificationSource -> NetworkSpecificationSrc -> NetworkSpecificationSrc
addMacroSource instancename macrosource (NSpecSrc spec source) = NSpecSrc spec source' where
    source' = SpecSrc {
        componentSource = Hash.union (componentSource source) (Hash.fromList . map (mapFst (instancename :)) $ Hash.toList comps),
        channelSource = Hash.union (channelSource source) (Hash.fromList . map (mapFst (instancename :)) $ Hash.toList chans)
    }
    comps = componentSource macrosource
    chans = channelSource macrosource

-- | Prints the components of a network specification
printComponents :: NetworkSpecification -> Text
printComponents (NSpec components _ _) = "COMPONENTS = " <> (intercalate ", " (map (M.getName) components))

-- | Prints the channels of a network specification
printChannels :: NetworkSpecification -> Text
printChannels (NSpec _ channels _) = "CHANNELS = " <> (intercalate ", " (map (M.getName) channels))

-- | Prints the ports of a network specification
printPorts :: NetworkSpecification -> Text
printPorts (NSpec _ _ ports) = ("PORTS = ") <> (intercalate (", ") (map printPort ports)) where
    printPort (source, dest) = "(" <> source <> ", " <> dest <> ")"

-- | Prints a network specification
printNetworkSpecification :: NetworkSpecification -> Text
printNetworkSpecification spec = (printComponents spec) <> " " <> (printChannels spec) <> " " <> (printPorts spec)

--------------------------------------------------------------------------------
-- Context
--------------------------------------------------------------------------------

-- | A Context consists of
--   1. a list of channel- and primitive-identifiers,
--   2. a map from busnames to either the bussize or a buschannelnames map
--   3. a map from names to colorsets
--   4. a map from names to functions
--   5. a map from names to predicates
--   6. a map from names to macros
--   7. a map from primitive names to primitive output size (for both predefined and user-defined primitives)
--   8. a map from names to int values (representing int parameters)
--   9. a map from names to functions and types (representing the input parameters of a function)
data Context = Context {
    contextIdentifiers         :: [Text],
    contextBusNames            :: Hash.Map Text (Either Int (IntMap Text)),
    contextChannelNames        :: Hash.Map Text Text,
    contextColorSets           :: Hash.Map Text Types.ColorSet,
    contextFunctions           :: Hash.Map Text (Types.MFunctionDisj, Types.ColorSet),
    contextPredicates          :: Hash.Map Text Types.MFunctionBool,
    contextMacros              :: Hash.Map Text MacroFunction,
    contextPrimitiveOutputSize :: Hash.Map Text (Maybe Int),
    contextParameters          :: Hash.Map Text Int,
    contextFunctionInput       :: Hash.Map Text (Types.MFunctionDisj, Types.ColorSet),
    contextInForLoop           :: Bool
}
instance Show Context where
    show context = unlines [
        show             $ contextIdentifiers         context,
        show             $ contextBusNames            context,
        show             $ contextChannelNames        context,
        show             $ contextColorSets           context,
        show             $ contextFunctions           context,
        show             $ contextPredicates          context,
        show . Hash.keys $ contextMacros              context,
        show             $ contextPrimitiveOutputSize context,
        show             $ contextParameters          context,
        show             $ contextFunctionInput       context,
        show             $ contextInForLoop           context
        ]

-- | Function to obtain a macro based on a context and a list of primitive expressions
type MacroFunction = Context -> [PrimitiveExpression] -> (Parser.ASTTranslator.Macro, SpecificationSource)

-- | The empty context
emptyContext :: Context
emptyContext = Context {
    contextIdentifiers         = [],
    contextBusNames            = Hash.empty,
    contextChannelNames        = Hash.empty,
    contextColorSets           = Hash.empty,
    contextFunctions           = Hash.empty,
    contextPredicates          = Hash.empty,
    contextMacros              = Hash.empty,
    contextPrimitiveOutputSize = defaultOutputSizes,
    contextParameters          = Hash.empty,
    contextFunctionInput       = Hash.empty,
    contextInForLoop           = False
}

-- | OutputSize map for predefined primitives.
defaultOutputSizes :: Hash.Map Text (Maybe Int)
defaultOutputSizes = Hash.fromList [
    ("CtrlJoin"      , Just 1),
    ("DeadSink"      , Just 0),
    ("FCtrlJoin"     , Just 1),
    ("Fork"          , Nothing),
    ("Function"      , Just 1),
    ("GuardQueue"    , Just 1),
    ("Joitch"        , Nothing),
    ("LoadBalancer"  , Nothing),
    ("Match"         , Just 2),
    ("Merge"         , Just 1),
    ("MultiMatch"    , Nothing),
    ("PatientSource" , Just 1),
    ("Queue"         , Just 1),
    ("Sink"          , Just 0),
    ("Source"        , Just 1),
    ("Switch"        , Nothing),
    ("Vars"          , Just 1),
    ("Cut"           , Just 1)
    ]

-- | Adds a busname to a context
addBusToContext :: IntegerExpression -> Text -> Context -> Context
addBusToContext size bname context = context{contextBusNames = Hash.insert bname (Left size') (contextBusNames context)} where
    size' = evaluateIntegerExpression context size

-- | Adds a busname to a context and generate channels for this bus
addBusToContextWithChannels :: Int -> Text -> Context -> (Context, [Text])
addBusToContextWithChannels size bname context = (context', cnames) where
    context' = context{
      contextIdentifiers = cnames ++ contextIdentifiers context,
      contextBusNames = Hash.insert bname (Right channelmap) (contextBusNames context)
    }
    channelmap = IM.fromList $ zip [0..] cnames
    cnames = generateIdentifiers context "channel" (toInteger size)

-- | Adds buschannels to a context
addBusChannelsToContext :: Text -> [Text] -> Context -> Context
addBusChannelsToContext bname cnames context = context{
  contextIdentifiers = cnames ++ contextIdentifiers context,
  contextBusNames = Hash.adjust addBusChannels bname (contextBusNames context)
  } where
    addBusChannels (Left _)  = Right . IM.fromList $ zip [0..] cnames
    addBusChannels (Right m) = Right . IM.union m . IM.fromList $ zip [0..] cnames

-- | Adds a channel to a context, where an identifier is generated if requested.
addChannelToContext :: Bool -> Text -> Context -> Context
addChannelToContext generate name context = context {
    contextIdentifiers = identifier:(contextIdentifiers context),
    contextChannelNames = Hash.insert name identifier (contextChannelNames context)
    } where
        identifier = if generate then generateIdentifier context (utxt name) else name

-- | Adds a component name to a context
addComponentToContext :: Text -> Context -> Context
addComponentToContext name context = context{contextIdentifiers = name:contextIdentifiers context}

-- | Adds a colorset to a context
addColorSetToContext :: Text -> Types.ColorSet -> Context -> Context
addColorSetToContext name colorset context = context{contextColorSets = Hash.insert name colorset (contextColorSets context)}

-- | Adds a function to a context
addFunctionToContext :: Text -> (Types.MFunctionDisj, Types.ColorSet) -> Context -> Context
addFunctionToContext name function context = context{contextFunctions = Hash.insert name function (contextFunctions context)}

-- | Adds a predicate to a context
addPredicateToContext :: Text -> Types.MFunctionBool -> Context -> Context
addPredicateToContext name predicate context = context{contextPredicates = Hash.insert name predicate (contextPredicates context)}

-- | Adds a macro to a context
addMacroToContext :: Text -> Maybe Int -> MacroFunction -> Context -> Context
addMacroToContext name outputsize macro context = context{
    contextMacros = Hash.insert name macro (contextMacros context),
    contextPrimitiveOutputSize = Hash.insert name outputsize (contextPrimitiveOutputSize context)
  }

-- | Adds an int parameter to a context
addIntParamToContext :: Text -> Maybe Int -> Context -> Context
addIntParamToContext name val context = context{contextParameters = Hash.alter (\_ -> val) name (contextParameters context)}

-- | Sets a list of function inputs
setFunctionInput :: [VariableDeclaration TypeExpression] -> Context -> Context
setFunctionInput inputs context = context{contextFunctionInput = Hash.fromList . map (uncurry evalInput) $ zip [0..] inputs} where
    evalInput :: Int -> VariableDeclaration TypeExpression -> (Text, (Types.MFunctionDisj, Types.ColorSet))
    evalInput i (VariableDeclaration n c) = (n, (Types.XVar i, evaluateTypeExpression context c))

-- | Sets a list of automaton state inputs
setStateInput :: [(Text, Types.Color)] -> Context -> Context
setStateInput inputs context = context{contextFunctionInput = Hash.fromList . map (uncurry evalInput) $ zip [0..] inputs} where
    evalInput :: Int -> (Text, Types.Color) -> (Text, (Types.MFunctionDisj, Types.ColorSet))
    evalInput i (n, c) = (n, (Types.XVar i, Types.toColorSet c))

-- | Adds an automaton state inputs
addStateInput :: Text -> Types.Color -> Context -> Context
addStateInput name c context = context{contextFunctionInput = Hash.insert name (Types.XVar 0, Types.toColorSet c) (contextFunctionInput context)}

--------------------------------------------------------------------------------
-- generateIdentifier
--------------------------------------------------------------------------------

-- | Returns the trailing <number> if name has the shape prefix<number>.
-- Returns 0 otherwise.
identifierIndex :: Text -> String -> Integer
identifierIndex name prefix = case List.stripPrefix prefix (utxt name) of
    Nothing -> 0
    Just postfix -> case postfix =~ ("(0|([1-9][0-9]*))$" :: String) of
        True -> read postfix :: Integer
        False -> 0

-- | Returns the maximum identifier index appearing in a list of names, with respect to a given prefix
maxIdentifierIndex :: [Text] -> String -> Integer
maxIdentifierIndex [] _ = 0
maxIdentifierIndex (x:xs) prefix = max (identifierIndex x prefix) (maxIdentifierIndex xs prefix)

-- | Returns a name that does not occur in names, and with a given prefix
-- TODO(tssb): use a map, to improve efficiency
generateIdentifier :: Context -> String -> Text
generateIdentifier context prefix = txt prefix' +++ (showT (number + 1))
    where
        number = maxIdentifierIndex (contextIdentifiers context) prefix'
        prefix' = prefix ++ "_"

-- | Returns n names that do not occur in names, and with a given prefix
-- TODO(tssb: use a map, to improve efficiency
generateIdentifiers :: Context -> String -> Integer -> [Text]
generateIdentifiers context prefix n = map ((txt prefix' +++) . showT) [number+1..number+n]
    where
        number = maxIdentifierIndex (contextIdentifiers context) prefix'
        prefix' = prefix ++ "_"

-- | Returns the identifier belonging to a specific channel in a bus
busIndexIdentifier :: Context -> Text -> IntegerExpression -> Text
busIndexIdentifier context bname i = case Hash.lookup bname (contextBusNames context) of
    Nothing -> fatal 988 $ "Busname " +++ bname +++ " was not found in context"
    Just (Left _) -> fatal 989 $ "Bus " +++ bname +++ " has not been assigned channelnames"
    Just (Right m) -> case IM.lookup i' m of
        Nothing -> fatal 991 $ "Bus " +++ bname +++ " index " +++showT i' +++ " has not been assigned a channelname"
        Just cname -> cname
    where
      i' = evaluateIntegerExpression context i

-- | Returns the identifiers of all channels in a bus
busIndexIdentifiers :: Context -> Text -> [Text]
busIndexIdentifiers context bname = case Hash.lookup bname (contextBusNames context) of
    Nothing -> fatal 999 $ "Busname " +++ bname +++ " was not found in context"
    Just (Left _) -> fatal 1000 $ "Bus " +++ bname +++ " has not been assigned channelnames"
    Just (Right m) -> IM.elems m

-- | Returns the identifier of a channel
channelIdentifier :: Context -> Text -> Text
channelIdentifier context cname = lookupM (src 354) cname (contextChannelNames context)

--------------------------------------------------------------------------------
-- Parameter
--------------------------------------------------------------------------------

-- | Returns the channel names of a parameter
paramExpression :: Parameter -> Maybe NetworkStatement
paramExpression (ChannelParameter cname)  = Just . NetworkChannelDeclaration $ ChannelDeclaration [cname]
paramExpression (BusParameter size bname) = Just . NetworkBusDeclaration $  BusDeclaration size [bname]
paramExpression (IntParameter _)          = Nothing
paramExpression (FunctionParameter _)     = Nothing

-- | Returns the channel names of a parameter
paramChannelNames :: Context -> Parameter -> [Text]
paramChannelNames _       (ChannelParameter cname) = [cname]
paramChannelNames context (BusParameter _ bname)   = busIndexIdentifiers context bname
paramChannelNames _       (IntParameter _)         = []
paramChannelNames _       (FunctionParameter _)    = []

-- | Return the number of channels declared in a parameter
paramNrChannels :: Context -> Parameter -> Int
paramNrChannels _       (ChannelParameter _)  = 1
paramNrChannels context (BusParameter size _) = evaluateIntegerExpression context size
paramNrChannels _       (IntParameter _)      = 0
paramNrChannels _       (FunctionParameter _) = 0

-- | Returns true if the parameter defines channels
isChannelParameter :: Parameter -> Bool
isChannelParameter param = case param of
    ChannelParameter{} -> True
    BusParameter{} -> True
    _ -> False

-- | Adds a parameter to the given context
paramToContext :: Context -> (Parameter, PrimitiveExpression) -> Context -> Context
paramToContext cntxt (parameter, expression) context = case (parameter, expression) of --todo(tssb) count channel/bus sizes
    (ChannelParameter{},    PrimitiveChannel{})  -> context
    (BusParameter{},        PrimitiveChannel{})  -> context
    (IntParameter param,    PrimitiveInteger i)  -> addIntParamToContext param (Just i') context where
                                                    i' = evaluateIntegerExpression cntxt i
    (FunctionParameter sig, PrimitiveFunction f) -> addFunctionToContext name  f' context where
                                                    (FunctionSignature _ name _) = sig
                                                    f' = evaluateFunctionExpression cntxt f

    (param, expr) -> fatal 1038 $ exprtype +++ " does not match " +++ paramtype where
        paramtype = case param of ChannelParameter{} -> "ChannelParameter"; BusParameter{} -> "BusParameter";
                                  IntParameter{} -> "IntParameter"; FunctionParameter{} -> "FunctionParameter"
        exprtype = case expr of PrimitiveChannel{} -> "PrimitiveChannel"; PrimitiveInteger{} -> "PrimitiveInteger";
                                PrimitiveFunction{} -> "PrimitiveFunction"; PrimitivePredicate{} -> "PrimitivePredicate";
                                PrimitiveSwitch{} -> "PrimitiveSwitchExpression"; PrimitiveType{} -> "PrimitiveType";
                                PrimitiveJoitch{} -> "PrimitiveJoitchExpression"; PrimitiveUnknown{} -> "PrimitiveUnknown"

-- | Get the name of a parameter instantiation
primitiveExpressionName :: Context -> PrimitiveExpression -> Maybe Text
primitiveExpressionName context expression = case expression of
    PrimitiveChannel{} -> Nothing
    PrimitiveInteger i -> Just . showT $ evaluateIntegerExpression context i
    PrimitiveType{} -> Nothing
    PrimitiveFunction (FunctionVariable name) -> Just name
    PrimitivePredicate{} -> Nothing
    PrimitiveJoitch{} -> Nothing
    PrimitiveSwitch{} -> Nothing
    PrimitiveUnknown name -> fatal 348 $ "Unknown expression should not be present: " +++ name

-- | Returns whether a primitive expressions represents channels
isChannelPrimitiveExpression :: PrimitiveExpression -> Bool
isChannelPrimitiveExpression expression = case expression of
    PrimitiveChannel{} -> True
    _ -> False

--------------------------------------------------------------------------------
-- Channel Variable
--------------------------------------------------------------------------------

-- | Returns the list of channels that a channelvariable refers to
channelVariableChannels :: Context -> ChannelVariable -> [Text]
channelVariableChannels context channelvar = case channelvar of
    ChannelVariable name -> [channelIdentifier context name]
    BusVariable name -> busIndexIdentifiers context name
    BusIndex name index -> [busIndexIdentifier context name index]
    UnknownVariable name -> fatal 393 $ "Unknown expression should not be present: " +++ name

--------------------------------------------------------------------------------
-- Initial context
--------------------------------------------------------------------------------

-- | Add declared channelnames and integer parameters from a networkstatement to a context
addToInitialContext :: NetworkStatement -> Context -> Context
addToInitialContext statement context = case statement of
    NetworkChannelDeclaration (ChannelDeclaration names )      -> foldr (addChannelToContext $ contextInForLoop context) context names
    NetworkChannelDeclaration (ChannelDefinition names _)      -> foldr (addChannelToContext $ contextInForLoop context) context names
    NetworkBusDeclaration     (BusDeclaration size names)      -> foldr (\name cntxt -> addBusToContext size name cntxt) context names
    NetworkBusDeclaration     (BusDefinition size name _)      -> addBusToContext size name context
    NetworkFunctionDeclaration{}                               -> context
    NetworkLetStatement{}                                      -> context
    NetworkNetworkPrimitive{}                                  -> context
    NetworkParameterDeclaration (ParameterDeclaration name e)  -> addIntParamToContext name (Just val) context where
        val = evaluateIntegerExpression context e
    NetworkMacro{}                                             -> context
    NetworkProcess{}                                           -> context
    NetworkTypeDeclaration{}                                   -> context
    NetworkForLoop{}                                           -> context
    NetworkIfThenElse (IfThenElse condition thencase elsecase) -> List.foldl' (flip addToInitialContext) context statements where
        statements = map removeSourceInfo $ case evaluateBooleanExpressionAsBool context condition of
            Just True -> thencase
            Just False -> elsecase
            Nothing -> fatal 368 "Couldn't evaluate boolean expression"
    NetworkPredicateDeclaration{}                              -> context
    NetworkIncludeStatement{}                                  -> fatal 417 "Include statement shouldn't be present"

-- | Create separate names for the channels in a bus
createBusChannels :: Context -> Context
createBusChannels context = foldr (uncurry updateBus) context (Hash.assocs $ contextBusNames context) where
    updateBus bname (Left n) cntxt = addBusChannelsToContext bname cnames cntxt where
        cnames = generateIdentifiers cntxt ("bus_"++utxt bname) (toInteger n)
    updateBus _ Right{} cntxt = cntxt -- Bus has already been assigned channelnames (i.e. it was declared in a higher scope)

-- | Extract the initial context from a list of network statements, ie. the used channelnames.
getInitialContext :: [NetworkStatement] -> Context -> Context
getInitialContext statements = createBusChannels . flip (List.foldl' (flip addToInitialContext)) statements

--------------------------------------------------------------------------------
-- Expression evaluations
--------------------------------------------------------------------------------

-- | Given a context, returns the value represented by an integer-expression
evaluateIntegerExpression :: Context -> IntegerExpression -> Int
evaluateIntegerExpression _ (IntegerNumber n) = fromIntegral n
evaluateIntegerExpression context (IntegerVariable n) = Hash.findWithDefault err n (contextParameters context) where
    err = fatal 1093 $ "Parameter " +++ n +++ " was not found in context"
evaluateIntegerExpression context (IntegerBinary op n m) = f nresult mresult where
    nresult = evaluateIntegerExpression context n
    mresult = evaluateIntegerExpression context m
    f = case op of Plus -> (+); Minus -> (-); Mult -> (*); Mod -> mod;

-- | Given a context, returns the range-size represented by a range-expression
evaluateRangeExpression :: Context -> RangeExpression -> Int
evaluateRangeExpression context (RangeExpression x y) = abs (x' - y') + 1 where
    x' = evaluateIntegerExpression context x
    y' = evaluateIntegerExpression context y

-- | Given a context, returns the colorset represented by a type-expression
evaluateTypeExpression :: Context -> TypeExpression -> Types.ColorSet
evaluateTypeExpression context (TypeVariable t) = Hash.findWithDefault err t (contextColorSets context) where
    err = fatal 369 $ "TypeVariable " +++ t +++ " was not found in context"

-- | Given a context, returns the maybe colorset represented by a type-expression
evaluateSwitchExpression :: Context -> [SwitchExpression] -> SwitchExpression -> Types.MFunctionBool
evaluateSwitchExpression context allexpressions switchexpression = case switchexpression of
    SwitchTypeExpression expr -> if Types.isConstant cs
        then Types.XMatch (Types.XVar 0) (Types.XChoice (head $ Types.colorSetKeys cs) . Left $ Types.XConcat Hash.empty)
        else fatal 411 "Only constants are allowed as switch types" where
            cs = evaluateTypeExpression context expr
    SwitchPredicate predicate -> evaluatePredicateExpression context predicate
    SwitchOtherwise -> case mapMaybe toPredicate allexpressions of
        [] -> Types.XTrue
        (p:ps) -> Types.XUnOpBool Types.Not $ foldr (Types.XBinOpBool Types.Or) p ps
        where
            toPredicate SwitchOtherwise = Nothing
            toPredicate expr = Just $ evaluateSwitchExpression context [] expr
    SwitchBooleanExpression expr -> evaluateBooleanExpression context' expr where
        context' = context{contextFunctionInput = functionInput}
        functionInput = Hash.fromList $ map (\(n, t) -> (n, (Types.XVar 0, t))) (Hash.assocs $ contextColorSets context)
    SwitchUnknown name -> fatal 526 $ "Unknown expression should not be present: " +++ name

-- | Given a context, returns the colorset or bitvector represented by an SUtype-expression
evaluateSUTypeExpressionAsDisj :: Context -> SUTypeExpression -> Types.OrBitVector Types.ColorSet
evaluateSUTypeExpressionAsDisj context = mapBoth (either id structToColorSet) id . evaluateSUTypeExpression context

-- | Given a context, returns the struct or bitvector represented by an SUtype-expression
evaluateSUTypeExpressionAsStruct :: Context -> SUTypeExpression -> Types.OrBitVector Types.Struct
evaluateSUTypeExpressionAsStruct context = mapBoth (either toStruct id) id . evaluateSUTypeExpression context

-- | Given a context, return the colorset, struct or bitvector represented by an SUtype-expression
evaluateSUTypeExpression :: Context -> SUTypeExpression -> Either (Either Types.ColorSet Types.Struct) Types.BitVector
evaluateSUTypeExpression context (SUTypeVariable t) = Left . Left $ evaluateTypeExpression context t
evaluateSUTypeExpression _       (SUTypeEnumeration values) = Left . Left $ Types.enumColorSet values
evaluateSUTypeExpression context (SUTypeUnion values) = Left . Left . Types.makeColorSet $ map fromUnion values where
    fromUnion (VariableDeclaration key val) = (key, evaluateSUTypeExpressionAsStruct context val)
evaluateSUTypeExpression context (SUTypeStruct values) = Left . Right . Types.makeStruct $ map fromStruct values where
    fromStruct (VariableDeclaration key val) = (key, evaluateSUTypeExpressionAsDisj context val)
evaluateSUTypeExpression context (SUTypeRange range) = Right . Types.bitvecT $ evaluateRangeExpression context range

-- | Given a context, return the function represented by a name
evaluateFunctionExpression :: Context -> FunctionExpression -> (Types.MFunctionDisj, Types.ColorSet)
evaluateFunctionExpression context expression = case expression of
    FunctionVariable name -> fromMaybe err $ Hash.lookup name (contextFunctions context) where
        err = fatal 1137 $ "Functionname " +++ name +++ " was not found in context"

-- | Given a context, return the predicate represented by a name
evaluatePredicateExpression :: Context -> PredicateExpression -> Types.MFunctionBool
evaluatePredicateExpression context expression = case expression of
    PredicateVariable name -> fromMaybe err $ Hash.lookup name (contextPredicates context) where
        err = fatal 1138 $ "Predicatename " +++ name +++ " was not found in context"

-- | Given a context, return the predicate represented by a name
evaluateJoitchExpression :: Context -> [JoitchExpression] -> JoitchExpression -> Types.MFunctionBool
evaluateJoitchExpression context allexpressions joitchexpression = case joitchexpression of
    JoitchPredicate predicate -> evaluatePredicateExpression context predicate
    JoitchOtherwise -> case mapMaybe toPredicate allexpressions of
        [] -> Types.XTrue
        (p:ps) -> Types.XUnOpBool Types.Not $ foldr (Types.XBinOpBool Types.Or) p ps
        where
            toPredicate JoitchOtherwise = Nothing
            toPredicate expr = Just $ evaluateJoitchExpression context [] expr

-- | Given a context, returns the macro represented by a name and a list of primitive-expressions (arguments)
evaluateMacro :: Context -> Text -> [PrimitiveExpression] -> (Parser.ASTTranslator.Macro, SpecificationSource)
evaluateMacro context name parameters = case Hash.lookup name (contextMacros context) of
    Nothing -> fatal 1142 $ "Macro or process-name " +++ name +++ " was not found in context"
    Just macrofunction -> macrofunction context parameters

-- | Given a context, return the outputsize of the primitive with the given name
evaluatePrimitiveOutputSize :: Context -> NetworkPrimitive -> Int
evaluatePrimitiveOutputSize context prim = case Hash.lookup name (contextPrimitiveOutputSize context) of
    Nothing -> fatal 1148 $ "Primitivename " +++ name +++ " was not found in context"
    Just Nothing -> fatal 1149 $ "Outputsize of primitive " +++ name +++ " is unknown"
    Just (Just n) -> n
    where
        name = getPrimitiveName prim

-- | Translate an attribute
evaluateAttribute :: Context -> Attribute -> Types.MFunction
evaluateAttribute context attribute = case attribute of
    [] -> fatal 607 $ "Empty attribute list"
    name:fieldlist -> case Hash.lookup name (contextFunctionInput context) of
        Nothing -> fatal 608 $ "Unknown name: " +++ name
        Just (mfdisj, colorset) -> resolveFields fieldlist colorset mfdisj where

            resolveFields :: Attribute -> Types.ColorSet -> Types.MFunctionDisj -> Types.MFunction
            resolveFields attr cs function = case Types.colorSetAssocs cs of
                [("", Left struct)] -> resolveFieldsStruct attr struct $ Types.XChooseStruct "" function
                [("", Right _)] -> resolveFieldsBv attr $ Types.XChooseVal "" function
                _ -> case attr of
                    [] -> Types.MFDisj function --Left function
                    (fld:flds) -> case Types.lookupKey fld cs of
                        Nothing -> fatal 471 $ "Field does not exist: " +++ fld
                        Just (Left struct) -> resolveFieldsStruct flds struct $ Types.XChooseStruct fld function
                        Just (Right _) -> resolveFieldsBv flds $ Types.XChooseVal fld function

            resolveFieldsStruct :: Attribute -> Types.Struct -> Types.MFunctionStruct -> Types.MFunction
            resolveFieldsStruct attr struct function = case Types.structAssocs struct of
                [("", Left cs)] -> resolveFields attr cs $ Types.XGetFieldDisj "" function
                [("", Right _)] -> resolveFieldsBv attr $ Types.XGetFieldVal "" function
                _ -> case attr of
                    [] -> Types.MFStruct function
                    (fld:flds) -> case Types.lookupStructKey fld struct of
                        Nothing -> fatal 472 $ "Field does not exist: " +++ fld +++" in struct: " +++showT struct
                        Just (Left cs) -> resolveFields flds cs $ Types.XGetFieldDisj fld function
                        Just (Right _) -> resolveFieldsBv flds $ Types.XGetFieldVal fld function

            resolveFieldsBv :: Attribute -> Types.MFunctionVal -> Types.MFunction
            resolveFieldsBv [] f = Types.MFVal f
            resolveFieldsBv attr _ = fatal 622 $ "Dangling fields: " +++showT attr

-- | Translate an attribute to a color, if possible
evaluateAttributeAsColor :: Context -> Attribute -> Maybe Types.Color
evaluateAttributeAsColor context attribute = case attribute of
    [] -> fatal 544 "Empty attribute list"
    name:fieldlist -> case Hash.lookup name (contextFunctionInput context) of
        Nothing -> fatal 546 $ "Unknown name: " +++ name
        Just (_, colorset) -> case Types.getColors $ resolveFields fieldlist colorset of
            [c] -> Just c
            _ -> Nothing
            where
                resolveFields :: Attribute -> Types.ColorSet -> Types.ColorSet
                resolveFields attr cs = case Types.colorSetAssocs cs of
                    [("", Left struct)] -> resolveFieldsStruct attr struct
                    [("", Right bv)] -> resolveFieldsBv attr bv
                    _ -> case attr of
                        [] -> cs
                        (fld:flds) -> case Types.lookupKey fld cs of
                            Nothing -> fatal 559 $ "Field does not exist: " +++ fld
                            Just (Left struct) -> resolveFieldsStruct flds struct
                            Just (Right bv) -> resolveFieldsBv flds bv

                resolveFieldsStruct :: Attribute -> Types.Struct -> Types.ColorSet
                resolveFieldsStruct attr struct = case Types.structAssocs struct of
                    [("", Left cs)] -> resolveFields attr cs
                    [("", Right bv)] -> resolveFieldsBv attr bv
                    _ -> case attr of
                        [] -> Types.makeColorSet [("", Left struct)]
                        (fld:flds) -> case Types.lookupStructKey fld struct of
                            Nothing -> fatal 570 $ "Field does not exist: " +++ fld
                            Just (Left cs) -> resolveFields flds cs
                            Just (Right bv) -> resolveFieldsBv flds bv

                resolveFieldsBv :: Attribute -> Types.BitVector -> Types.ColorSet
                resolveFieldsBv [] bv = Types.makeColorSet [("", Right bv)]
                resolveFieldsBv attr _ = fatal 576 $ "Dangling fields: " +++showT attr

-- | Translate an attribute to an int, if possible
evaluateAttributeAsInt :: Context -> Attribute -> Maybe Int
evaluateAttributeAsInt context attribute = case attribute of
    [] -> fatal 657 "Empty attribute list"
    name:fieldlist -> case Hash.lookup name (contextFunctionInput context) of
        Nothing -> fatal 659 $ "Unknown name: " +++ name
        Just (_, colorset) -> resolveFields fieldlist colorset
            where
                resolveFields :: Attribute -> Types.ColorSet -> Maybe Int
                resolveFields attr cs = case Types.colorSetAssocs cs of
                    [("", Left struct)] -> resolveFieldsStruct attr struct
                    [("", Right bv)] -> resolveFieldsBv attr bv
                    _ -> case attr of
                        [] -> Nothing
                        (fld:flds) -> case Types.lookupKey fld cs of
                            Nothing -> fatal 669 $ "Field does not exist: " +++ fld
                            Just (Left struct) -> resolveFieldsStruct flds struct
                            Just (Right bv) -> resolveFieldsBv flds bv

                resolveFieldsStruct :: Attribute -> Types.Struct -> Maybe Int
                resolveFieldsStruct attr struct = case Types.structAssocs struct of
                    [("", Left cs)] -> resolveFields attr cs
                    [("", Right bv)] -> resolveFieldsBv attr bv
                    _ -> case attr of
                        [] -> Nothing
                        (fld:flds) -> case Types.lookupStructKey fld struct of
                            Nothing -> fatal 680 $ "Field does not exist: " +++ fld
                            Just (Left cs) -> resolveFields flds cs
                            Just (Right bv) -> resolveFieldsBv flds bv

                resolveFieldsBv :: Attribute -> Types.BitVector -> Maybe Int
                resolveFieldsBv [] bv = case Set.toList $ Types.bvInts bv of
                    [val] -> Just val
                    _ -> Nothing
                resolveFieldsBv attr _ = fatal 686 $ "Dangling fields: " +++showT attr

-- | Given a context, returns the integer represented by a data integer-expression, if possible
evaluateDataIntegerExpressionAsInt :: Context -> DataIntegerExpression -> Maybe Int
evaluateDataIntegerExpressionAsInt context expression = case expression of
    DataIntegerBinary op x y -> case (operandX, operandY) of
        (Just valX, Just valY) -> Just $ op' valX valY
        _ -> Nothing
        where
            operandX = evaluateDataIntegerExpressionAsInt context x
            operandY = evaluateDataIntegerExpressionAsInt context y
            op' = case op of Plus -> (+); Minus -> (-); Mult -> (*); Mod -> mod;
    DataIntegerNumber val -> Just $ evaluateIntegerExpression context (IntegerNumber val)
    DataIntegerVariable name -> Just $ evaluateIntegerExpression context (IntegerVariable name)
    DataIntegerAttribute attr -> evaluateAttributeAsInt context attr
    DataIntegerUnknown name -> fatal 524 $ "Unknown expression should not be present: " +++ name

-- | Given a context, returns the MFunctionVal represented by a data integer-expression
evaluateDataIntegerExpression :: Context -> DataIntegerExpression -> Types.MFunctionVal
evaluateDataIntegerExpression context expression = case evaluateDataIntegerExpressionAsInt context expression of
    Just val -> Types.XConst val
    Nothing -> case expression of
        DataIntegerBinary op x y -> Types.XBinOp op' operandX operandY where
            operandX = evaluateDataIntegerExpression context x
            operandY = evaluateDataIntegerExpression context y
            op' = case op of Plus -> Types.Plus; Minus -> Types.Minus; Mult -> Types.Mult; Mod -> Types.Mod;
        DataIntegerNumber val -> Types.XConst $ evaluateIntegerExpression context (IntegerNumber val)
        DataIntegerVariable name -> Types.XConst $ evaluateIntegerExpression context (IntegerVariable name)
        DataIntegerAttribute attr -> case evaluateAttribute context attr of
            Types.MFVal mfval -> mfval
            _ -> fatal 502 "Attribute does not represent value"
        DataIntegerUnknown name -> fatal 526 $ "Unknown expression should not be present: " +++ name

-- | Translate a data expression to an integer, if possible
evaluateDataExpressionAsInt :: Context -> DataExpression -> Maybe Int
evaluateDataExpressionAsInt context dataexpression = case dataexpression of
    DataAttribute attr -> evaluateAttributeAsInt context attr
    DataInteger expression -> evaluateDataIntegerExpressionAsInt context expression
    DataType{} -> Nothing
    DataFunctionApplication{} -> Nothing
    DataUnknown name -> fatal 584 $ "Unknown expression should not be present: " +++ name

-- | Translate a data expression to a color, if possible
evaluateDataExpressionAsColor :: Context -> DataExpression -> Maybe Types.Color
evaluateDataExpressionAsColor context dataexpression = case dataexpression of
    DataAttribute attr -> evaluateAttributeAsColor context attr
    DataInteger{} -> Nothing
    DataType name -> case Types.getColors $ evaluateTypeExpression context name of
        [c] -> Just c
        _ -> Nothing
    DataFunctionApplication function operands -> if any isNothing operands' then Nothing
        else Just $ Types.eval (Types.makeVArguments $ catMaybes operands') mfdisj
        where
            operands' = map (evaluateDataExpressionAsColor context) operands
            (mfdisj, _) = evaluateFunctionExpression context function
    DataUnknown name -> fatal 601 $ "Unknown expression should not be present: " +++ name

-- | Translate a data expression to a colorset, if possible
evaluateDataExpressionAsColorSet :: Context -> DataExpression -> Maybe Types.ColorSet
evaluateDataExpressionAsColorSet context dataexpression = case dataexpression of
    DataAttribute attr -> fmap Types.toColorSet $ evaluateAttributeAsColor context attr
    DataInteger{} -> Nothing
    DataType name -> Just $ evaluateTypeExpression context name
    DataFunctionApplication function operands -> if any isNothing operands' then Nothing
        else Just . Types.toColorSet $ (Types.eval (Types.makeVArguments $ catMaybes operands') mfdisj :: Types.Color)
        where
            operands' = map (evaluateDataExpressionAsColor context) operands
            (mfdisj, _) = evaluateFunctionExpression context function
    DataUnknown name -> fatal 601 $ "Unknown expression should not be present: " +++ name

-- | Translate a data expression
evaluateDataExpression :: Context -> DataExpression -> Types.MFunction
evaluateDataExpression context dataexpression = case dataexpression of
    DataAttribute attribute -> evaluateAttribute context attribute
    DataInteger expression -> Types.MFVal $ evaluateDataIntegerExpression context expression
    DataType name -> Types.MFDisj $ if Types.isConstant cs then Types.XChoice val (Left $ Types.XConcat Hash.empty)
        else fatal 665 $ "Colorset is not suitable as data expression: " +++showT cs where
            cs = evaluateTypeExpression context name
            val = head $ Types.colorSetKeys cs
    DataFunctionApplication function operands -> Types.MFDisj . Types.XAppliedTo mfdisj $ map toOperand operands where
        (mfdisj, _) = evaluateFunctionExpression context function
        toOperand operand = case evaluateDataExpression context operand of
            Types.MFDisj op -> op
            Types.MFStruct (Types.XChooseStruct "" op) -> op
            Types.MFStruct op -> Types.XChoice "" $ Left op
            op -> fatal 583 $ "Data expression not suitable for function application: " +++showT op
    DataUnknown name -> fatal 526 $ "Unknown expression should not be present: " +++ name

-- | Evaluate a boolean expression as a boolean, if possible
evaluateBooleanExpressionAsBool :: Context -> BooleanExpression -> Maybe Bool
evaluateBooleanExpressionAsBool context boolexpression = case boolexpression of
    BooleanTrue -> Just True
    BooleanFalse -> Just False
    BooleanUnary op x -> case operandX of
        Just val -> Just $ op' val
        Nothing -> Nothing
        where
            operandX = evaluateBooleanExpressionAsBool context x
            op' = case op of NOT -> not;
    BooleanBinary op x y -> case (operandX, operandY) of
        (Just valX, Just valY) -> Just $ op' valX valY
        (Just valX, Nothing) -> if valX == constant then Just valX else Nothing
        (Nothing, Just valY) -> if valY == constant then Just valY else Nothing
        (Nothing, Nothing) -> Nothing
        where
            operandX = evaluateBooleanExpressionAsBool context x
            operandY = evaluateBooleanExpressionAsBool context y
            op' = case op of AND -> (&&); OR -> (||);
            constant = case op of AND -> False; OR -> True;
    BooleanComparison op x y -> case (toInt x, toInt y) of
        (Just valX, Just valY) -> Just $ op' valX valY
        _ -> case (toColor x, toColor y) of
            (Just valX, Just valY) -> Just $ op' (Types.colorKey valX) (Types.colorKey valY)
            _ -> Nothing
        where
            toInt = evaluateDataExpressionAsInt context
            toColor = evaluateDataExpressionAsColor context
            op' :: (Ord a, Eq a) => a -> a -> Bool
            op' = case op of EqualTo -> (==); NotEqualTo -> (/=); LessThan -> (<); AtMost -> (<=);
                                GreaterThan -> (>); AtLeast -> (>=);
    BooleanPredicateApplication p operands -> if any isNothing operands' then Nothing
        else Just $ Types.eval (Types.makeVArguments $ catMaybes operands') predicate
        where
            operands' = map (evaluateDataExpressionAsColor context) operands
            predicate = evaluatePredicateExpression context p

-- | Evaluate a boolean expression as an MFunctionBool
evaluateBooleanExpression :: Context -> BooleanExpression -> Types.MFunctionBool
evaluateBooleanExpression context expression = case evaluateBooleanExpressionAsBool context expression of
    Just True -> Types.XTrue
    Just False -> Types.XFalse
    Nothing -> case expression of
        BooleanTrue -> Types.XTrue
        BooleanFalse -> Types.XFalse
        BooleanUnary op x -> Types.XUnOpBool op' operandX where
            operandX = evaluateBooleanExpression context x
            op' = case op of NOT -> Types.Not;
        BooleanBinary op x y -> Types.XBinOpBool op' operandX operandY where
            operandX = evaluateBooleanExpression context x
            operandY = evaluateBooleanExpression context y
            op' = case op of AND -> Types.And; OR -> Types.Or;
        BooleanComparison op x y -> case (operandX, operandY) of
            (Types.MFDisj valX, Types.MFDisj valY) -> case op of
                EqualTo -> Types.XMatch valX valY
                _       -> fatal 524 $ "Operator not supported on colors: " +++ showT op
            (Types.MFVal valX, Types.MFVal valY) -> case op of
                EqualTo -> equals
                NotEqualTo -> booleanNot equals
                LessThan -> Types.XBinOpBool Types.And (booleanNot equals) (booleanNot morethan)
                AtMost -> booleanNot morethan
                GreaterThan -> morethan
                AtLeast -> Types.XBinOpBool Types.Or equals morethan
                where
                    equals = Types.XCompare Types.Eq valX valY
                    morethan = Types.XCompare Types.Gt valX valY
                    booleanNot = Types.XUnOpBool Types.Not
            _ -> fatal 718 "Types of operands don't match."
            where
                operandX = evaluateDataExpression context x
                operandY = evaluateDataExpression context y
        BooleanPredicateApplication predicate operands -> Types.XAppliedToB mfbool $ map toOperand operands where
            mfbool = evaluatePredicateExpression context predicate
            toOperand operand = case evaluateDataExpression context operand of
                Types.MFDisj op -> op
                Types.MFStruct (Types.XChooseStruct "" op) -> op
                Types.MFStruct op -> Types.XChoice "" $ Left op
                op -> fatal 583 $ "FunctionContent not suitable for predicate application: " +++showT op

-- | Translate a function body
evaluateFunctionBody :: Context -> FunctionBodySrc -> Types.MFunction
evaluateFunctionBody context functionbody = case removeSourceInfo functionbody of
    FunctionBodyAssignment assignments -> Types.MFStruct $ Types.XConcat (Hash.fromList structFields) where
        structFields = map (mapSnd resolveBody . splitFirstField) assignmentgroups
        assignmentgroups = List.groupBy (\(FunctionAssignment (a:_) _) (FunctionAssignment (b:_) _) -> a == b) assignments

        splitFirstField :: [FunctionAssignment] -> (Text, [FunctionAssignment])
        splitFirstField asgns@((FunctionAssignment (name:_) _):_) = (name, map removeHead asgns)
        splitFirstField asgns = fatal 616 $ "Illegal assignments: " +++ showT asgns

        resolveBody :: [FunctionAssignment] -> Types.OrMFVal Types.MFunctionDisj
        resolveBody asgns = case evaluateFunctionBody context body of
                Types.MFVal  mfval  -> Right mfval
                Types.MFDisj mfdisj -> Left  mfdisj
                Types.MFStruct mfstruct -> Left (Types.XChoice "" $ Left mfstruct)
                Types.MFBool _      -> fatal 632 "Unreachable"
            where
                body = case asgns of [FunctionAssignment [] b] -> b; asgns' -> setSourceInfo (FunctionBodyAssignment asgns') functionbody

        removeHead :: FunctionAssignment -> FunctionAssignment
        removeHead (FunctionAssignment [] _) = fatal 785 "Illegal"
        removeHead (FunctionAssignment (_:names) body) = FunctionAssignment names body

    FunctionBodySwitch (SwitchStatement swvalue swcases) -> Types.MFDisj $ Types.XSelect input swcasemap where
        input = toMFDisj $ evaluateAttribute context swvalue
        swcasemap = Hash.fromList $ map (\(SwitchCase a b) -> (a, toMFDisj $ evaluateFunctionBody context b)) swcases
    FunctionBodyTypeSelection name content -> Types.MFDisj . Types.XChoice name . Left $ mfstruct where
        mfstruct = maybe (Types.XConcat Hash.empty) (toMFStruct . evaluateFunctionBody context) content
    FunctionBodyContent content -> evaluateDataExpression context content
    FunctionBodyIfThenElse (IfThenElse condition thencase elsecase) -> case (thencase', elsecase') of
        (Types.MFVal  mf1, Types.MFVal  mf2) -> Types.MFVal  $ Types.XIfThenElseV condition' mf1 mf2
        (Types.MFDisj mf1, Types.MFDisj mf2) -> Types.MFDisj $ Types.XIfThenElseD condition' mf1 mf2
        (Types.MFStruct mf1, Types.MFStruct mf2) -> Types.MFStruct $ Types.XIfThenElseC condition' mf1 mf2
        _ -> fatal 674 "Types of then and else clauses don't match"
        where
            condition' = evaluateBooleanExpression context condition
            thencase' = evaluateFunctionBody context thencase
            elsecase' = evaluateFunctionBody context elsecase

-- | Translate a predicate body
evaluatePredicateBody :: Context -> PredicateBodySrc -> Types.MFunctionBool
evaluatePredicateBody context predicatebody = case removeSourceInfo predicatebody of
    PredicateBodyBool boolexpression -> evaluateBooleanExpression context boolexpression
    PredicateBodySwitch (SwitchStatement swvalue swcases) -> Types.XSelectB input swcasemap where
        input = toMFDisj $ evaluateAttribute context swvalue
        swcasemap = Hash.fromList $ map (\(SwitchCase a b) -> (a, evaluatePredicateBody context b)) swcases
    PredicateBodyIfThenElse (IfThenElse condition thencase elsecase) -> Types.XIfThenElseB condition' thencase' elsecase' where
        condition' = evaluateBooleanExpression context condition
        thencase' = evaluatePredicateBody context thencase
        elsecase' = evaluatePredicateBody context elsecase

--------------------------------------------------------------------------------
-- Colorset/struct and MFunction conversions
--------------------------------------------------------------------------------

-- | Convert a struct to a colorset
structToColorSet :: Types.Struct -> Types.ColorSet
structToColorSet struct = case Types.structAssocs struct of
    [("", Left cs)] -> cs
    _ -> Types.makeColorSet [("", Left struct)]

-- | Convert a colorset to a struct
toStruct :: Types.ColorSet -> Types.Struct
toStruct cs = case Types.colorSetAssocs cs of
    [("", Left struct)] -> struct
    _ -> Types.makeStruct [("", Left cs)]

-- | Transform an mfunction to an mfunctiondisj
toMFDisj :: Types.MFunction -> Types.MFunctionDisj
toMFDisj mfunction = case mfunction of
    Types.MFDisj f -> f
    Types.MFStruct f@(Types.XConcat m) -> case Hash.assocs m of
        [("", Left mfdisj)] -> mfdisj
        [("", Right mfval)] -> Types.XChoice "" $ Right mfval
        _ -> Types.XChoice "" $ Left f
    Types.MFStruct f -> Types.XChoice "" $ Left f
    Types.MFVal  f -> Types.XChoice "" $ Right f
    Types.MFBool _  -> fatal 557 $ "MFBool can not interpreted as MFDisj"

-- | Transform an mfunction to an mfunctionstruct
toMFStruct :: Types.MFunction -> Types.MFunctionStruct
toMFStruct mfunction = case mfunction of
    Types.MFDisj (Types.XChoice "" (Left f )) -> f
    Types.MFDisj (Types.XChoice "" (Right f)) -> Types.XConcat . Hash.singleton "" $ Right f
    Types.MFDisj f -> Types.XConcat . Hash.singleton "" $ Left f
    Types.MFStruct f -> f
    Types.MFVal  f -> Types.XConcat . Hash.singleton "" $ Right f
    Types.MFBool _  -> fatal 557 $ "MFBool can not interpreted as MFStruct"

--------------------------------------------------------------------------------
-- Translate a parsed Network to a NetworkSpecification
--------------------------------------------------------------------------------

-- | Get the name of a networkprimitive
getPrimitiveName :: NetworkPrimitive -> Text
getPrimitiveName ControlJoin{}                 = "CtrlJoin"
getPrimitiveName DeadSink{}                    = "DeadSink"
getPrimitiveName FControlJoin{}                = "FCtrlJoin"
getPrimitiveName Fork{}                        = "Fork"
getPrimitiveName Function{}                    = "Function"
getPrimitiveName GuardQueue{}                  = "GuardQueue"
getPrimitiveName Joitch{}                      = "Joitch"
getPrimitiveName LoadBalancer{}                = "LoadBalancer"
getPrimitiveName Match{}                       = "Match"
getPrimitiveName Merge{}                       = "Merge"
getPrimitiveName MultiMatch{}                  = "MultiMatch"
getPrimitiveName PatientSource{}               = "PatientSource"
getPrimitiveName Queue{}                       = "Queue"
getPrimitiveName Sink{}                        = "Sink"
getPrimitiveName Source{}                      = "Source"
getPrimitiveName Switch{}                      = "Switch"
getPrimitiveName Vars{}                        = "Vars"
getPrimitiveName Cut{}                         = "Cut"
getPrimitiveName (UserDefinedPrimitive name _ _ ) = name

-- | Get the list of arguments of a networkprimitive
getPrimitiveArguments :: NetworkPrimitive -> [PrimitiveExpression]
getPrimitiveArguments (ControlJoin a b _)           = [PrimitiveChannel a, PrimitiveChannel b]
getPrimitiveArguments (DeadSink i _)                = [PrimitiveChannel i]
getPrimitiveArguments (FControlJoin f a b _)        = [PrimitivePredicate f, PrimitiveChannel a, PrimitiveChannel b]
getPrimitiveArguments (Fork i _)                    = [PrimitiveChannel i]
getPrimitiveArguments (Function f i _)              = [PrimitiveFunction f, PrimitiveChannel i]
getPrimitiveArguments (GuardQueue s ib ig _)        = [PrimitiveInteger s, PrimitiveChannel ib, PrimitiveChannel ig]
getPrimitiveArguments (Joitch a b ps _)             = [PrimitiveChannel a, PrimitiveChannel b] ++ map PrimitiveJoitch ps
getPrimitiveArguments (LoadBalancer i _)            = [PrimitiveChannel i]
getPrimitiveArguments (Match f mIn dIn _)           = [PrimitivePredicate f, PrimitiveChannel mIn, PrimitiveChannel dIn]
getPrimitiveArguments (Merge a b _)                 = [PrimitiveChannel a, PrimitiveChannel b]
getPrimitiveArguments (MultiMatch f ins _)          = (PrimitivePredicate f : map PrimitiveChannel ins)
getPrimitiveArguments (PatientSource e _)           = [PrimitiveType e]
getPrimitiveArguments (Queue k i _)                 = [PrimitiveInteger k, PrimitiveChannel i]
getPrimitiveArguments (Sink i _)                    = [PrimitiveChannel i]
getPrimitiveArguments (Source e _)                  = [PrimitiveType e]
getPrimitiveArguments (Switch i sws _)              = (PrimitiveChannel i : map PrimitiveSwitch sws)
getPrimitiveArguments (Vars i _)                    = [PrimitiveChannel i]
getPrimitiveArguments (Cut i _)                     = [PrimitiveChannel i]
getPrimitiveArguments (UserDefinedPrimitive _ args _) = args

-- | Translate an argument of a network primitive, and add channels and ports
translatePrimitiveArgument :: Text -> PrimitiveExpression -> (NetworkSpecificationSrc, Context) -> (NetworkSpecificationSrc, Context)
translatePrimitiveArgument parentname expression (parentspec, parentcontext) = case expression of
    PrimitiveChannel (ChannelPrimitive primitive) -> (spec', context') where
        spec' = joinNetworkSpecifications parentspec . addChannels channelsWithSrc $ addPorts ports ispec
        -- create ports for the channels
        ports = zip (repeat iname) channels ++ zip channels (repeat parentname)
        -- create channels between the parent primitive and argument i
        channelidentifier = generateIdentifier icontext "channel"
        channelsWithSrc = zip channels $ repeat (getSourceInfo primitive)
        (context', channels) = if primitiveOutputSize == 1
            then (addChannelToContext False channelidentifier icontext, [channelidentifier])
            else addBusToContextWithChannels primitiveOutputSize channelidentifier icontext
        -- translate the argument primitive
        (iname, ispec, icontext) = translateNetworkPrimitive primitive parentcontext
        primitiveOutputSize = evaluatePrimitiveOutputSize parentcontext (removeSourceInfo primitive)
    PrimitiveChannel (ChannelId channelvar) -> (spec', parentcontext) where
        spec' = addPorts ports parentspec
        ports = map (\name -> (name, parentname)) channelnames
        channelnames = channelVariableChannels parentcontext channelvar
    PrimitiveInteger{} -> (parentspec, parentcontext)
    PrimitiveType{} -> (parentspec, parentcontext)
    PrimitiveFunction{} -> (parentspec, parentcontext)
    PrimitivePredicate{} -> (parentspec, parentcontext)
    PrimitiveJoitch{} -> (parentspec, parentcontext)
    PrimitiveSwitch{} -> (parentspec, parentcontext)
    PrimitiveUnknown name -> fatal 494 $ "Unknown expression should not be present: " +++ name

-- | Translate a list of network primitive arguments, and add channels and ports
translatePrimitiveArguments :: Text -> Context -> [PrimitiveExpression] -> (NetworkSpecificationSrc, Context)
translatePrimitiveArguments parentname parentcontext = List.foldl' (flip $ translatePrimitiveArgument parentname) initial where
    initial = (emptySpecificationSrc, parentcontext)

-- | Adds the component name of a primitive to the result
addPrimitive :: NetworkSpecificationSrc -> NetworkPrimitiveSrc -> Text -> Context -> NetworkSpecificationSrc
addPrimitive spec networkprimitiveSrc name context = addComponents [(component, srcinfo)] spec' where
    srcinfo = getSourceInfo networkprimitiveSrc
    (component, spec') = case removeSourceInfo networkprimitiveSrc of
        ControlJoin                    _ _ _      -> (M.C $ M.ControlJoin name, spec)
        DeadSink                       _ _        -> (M.C $ M.DeadSink name, spec)
        FControlJoin                   f _ _ _    -> (M.C $ M.FControlJoin name function, spec) where
                                                        function = evaluatePredicateExpression context f
        Fork                           _ _        -> (M.C $ M.Fork name, spec)
        Function                       f _ _      -> (M.C $ M.Function name function returntype, spec) where
                                                        (function, returntype) = evaluateFunctionExpression context f
        GuardQueue                     s _ _ _    -> (M.C $ M.GuardQueue name size, spec) where
                                                        size = evaluateIntegerExpression context s
        Joitch                         _ _ ps _   -> (M.C $ M.Joitch name preds, spec) where
                                                        preds = map (evaluateJoitchExpression context ps) ps
        LoadBalancer                   _ _        -> (M.C $ M.LoadBalancer name, spec)
        Match                          f _ _ _    -> (M.C $ M.Match name function, spec) where
                                                        function = evaluatePredicateExpression context f
        Merge                          _ _ _      -> (M.C $ M.Merge name, spec)
        MultiMatch                     f _ _      -> (M.C $ M.MultiMatch name function, spec) where
                                                        function = evaluatePredicateExpression context f
        PatientSource                  e _        -> (M.C $ M.PatientSource name msgtype, spec) where
                                                        msgtype = evaluateTypeExpression context e
        Queue                          k _ _      -> (M.C $ M.Queue name cap, spec) where
                                                        cap = evaluateIntegerExpression context k
        Sink                           _ _        -> (M.C $ M.Sink name, spec)
        Source                         e _        -> (M.C $ M.Source name msgtype, spec) where
                                                        msgtype = evaluateTypeExpression context e
        Switch                         _ ps _     -> (M.C $ M.Switch name swtypes, spec) where
                                                        swtypes = map (evaluateSwitchExpression context ps) ps
        Vars                           _ _        -> (M.C $ M.Vars name, spec)
        Cut                            _ _        -> (M.C $ M.Cut name, spec)
        UserDefinedPrimitive macroname parameters _ -> (M.M $ M.MacroInstance name macro, mspec) where
                                                        (macro, msource) = evaluateMacro context macroname parameters
                                                        mspec = addMacroSource name msource spec



-- | Adds the component name of a primitive to the result
getNameOfComponent :: NetworkPrimitiveSrc -> Maybe String
getNameOfComponent networkprimitiveSrc =
    case removeSourceInfo networkprimitiveSrc of
        ControlJoin   _ _ (Just l)     -> Just l
        DeadSink      _ (Just l)       -> Just l
        FControlJoin  _ _ _ (Just l)   -> Just l
        Fork          _ (Just l)       -> Just l
        Function      _ _ (Just l)     -> Just l
        Joitch        _ _ _ (Just l)   -> Just l
        LoadBalancer  _ (Just l)       -> Just l
        Match         _ _ _ (Just l)   -> Just l
        Merge         _ _ (Just l)     -> Just l 
        MultiMatch    _ _ (Just l)     -> Just l
        PatientSource _ (Just l)       -> Just l               
        Queue         _ _ (Just l)     -> Just l
        Sink          _ (Just l)       -> Just l
        Source        _ (Just l)       -> Just l        
        Switch        _ _ (Just l)     -> Just l
        Vars          _ (Just l)       -> Just l
        Cut           _ (Just l)       -> Just l
        UserDefinedPrimitive _ _ (Just l) -> Just l
        _ -> Nothing

-- | Translate a network primitive
translateNetworkPrimitive :: NetworkPrimitiveSrc -> Context -> (Text, NetworkSpecificationSrc, Context)
translateNetworkPrimitive networkprimitiveSrc context = (newname, newresult, argumentscontext) where
    newresult = addPrimitive argumentsresult networkprimitiveSrc newname argumentscontext
    (argumentsresult, argumentscontext) = translatePrimitiveArguments newname context1 $ getPrimitiveArguments networkprimitive
    networkprimitive = removeSourceInfo networkprimitiveSrc
    context1 = addComponentToContext newname context
    newname = case getNameOfComponent networkprimitiveSrc of
                Nothing -> generateIdentifier context (utxt $ getPrimitiveName networkprimitive)
                Just l -> T.pack l

-- | Dummy color to use for transitions without explicit read action.
pConstColorSet :: Types.ColorSet
pConstColorSet = Types.constColorSet "const" --Since const is a keyword, a user will never use it.
pConstColor :: Types.Color
pConstColor = head $ Types.getColors pConstColorSet

-- | A process state consists of a name of this state, and a list of argument instantiations
type PState = (Text, [Types.Color])
-- | Maps process state to identifier number
type PStateNrMap = Map PState Int
-- | A process context
data ProcessContext = PContext {
    stateSpecMap :: Map Text ProcessState, -- ^ Map from state name to state
    inputChanMap :: Map Text Int, -- ^ Map from input channel name to input channel index
    outputChanMap :: Map Text Int -- ^ Map from output channel name to output channel index
}

-- | translate a process
translateProcess :: Process -> Context -> NetworkSpecificationSrc -> NetworkSpecificationSrc
translateProcess (Process header contentsSrc) context spec = addPorts ports spec' where
    contents = map removeSourceInfo contentsSrc
    spec' = addComponents components $ addChannels channels spec
    channels = [("Source_Process", srcInfo) | needsSource]
    components = (automaton, srcInfo) : [(sourceComp, srcInfo) | needsSource]
    srcInfo = getSourceInfo header
    sourceComp = M.C $ M.Source "Source" pConstColorSet
    ports = zip inputNames (repeat "Process")
        ++ zip (repeat "Process") (concatMap (paramChannelNames context) outputs)
        ++ [("Source", "Source_Process") | needsSource] ++ [("Source_Process", "Process") | needsSource]
    inputNames = concatMap (paramChannelNames context) inputs
    outputNames = concatMap (paramChannelNames context) outputs
    MacroHeader _ inputs outputs = removeSourceInfo header

    -- | next line fills in the fields of the datastructure for automaton
    -- components. 
    automaton = M.C $ M.Automaton "Process" nrIns nrOuts n transitions stateMap
    nrIns = length $ filter (\(_, dest) -> dest == "Process") ports
    nrOuts = length $ filter (\(source, _) -> source == "Process") ports
    n = Map.size stateMap
    needsSource = any (\t -> (M.eventFunction t) (length inputNames) pConstColor) transitions
    (stateMap, transitions) = case getInitialState contents of
        Nothing -> (Map.empty, [])
        Just initialState -> getProcess context pcontext [initialState] (Map.singleton initialState 0, [])
    pcontext = PContext {
        stateSpecMap = Map.fromList $ mapMaybe getState contents,
        inputChanMap = Map.fromList $ zip (inputNames ++ ["Source_Process"]) [0..],
        outputChanMap = Map.fromList $ zip outputNames [0..]
    }
    getState (InitialState s@(State name _ _)) = Just (name, s)
    getState (ContentState s@(State name _ _)) = Just (name, s)

-- | get the initial state from a process
getInitialState :: [ProcessContent] -> Maybe PState
getInitialState contents = case mapMaybe (\c -> case c of InitialState s -> Just s; _ -> Nothing) contents of
    [] -> Nothing
    [s] -> toOutput s
    _ -> fatal 992 "Only one initial state allowed"
    where
        toOutput (State name [] _) = Just (name, [])
        toOutput _ = fatal 995 "InitialState is not allowed to have parameters."

-- | A process specification consists of a stateNrMap and a list of transitions
type ProcessSpecification = (PStateNrMap, [M.AutomatonTransition])
-- | update a process specification with a list of states.
getProcess :: Context -> ProcessContext -> [PState] -> ProcessSpecification -> ProcessSpecification
getProcess _ _ [] process = process
getProcess context pcontext (s:ss) (nrmap, ts) = getProcess context pcontext (ss++newStates) (nrmap', ts ++ newTransitions) where
    (nrmap', newTransitions) = unfoldProcessState context pcontext nrmap s
    newStates = Map.keys $ Map.difference nrmap' nrmap

-- | Get a process specification from a single state
unfoldProcessState :: Context -> ProcessContext -> PStateNrMap -> PState -> ProcessSpecification
unfoldProcessState context pc@(PContext smap _ _) nrmap s@(sname, params) = case (Map.lookup sname smap, Map.lookup s nrmap) of
    (Just (State _ vars content), Just i) -> foldr (unfoldStateContent context' i) (nrmap, []) content where
        context' = setStateInput (zip varnames params) context
        varnames = map variableName vars
    _ -> fatal 1010 "State not found in statemap or statenrmap"
    where
        unfoldStateContent :: Context -> Int -> WithSourceInfo StateContent -> ProcessSpecification -> ProcessSpecification
        unfoldStateContent cntxt srcState content = case removeSourceInfo content of
            StateTransition t -> unfoldProcessTransition cntxt pc srcState t

-- | Get a process specification from a single transition
unfoldProcessTransition :: Context -> ProcessContext -> Int -> ProcessTransition -> ProcessSpecification -> ProcessSpecification
unfoldProcessTransition context (PContext _ imap omap) srcState (Transition contentsSrc) spec = case readActions of
    [] -> unfoldProcessTransition' context (fromMaybe (err 1099 "Source_Process") $ Map.lookup "Source_Process" imap) pConstColor spec
    [(inChan, t, v)] -> foldr (\c -> unfoldProcessTransition' (context' c) (getChannelNr inChan imap) c) spec colors where
        colors = Types.getColors $ evaluateTypeExpression context t
        context' c' = addStateInput v c' context
    _:_ -> fatal 1019 "At most one read action allowed"
    where
        readActions = mapMaybe (\t -> case t of TransitionRead c d v -> Just (c, d, v); _ -> Nothing) contents
        writeActions = mapMaybe (\t -> case t of TransitionWrite c f -> Just (c, f); _ -> Nothing) contents
        guardActions = mapMaybe (\t -> case t of TransitionGuard e -> Just e; _ -> Nothing) contents
        nextActions = mapMaybe (\t -> case t of TransitionNext s vs -> Just (s, vs); _ -> Nothing) contents
        contents = map removeSourceInfo contentsSrc

        unfoldProcessTransition' :: Context -> Int -> Types.Color -> ProcessSpecification -> ProcessSpecification
        unfoldProcessTransition' cntxt inchan color (nrmap, ts) = if satisfiesGuards then (nrmap', newTransitions ++ ts) else (nrmap, ts) where
            satisfiesGuards = if any isNothing guards then fatal 114 "Couldn't evaluate guard" else all fromJust guards
            guards = map (evaluateBooleanExpressionAsBool cntxt) guardActions
            newTransitions = map (\(a,b,c) -> M.AutomatonT srcState destState inchan eps event a b c) transforms
            destState = fromMaybe (fatal 1100 "unreachable") $ Map.lookup newState nrmap'
            newState = case nextActions of
                [] -> fatal 1123 "No next action found"
                [(s, vs)] -> if any isNothing newvars then fatal 1124 "Couldn't evaluate new param value"
                    else (s, map fromJust newvars) where
                        newvars = map (evaluateDataExpressionAsColor cntxt) vs
                _ -> fatal 1131 "At most one next action allowed"
            nrmap' :: PStateNrMap
            nrmap' = Map.insertWith (flip const) newState (Map.size nrmap) nrmap
            eps = Types.XMatch (Types.color2mfunction color) (Types.XVar inchan)
            event i c = i == inchan && c == color
            transforms :: [(Maybe Int, Maybe Types.MFunctionDisj, Int -> Types.Color -> Maybe (Int, Types.Color))]
            transforms = case writeActions of
                [] -> [(Nothing, Nothing, \_ _ -> Nothing)]
                [(oChan, f)] -> case evaluateDataExpressionAsColorSet cntxt f of
                    Just cs -> map (\c -> (Just $ getChannelNr oChan omap, Just $ Types.color2mfunction c, \ _ _ -> Just (getChannelNr oChan omap, c))) $ Types.getColors cs
                    _ -> fatal 1130 "Couldn't evaluate function content"
                _ -> fatal 1131 "At most one write action allowed"

        getChannelNr c cmap = case channelVariableChannels context c of
            [] -> fatal 1101 $ "ChannelVariable should define exactly one channel: " +++ showT c
            [c'] -> fromMaybe (err 1102 $ showT c') $ Map.lookup c' cmap
            _ -> fatal 1103 $ "ChannelVariable should define exactly one channel: " +++ showT c
        err i name = fatal i $ "Channelname not found in process-context: " +++name

-- | A specification transformation is a function that updates a networkspecification using a context
type SpecTransformation = Context -> NetworkSpecificationSrc -> NetworkSpecificationSrc
-- | translate a macro
translateMacro :: Context -> Parser.MadlAST.Macro -> SpecTransformation -> MacroFunction
translateMacro context (Macro header networkstatements) f pcntxt pexprs = (M.mkMacro network macroname macrointerface, sourceContext mspec') where
    network = M.mkMacroNetwork $ networkSpecification mspec'
    mspec' = f mcntxt mspec
    macroname = T.intercalate "__" $ name : mapMaybe (primitiveExpressionName pcntxt) pexprs
    macrointerface = concatMap (paramChannelNames mcntxt) (inputs ++ outputs)
    (mspec, mcntxt) = translateNetworkStatements networkstatements' (emptySpecificationSrc, paramContext)
    networkstatements' = map (flip setSourceInfo header) interface ++ networkstatements
    paramContext = List.foldl' (flip $ paramToContext pcntxt) context' $ zip nonChannelInputs nonChannelExpressions
    nonChannelInputs = filter (not . isChannelParameter) inputs
    nonChannelExpressions = filter (not . isChannelPrimitiveExpression) pexprs
    context' = context {contextIdentifiers = [], contextBusNames = Hash.empty}
    interface = mapMaybe paramExpression $ inputs ++ outputs

    MacroHeader name inputs outputs = removeSourceInfo header

-- | Convert a network statement and a context to a set of ports and an updated context
translateNetworkStatement :: NetworkStatementSrc -> (NetworkSpecificationSrc, Context) -> (NetworkSpecificationSrc, Context)
translateNetworkStatement statementSrc (spec, context) = let
    srcInfo = getSourceInfo statementSrc
    addSrc l = zip l $ repeat srcInfo
    in case removeSourceInfo statementSrc of
    NetworkChannelDeclaration (ChannelDeclaration channels) -> (spec', context) where
        spec' = addChannels (addSrc channelidentifiers) spec
        channelidentifiers = map (channelIdentifier context) channels
    NetworkChannelDeclaration (ChannelDefinition channels primitiveSrc) -> (spec', pcontext) where
        spec' = joinNetworkSpecifications spec . addChannels (addSrc channelidentifiers) $ addPorts ports pspec
        (pname, pspec, pcontext) = translateNetworkPrimitive primitiveSrc context
        ports = zip (repeat pname) channelidentifiers
        channelidentifiers = map (channelIdentifier context) channels
    NetworkBusDeclaration (BusDeclaration _ busnames) -> (spec', context) where
        spec' = addChannels (addSrc channels) spec
        channels = concatMap (busIndexIdentifiers context) busnames
    NetworkBusDeclaration (BusDefinition _ name primitiveSrc) -> (spec', pcontext) where
        spec' = joinNetworkSpecifications spec . addChannels (addSrc channels) $ addPorts ports pspec
        (pname, pspec, pcontext) = translateNetworkPrimitive primitiveSrc context
        ports = zip (repeat pname) channels
        channels = busIndexIdentifiers context name
    NetworkFunctionDeclaration (FunctionDeclaration header contents) -> (spec, addFunctionToContext name (fun, rt) context) where
        fun = toMFDisj $ evaluateFunctionBody (setFunctionInput intypes context) contents
        rt = evaluateTypeExpression context outtype
        (FunctionHeader name intypes outtype) = removeSourceInfo header
    NetworkLetStatement (LetStatement channelvars primitiveSrc) -> (spec', pcontext) where
        spec' = joinNetworkSpecifications spec $ addPorts ports pspec
        (pname, pspec, pcontext) = translateNetworkPrimitive primitiveSrc context
        ports = zip (repeat pname) channels
        channels = concatMap (channelVariableChannels context) channelvars
    NetworkNetworkPrimitive primitive -> (joinNetworkSpecifications spec pspec, pcontext) where
        (_, pspec, pcontext) = translateNetworkPrimitive (setSourceInfo primitive statementSrc) context
    NetworkParameterDeclaration{} -> (spec, context) -- Int parameters have already been added to the initial context
    NetworkMacro m@(Macro header _) -> (spec, addMacroToContext name outputsize macro context) where
        macro = translateMacro context m (\_ -> id)
        outputsize = Just . sum $ map (paramNrChannels context) outputs
        MacroHeader name _ outputs = removeSourceInfo header
    NetworkProcess p@(Process header _) -> (spec, addMacroToContext name outputsize process context) where
        process = translateMacro context (Macro header []) (translateProcess p)
        outputsize = Just . sum $ map (paramNrChannels context) outputs
        MacroHeader name _ outputs = removeSourceInfo header
    NetworkTypeDeclaration (TypeConst value) -> (spec, addColorSetToContext value colorset context) where
        colorset = Types.constColorSet value
    NetworkTypeDeclaration (TypeEnum name values) -> (spec, addColorSetToContext name colorset context) where
        colorset = Types.enumColorSet values
    NetworkTypeDeclaration (TypeStruct name values) -> (spec, addColorSetToContext name (structToColorSet struct) context) where
        struct = Types.makeStruct $ map (\(VariableDeclaration key expr) -> (key, evaluateSUTypeExpressionAsDisj context expr)) values
    NetworkTypeDeclaration (TypeUnion name values) -> (spec, addColorSetToContext name union context) where
        union = Types.makeColorSet $ map (\(VariableDeclaration key expr) -> (key, evaluateSUTypeExpressionAsStruct context expr)) values
    NetworkForLoop (ForLoop header statements) -> List.foldl' (flip addStatementsToContext) (spec, context) [low..high-1] where
        addStatementsToContext i (s, c) = (s', c{contextIdentifiers = contextIdentifiers c'}) where
            (s', c') = translateNetworkStatements statements (s, addIntParamToContext var (Just i) c{contextInForLoop = True})
        low = evaluateIntegerExpression context l
        high = evaluateIntegerExpression context h
        ForLoopHeader var l h = removeSourceInfo header
    NetworkIfThenElse (IfThenElse cond true false) -> List.foldl' (flip $ translateNetworkStatement) (spec, context) statements where
        statements = case evaluateBooleanExpressionAsBool context cond of
            Just True -> true
            Just False -> false
            Nothing -> fatal 979 "Couldn't evaluate if-then-else condition"
    NetworkPredicateDeclaration (PredicateDeclaration header body) -> (spec, addPredicateToContext name fun context) where
        fun = evaluatePredicateBody (setFunctionInput intypes context) body
        PredicateHeader name intypes = removeSourceInfo header
    NetworkIncludeStatement{} -> fatal 1238 "Include statement shouldn't be present"

-- | Convert a sequence of network statements, a network specification and a context to an updated networkspecification and context
translateNetworkStatements :: [NetworkStatementSrc] -> (NetworkSpecificationSrc, Context) -> (NetworkSpecificationSrc, Context)
translateNetworkStatements statements (spec, context) = List.foldl' (flip $ translateNetworkStatement) (spec, context') statements where
    context' = getInitialContext (map removeSourceInfo statements) context

-- | Convert a network to a network specification
translateNetwork :: Network -> NetworkSpecificationSrc
translateNetwork (NetworkStatements networkstatements) = nspecsrc where
    nspecsrc = fst $ translateNetworkStatements networkstatements (emptySpecificationSrc, emptyContext)
