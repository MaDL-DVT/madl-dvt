{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

{-|
Module      : Parser.MadlTypeChecker
Description : Typechecker for madl AST
Copyright   : (c) Wieger Wesselink 2015-2016, Tessa Belder 2016

This module contains a typechecker for the madl AST
-}
module Parser.MadlTypeChecker (typecheckNetwork, showError) where

-- import Debug.Trace

import Control.Monad

import qualified Data.HashMap as Hash
import qualified Data.Set as Set
import Data.List (nub, intercalate)
import Data.Maybe

import Utils.Either
import Utils.Map
import Utils.Text
import Utils.Tuple

import Parser.MadlAST
import Madl.SourceInformation

--------------------------------------------------------------------------------
-- Error function
--------------------------------------------------------------------------------

-- | The name of this module
fileName :: Text
fileName = "Parser.MadlTypeChecker"

-- | Produces an error message with the given error code
fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

-- | Pairs the module name with an error code
src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src

--------------------------------------------------------------------------------
-- Utility
--------------------------------------------------------------------------------

-- | Checks if a list contains duplicates. N.B. The implementation is not efficient.
listContainsDuplicates :: (Eq a) => [a] -> Bool
listContainsDuplicates xs = xs /= nub xs

--------------------------------------------------------------------------------
-- Typecheck errors
--------------------------------------------------------------------------------

-- | Different types of errors
data Error = BooleanPredicateNotConstantError BooleanExpression -- Not possible to trigger
           | IntegerNotPositiveError IntegerExpression Int
           | BusIndexError Text IntegerExpression
           | BusInputAlreadyAssignedError SourceInformation Text Int
           | BusOutputAlreadyAssignedError SourceInformation Text Int
           | BusInputOutputUsageError Text Int InputOutputUsage
           | ChannelInputAlreadyAssignedError SourceInformation Text
           | ChannelOutputAlreadyAssignedError SourceInformation Text
           | ChannelInputOutputUsageError Text InputOutputUsage
           | DataAttributeNoIntegerConstantError DataExpression -- Not possible to trigger
           | DataFunctionNoIntegerConstantError DataExpression -- Not possible to trigger
           | DataIntegerAttributeNotConstantError DataIntegerExpression -- Not possible to trigger
           | DataTypeNoIntegerConstantError DataExpression
           | DuplicateVariableNamesError [VariableDeclaration TypeExpression]
           | IncorrectSwitchCasesError Attribute [Text] [Text] -- ^ @IncorrectSwitchCasesError switchAttribute declaredSwitchCases expectedSwitchCases@
           | IncompleteFunctionAssignmentError SUTypeExpression
           | IncorrectReturnTypeError SUTypeExpression
           | IllegalTypeSelectionError Text SUTypeExpression
           | IncorrectNrOfArgumentsError [DataExpression] Int -- ^ @IncorrectNrOfArgumentsError arguments expectedNrOfArguments@
           | InvalidArgumentError DataExpression SUTypeExpression -- ^ @InvalidArgumentError argument expectedType@
           | UnsuitableIntegerAttributeError Attribute
           | IllegalAttributeError SUTypeExpression Attribute
           | UnsuitableSwitchExpressionError Attribute SUTypeExpression
           | InvalidEnumerationError [Text]
           | InvalidUnionError [VariableDeclaration SUTypeExpression]
           | InvalidStructError [VariableDeclaration SUTypeExpression]
           | DuplicateParameterNamesError
           | UndeclaredBusNameError Text
           | UndeclaredChannelNameError Text
           | UndeclaredFunctionError Text
           | UndeclaredParameterError Text
           | UndeclaredPredicateError Text
           | UndeclaredPrimitiveError Text
           | UndeclaredIntegerParameterError Text
           | UndeclaredTypeVariableError Text
           | UndefinedDataUnknownError Text
           | UndefinedDataIntegerUnknownError Text
           | UndefinedPrimitiveUnknownError Text
           | UndefinedSwitchUnknownError Text
           | MultipleSwitchOtherwiseError [SwitchExpression]
           | MultipleJoitchOtherwiseError [JoitchExpression]
           | MultiplyDefinedNameError Text
           | AmbiguousInputOutputSizeError Int
           | InputOutputSizeError Int Int Int -- ^ @InvalidArgumentError argumentIndex argumentSize expectedSize@
           | IncorrectNrOfArgumentsFunctionError Int Int FunctionExpression -- ^ @IncorrectNrOfArgumentsFunctionError size expectedSize functionexpression@
           | IncorrectNrOfArgumentsPredicateError Int Int PredicateExpression -- ^ @IncorrectNrOfArgumentsPredicateError size expectedSize predicateexpression@
           | ParameterMismatchError SourceInformation Parameter PrimitiveExpression
           | NoParameterPresentError [PrimitiveExpression]
           | UninstantiatedParametersError [Parameter]
           | UnequalBusSizeError Int Int -- ^ @UnequalBusSizeError bussize assignmentsize@
           | TypeNotEmptyError SUTypeExpression
           | MultipleInitialStatesError -- Not possible to trigger (yet), since no syntax for initial states exists.
           | ProcessInitialStateParamsError
           | MultipleReadActionsError
           | MultipleWriteActionsError
           | NoNextActionError
           | MultipleNextActionsError
           | IllegalProcessChannelError ChannelVariable Int
           | UnknownStateError Text
           | DoublyDefinedStateError SourceInformation Text
           deriving (Show)

-- | An object that has been checked, and as a result may be an 'Error'
type Checked a = Either (WithSourceInfo Error) a
-- | A function that typechecks an object using a context
type TypeCheck a = Context -> a -> Checked a

-- | Indents a string four spaces
indent :: String -> String
indent = ("    " ++)

-- | Pretty show function for typecheck errors
showError :: WithSourceInfo Error -> String
showError (WSI err srctxt srcpos) = unlines $
       [showSourcePos srcpos]
    ++ map indent (showError' err)
    ++ map indent ["In the expression:", indent $ srctxt]

-- | Produced error message for typecheck errors
showError' :: Error -> [String]
showError' err = msg ++ (case expr of Nothing -> []; Just e -> ["In the expression:", indent e]) where
    msg = case err of
        AmbiguousInputOutputSizeError i -> ["The number of channels that should be created at argument #" ++show i ++" of the networkprimitive is ambiguous."]
        BooleanPredicateNotConstantError{} -> ["A predicate application does not evaluate to a constant boolean value."]
        BusIndexError name _ -> ["This expression does not evaluate to a valid index of bus " ++utxt name ++"."]
        BusInputAlreadyAssignedError s name i -> ["The input of bus " ++utxt name ++"[" ++show i ++"] was already assigned at:", indent $ show s]
        BusInputOutputUsageError name i io -> ["Error in input-output usage of bus " ++utxt name ++"[" ++show i ++"]:", indent $ showInputOutputError io]
        BusOutputAlreadyAssignedError s name i -> ["The output of bus " ++utxt name ++"[" ++show i ++"] was already assigned at:", indent $ show s]
        ChannelInputAlreadyAssignedError s name -> ["The input of channel " ++utxt name ++" was already assigned at:", indent $ show s]
        ChannelInputOutputUsageError name io -> ["Error in input-output usage of channel " ++utxt name ++":", indent $ showInputOutputError io]
        ChannelOutputAlreadyAssignedError s name -> ["The output of channel " ++utxt name ++" was already assigned at:", indent $ show s]
        DataAttributeNoIntegerConstantError{} -> ["An attribute does not evaluate to a constant integer value."]
        DataFunctionNoIntegerConstantError{} -> ["A function application does not evaluate to a constant integer value."]
        DataIntegerAttributeNotConstantError{} -> ["An attribute does not evaluate to a constant integer value."]
        DataTypeNoIntegerConstantError{} -> ["A packet type does not evaluate to a constant integer value."]
        DoublyDefinedStateError s name -> ["State " ++utxt name ++" was already declared in this process at:", indent $ show s]
        DuplicateParameterNamesError -> ["Duplicate parameter names."]
        DuplicateVariableNamesError{} -> ["Duplicate variable names."]
        IllegalAttributeError t attr -> ("The attribute '" ++show attr ++"' is not a valid attribute of the type:") : (map indent $ showSUTypeExpression t)
        IllegalProcessChannelError _ s -> ["Read and write actions can only be performed on channels expression of size 1. This expression has size " ++show s ++"."]
        IllegalTypeSelectionError name t -> ("Selection of type " ++utxt name ++" does not match the expected return type:") : (map indent $ showSUTypeExpression t)
        IncompleteFunctionAssignmentError t -> "Function assignment does not add up to the expected return type:" : (map indent $ showSUTypeExpression t)
        IncorrectNrOfArgumentsError ds n ->
            ["The provided number of arguments (" ++show (length ds) ++") is not equal to the expected number of arguments (" ++show n ++")."]
        IncorrectNrOfArgumentsFunctionError found expected _ ->
            ["Function takes " ++show found ++" arguments, while it is expected to take " ++show expected ++" arguments."]
        IncorrectNrOfArgumentsPredicateError found expected _ ->
            ["Predicate takes " ++show found ++" arguments, while it is expected to take " ++show expected ++" arguments."]
        IncorrectReturnTypeError t -> "Function content does not have the expected return type:" : (map indent $ showSUTypeExpression t)
        IncorrectSwitchCasesError attr found expected -> ("Incorrect switch cases declared for attribute " ++show attr ++":") : map indent
            ["Declared cases: " ++show found, "Expected cases: " ++show expected]
        InputOutputSizeError i found expected ->
            [show found ++" channels are created by argument #" ++show i ++" of the networkprimitive, while " ++show expected ++" channels are expected."]
        IntegerNotPositiveError _ val -> ["This expression evaluates to " ++show val ++", while it should evaluate to at least 1."]
        InvalidArgumentError _ t -> "The type of the provided argument does not match the expected type:" : (map indent $ showSUTypeExpression t)
        InvalidEnumerationError{} -> ["Enumeration is not valid since it contains duplicate values."]
        InvalidStructError{} -> ["Struct is not valid since it contains duplicate field names."]
        InvalidUnionError{} -> ["Union is not valid since it contains duplicate field names."]
        MultipleInitialStatesError{} -> ["A process can have at most one initial state."]
        MultipleJoitchOtherwiseError{} -> ["Joitch expression 'otherwise' can be used at most once for each Joitch primitive."]
        MultipleNextActionsError -> ["A transition can not specify more than one next state."]
        MultipleReadActionsError -> ["A transition can perform at most one read action."]
        MultipleSwitchOtherwiseError{} -> ["Switch expression 'otherwise' can be used at most once for each Switch primitive."]
        MultipleWriteActionsError -> ["A transition can perform at most one write action."]
        MultiplyDefinedNameError errmsg -> [utxt errmsg]
        NoNextActionError -> ["A transition must specify a next state."]
        NoParameterPresentError{} -> ["No parameters present to be instantiated."]
        ParameterMismatchError s param _ -> ["Expression does not match parameter:", indent $ show s ++ " " ++ show param]
        ProcessInitialStateParamsError -> ["The initial state of a process is not allowed to have parameters."]
        TypeNotEmptyError t -> "Empty type does not match the expected return type:" : (map indent $ showSUTypeExpression t)
        UndeclaredBusNameError name -> ["Bus " ++utxt name ++" is not declared."]
        UndeclaredChannelNameError name -> ["Channel " ++utxt name ++" is not declared."]
        UndeclaredFunctionError name -> ["Function " ++utxt name ++" is not declared."]
        UndeclaredIntegerParameterError name -> ["Integer parameter " ++utxt name ++" is not declared."]
        UndeclaredParameterError name -> ["Parameter " ++utxt name ++" is not declared."]
        UndeclaredPredicateError name -> ["Predicate " ++utxt name ++" is not declared."]
        UndeclaredPrimitiveError name -> ["Primitive " ++utxt name ++" is not declared."]
        UndeclaredTypeVariableError name -> ["Type " ++utxt name ++" is not declared."]
        UndefinedDataIntegerUnknownError name -> ["Data integer expression " ++utxt name ++" is not declared."]
        UndefinedDataUnknownError name -> ["Data expression " ++utxt name ++" is not declared."]
        UndefinedPrimitiveUnknownError name -> ["Primitive expression " ++utxt name ++" is not declared."]
        UndefinedSwitchUnknownError name -> ["Switch expression " ++utxt name ++" is not declared."]
        UnequalBusSizeError expected found -> ["Outputsize of network primitive (" ++show found ++") does not match number of channels (" ++show expected ++")."]
        UninstantiatedParametersError{} -> ["Some parameters are uninstantiated."]
        UnknownStateError name -> ["State " ++utxt name ++" is not declared."]
        UnsuitableIntegerAttributeError attr -> ["The attribute '" ++show attr ++"' does not evaluate to an integer value."]
        UnsuitableSwitchExpressionError attr t -> ("The attribute '" ++show attr ++"' does not evaluate to a suitable switch type:") : (map indent $ showSUTypeExpression t)

    expr = case err of
        AmbiguousInputOutputSizeError{} -> Nothing
        BooleanPredicateNotConstantError e -> Just $ show e
        BusIndexError _ e -> Just $ show e
        BusInputAlreadyAssignedError{} -> Nothing
        BusInputOutputUsageError{} -> Nothing
        BusOutputAlreadyAssignedError{} -> Nothing
        ChannelInputAlreadyAssignedError{} -> Nothing
        ChannelInputOutputUsageError{} -> Nothing
        ChannelOutputAlreadyAssignedError{} -> Nothing
        DataAttributeNoIntegerConstantError e -> Just $ show e
        DataFunctionNoIntegerConstantError e -> Just $ show e
        DataIntegerAttributeNotConstantError e -> Just $ show e
        DataTypeNoIntegerConstantError e -> Just $ show e
        DoublyDefinedStateError{} -> Nothing
        DuplicateParameterNamesError -> Nothing
        DuplicateVariableNamesError e -> Just $ show e
        IllegalAttributeError{} -> Nothing
        IllegalProcessChannelError c _ -> Just $ show c
        IllegalTypeSelectionError{} -> Nothing
        IncompleteFunctionAssignmentError{} -> Nothing
        IncorrectNrOfArgumentsError ds _ -> Just $ show ds
        IncorrectNrOfArgumentsFunctionError _ _ f -> Just $ show f
        IncorrectNrOfArgumentsPredicateError _ _ p -> Just $ show p
        IncorrectReturnTypeError{} -> Nothing
        IncorrectSwitchCasesError{} -> Nothing
        InputOutputSizeError{} -> Nothing
        IntegerNotPositiveError e _ -> Just $ show e
        InvalidArgumentError d _ -> Just $ show d
        InvalidEnumerationError names -> Just $ unlines (showSUTypeExpression $ SUTypeEnumeration names)
        InvalidStructError vars -> Just $ unlines (showSUTypeExpression $ SUTypeStruct vars)
        InvalidUnionError vars -> Just $ unlines (showSUTypeExpression $ SUTypeUnion vars)
        MultipleInitialStatesError -> Nothing
        MultipleJoitchOtherwiseError jss -> Just $ show jss
        MultipleNextActionsError -> Nothing
        MultipleReadActionsError -> Nothing
        MultipleSwitchOtherwiseError sws -> Just $ show sws
        MultipleWriteActionsError -> Nothing
        MultiplyDefinedNameError{} -> Nothing
        NoNextActionError -> Nothing
        NoParameterPresentError es -> Just $ show es
        ParameterMismatchError _ _ e -> Just $ show e
        ProcessInitialStateParamsError -> Nothing
        TypeNotEmptyError{} -> Nothing
        UndeclaredBusNameError{} -> Nothing
        UndeclaredChannelNameError{} -> Nothing
        UndeclaredFunctionError{} -> Nothing
        UndeclaredIntegerParameterError{} -> Nothing
        UndeclaredParameterError{} -> Nothing
        UndeclaredPredicateError{} -> Nothing
        UndeclaredPrimitiveError{} -> Nothing
        UndeclaredTypeVariableError{} -> Nothing
        UndefinedDataIntegerUnknownError{} -> Nothing
        UndefinedDataUnknownError{} -> Nothing
        UndefinedPrimitiveUnknownError{} -> Nothing
        UndefinedSwitchUnknownError{} -> Nothing
        UnequalBusSizeError{} -> Nothing
        UnknownStateError{} -> Nothing
        UninstantiatedParametersError ps -> Just $ show ps
        UnsuitableIntegerAttributeError{} -> Nothing
        UnsuitableSwitchExpressionError{} -> Nothing

-- | Show function for input-output usage
showInputOutputError :: InputOutputUsage -> String
showInputOutputError (Nothing, Nothing) = "Both input and output are not assigned."
showInputOutputError (Just{} , Nothing) = "Output is not assigned."
showInputOutputError (Nothing, Just{} ) = "Input is not assigned."
showInputOutputError (Just{} , Just{} ) = "No error."

-- | Show function for integer expressions
showIntegerExpression :: IntegerExpression -> String
showIntegerExpression expression = case expression of
    IntegerNumber n -> show n
    IntegerVariable name -> utxt name
    IntegerBinary op left right -> "(" ++showIntegerExpression left ++op' ++showIntegerExpression right ++")" where
        op' = case op of Plus -> " + "; Minus -> " - "; Mult -> " * "; Mod -> " % "

-- | Show function for type expressions
showSUTypeExpression :: SUTypeExpression -> [String]
showSUTypeExpression sutypeexpression = case sutypeexpression of
    SUTypeVariable expr -> case expr of
        TypeVariable name -> [utxt name]
    SUTypeEnumeration vals -> ["enum {" ++intercalate ";" (map utxt vals) ++"}"]
    SUTypeUnion vars -> ["union {"] ++ map indent (concatMap (showVariableDeclaration showSUTypeExpression) vars) ++ ["}"]
    SUTypeStruct vars -> ["struct {"] ++ map indent (concatMap (showVariableDeclaration showSUTypeExpression) vars) ++ ["}"]
    SUTypeRange (RangeExpression l h) -> ["[" ++showIntegerExpression l ++":" ++showIntegerExpression h ++"]"]

-- | Show function for a list of variable declarations
showVariableDeclaration :: (a -> [String]) -> VariableDeclaration a -> [String]
showVariableDeclaration showContent (VariableDeclaration name content) = [utxt name ++":"] ++ map indent (showContent content)

--------------------------------------------------------------------------------
-- Typecheck context
--------------------------------------------------------------------------------

-- | Indicates whether a channel has been used as an input or as a output, and if so, where.
type InputOutputUsage = (Maybe SourceInformation, Maybe SourceInformation)

type MacroParameters = (SourceInformation, Context, [Parameter], [Parameter], [NetworkStatementSrc])
type ProcessParameters = (SourceInformation, [Parameter], [Parameter])
type FunctionParameters = ([TypeExpression], TypeExpression)
type PredicateParameters = [TypeExpression]

-- | Setting for type checking a list of network statements
data CheckSettings = CS {
    checkInputOutput :: Bool, -- ^ If True, it is checker whether all channels in context have an initiator and a target
    checkMacro :: Bool -- ^ If True, it is assumed that integer expression cannot be evaluated to constants (as they may depend on macro parameters)
    }

-- | Typecheck context
data Context = Context {
    -- | Input/output usage information of bus variables
    contextBusDeclarations        :: Hash.Map Text (SourceInformation, [InputOutputUsage]),

    -- | Input/output usage information of channel variables
    contextChannelDeclarations    :: Hash.Map Text (SourceInformation, InputOutputUsage),

    -- | For loop variables and their minimum + maximum values
    contextForLoopChannels        :: Maybe (Set Text),

    -- | Macro names and their input + output parameters
    contextMacros                 :: Hash.Map Text MacroParameters,

    -- | Names of macro integer parameters that are in scope
    contextMacroIntegerParameters :: Set Text,

    -- | Process names and their input + output parameters
    contextProcesses              :: Hash.Map Text ProcessParameters,

    -- | Predicate declaration that are in scope
    contextFunctionDeclarations  :: Hash.Map Text FunctionParameters,

    -- | Int parameter declarations that are in scope
    contextIntegerParameters      :: Hash.Map Text Int,

    -- | Predicate declaration that are in scope
    contextPredicateDeclarations  :: Hash.Map Text PredicateParameters,

    -- | Type declarations that are in scope
    contextTypeDeclarations       :: Hash.Map Text TypeDeclaration,

    -- | Current settings for type checking
    contextCheckSettings          :: CheckSettings
}
instance Show Context where
    show context = unlines [
        "   buses: "                    ++ (show . Hash.keys $ contextBusDeclarations context),
        "   channels: "                 ++ (show . Hash.keys $ contextChannelDeclarations context),
        "   macros: "                   ++ (show . Hash.keys $ contextMacros context),
        "   macro integer parameters: " ++ (show $ contextMacroIntegerParameters context),
        "   processes: "                ++ (show . Hash.keys $ contextProcesses context),
        "   for loop channels: "        ++ (show $ contextForLoopChannels context),
        "   functions: "                ++ (show . Hash.keys $ contextFunctionDeclarations context),
        "   int parameters: "               ++ (show $ contextIntegerParameters context),
        "   predicates: "               ++ (show . Hash.keys $ contextPredicateDeclarations context),
        "   types: "                    ++ (show . Hash.keys $ contextTypeDeclarations context)
        ]

-- | The empty typecheck context
emptyContext :: Context
emptyContext = Context {
    contextBusDeclarations        = Hash.empty,
    contextChannelDeclarations    = Hash.empty,
    contextForLoopChannels        = Nothing,
    contextMacros                 = Hash.empty,
    contextMacroIntegerParameters = Set.empty,
    contextProcesses              = Hash.empty,
    contextFunctionDeclarations   = Hash.empty,
    contextIntegerParameters      = Hash.empty,
    contextPredicateDeclarations  = Hash.empty,
    contextTypeDeclarations       = Hash.empty,
    contextCheckSettings          = CS True False
}

-- | Join two typecheck contexts
joinContexts :: Context -> Context -> Context
joinContexts c1 c2 = Context {
    contextBusDeclarations = Hash.union (contextBusDeclarations c1) (contextBusDeclarations c2),
    contextChannelDeclarations = Hash.union (contextChannelDeclarations c1) (contextChannelDeclarations c2),
    contextForLoopChannels = liftM2 Set.union (contextForLoopChannels c1) (contextForLoopChannels c2),
    contextMacros = Hash.union (contextMacros c1) (contextMacros c2),
    contextMacroIntegerParameters = Set.union (contextMacroIntegerParameters c1) (contextMacroIntegerParameters c2),
    contextProcesses = Hash.union (contextProcesses c1) (contextProcesses c2),
    contextFunctionDeclarations = Hash.union (contextFunctionDeclarations c1) (contextFunctionDeclarations c2),
    contextIntegerParameters = Hash.union (contextIntegerParameters c1) (contextIntegerParameters c2),
    contextPredicateDeclarations = Hash.union (contextPredicateDeclarations c1) (contextPredicateDeclarations c2),
    contextTypeDeclarations = Hash.union (contextTypeDeclarations c1) (contextTypeDeclarations c2),
    contextCheckSettings = contextCheckSettings c1 -- assumption: Both contexts have the same check settings
    }

-- | Check if a channel of the given name exists
isChannelNameDeclared :: Context -> Text -> Bool
isChannelNameDeclared context name = Hash.member name (contextChannelDeclarations context)
-- | Check if a bus of the given name exists
isBusNameDeclared :: Context -> Text -> Bool
isBusNameDeclared context name = Hash.member name (contextBusDeclarations context)
-- | Check if a macro of the given name exists
isMacroNameDeclared :: Context -> Text -> Bool
isMacroNameDeclared context name = Hash.member name (contextMacros context)
-- | Check if a macro integer parameter of the given name exists
isMacroIntegerParameterDeclared :: Context -> Text -> Bool
isMacroIntegerParameterDeclared context name = elem name (contextMacroIntegerParameters context)
-- | Check if a process of the given name exists
isProcessNameDeclared :: Context -> Text -> Bool
isProcessNameDeclared context name = Hash.member name (contextProcesses context)
-- | Check if a function of the given name exists
isFunctionNameDeclared :: Context -> Text -> Bool
isFunctionNameDeclared context name = Hash.member name (contextFunctionDeclarations context)
-- | Check if a function input of the given name exists
isFunctionInputDeclared :: FunctionContext -> Text -> Bool
isFunctionInputDeclared fcontext name = Hash.member name (functionInputVariables fcontext)
-- | Check if an integer parameter of the given name exists
isIntegerParameterDeclared :: Context -> Text -> Bool
isIntegerParameterDeclared context name = Hash.member name (contextIntegerParameters context)
-- | Check if a integer of the given name exists
isIntegerVariableDeclared :: Context -> Text -> Bool
isIntegerVariableDeclared context name = or [
      isIntegerParameterDeclared context name
    , isMacroIntegerParameterDeclared context name
    ]
-- | Check if a predicate of the given name exists
isPredicateNameDeclared :: Context -> Text -> Bool
isPredicateNameDeclared context name = Hash.member name (contextPredicateDeclarations context)
-- | Check if a type of the given name exists
isTypeNameDeclared :: Context -> Text -> Bool
isTypeNameDeclared context name = Hash.member name (contextTypeDeclarations context)
-- | Check if the given name has not yet been used as a busname
checkBusNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkBusNameExists context name = case isBusNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a bus.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a channelname
checkChannelNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkChannelNameExists context name = case isChannelNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a channel.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a macroname
checkMacroNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkMacroNameExists context name = case isMacroNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a macro.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a macroIntegerParametername
checkMacroIntegerParameterExists :: Context -> WithSourceInfo Text -> Checked Text
checkMacroIntegerParameterExists context name = case isMacroIntegerParameterDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a macro integer parameter.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a processname
checkProcessNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkProcessNameExists context name = case isProcessNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a process.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a functionname
checkFunctionNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkFunctionNameExists context name = case isFunctionNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a function.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as an integerParmametername
checkIntegerParameterExists :: Context -> WithSourceInfo Text -> Checked Text
checkIntegerParameterExists context name = case isIntegerParameterDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a parameter.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a predicatename
checkPredicateNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkPredicateNameExists context name = case isPredicateNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a predicate.")) name
    False -> Right $ removeSourceInfo name
-- | Check if the given name has not yet been used as a typename
checkTypeNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkTypeNameExists context name = case isTypeNameDeclared context $ removeSourceInfo name of
    True -> Left $ fmap (MultiplyDefinedNameError . (+++ " was already declared as a type.")) name
    False -> Right $ removeSourceInfo name

-- | Returns a MultiplyDefinedNameError error if name was already defined in the context
checkContextNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkContextNameExists context name = check *> (Right $ removeSourceInfo name) where
    check =
           (checkBusNameExists               context name)
        *> (checkChannelNameExists           context name)
        *> (checkFunctionNameExists          context name)
        *> (checkIntegerParameterExists      context name)
        *> (checkMacroNameExists             context name)
        *> (checkMacroIntegerParameterExists context name)
        *> (checkPredicateNameExists         context name)
        *> (checkProcessNameExists           context name)
        *> (checkTypeNameExists              context name)

-- | Returns a MultiplyDefinedNameError error if name was already defined in the context
checkContextForLoopNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkContextForLoopNameExists context name = check *> (Right $ removeSourceInfo name) where
    check =
           (checkFunctionNameExists          context name)
        *> (checkPredicateNameExists         context name)
        *> (checkTypeNameExists              context name)

-- | Returns a MultiplyDefinedNameError error if the variable name was already defined in the context
checkContextVariableNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkContextVariableNameExists context name = check *> (Right $ removeSourceInfo name) where
    check =
           (checkFunctionNameExists          context name)
        *> (checkIntegerParameterExists      context name)
        *> (checkMacroIntegerParameterExists context name)
        *> (checkPredicateNameExists         context name)
        *> (checkTypeNameExists              context name)

-- | Returns a MultiplyDefinedNameError error if the channel parametername was already defined in the context
checkContextChannelParameterNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkContextChannelParameterNameExists context name = check *> (Right $ removeSourceInfo name) where
    check =
           (checkFunctionNameExists          context name)
        *> (checkIntegerParameterExists      context name)
        *> (checkMacroNameExists             context name)
        *> (checkMacroIntegerParameterExists context name)
        *> (checkPredicateNameExists         context name)
        *> (checkProcessNameExists           context name)
        *> (checkTypeNameExists              context name)

-- | Returns a MultiplyDefinedNameError error if the integer parametername was already defined in the context
checkContextIntegerParameterNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkContextIntegerParameterNameExists context name = check *> (Right $ removeSourceInfo name) where
    check =
           (checkFunctionNameExists          context name)
        *> (checkMacroNameExists             context name)
        *> (checkPredicateNameExists         context name)
        *> (checkProcessNameExists           context name)
        *> (checkTypeNameExists              context name)

-- | Returns a MultiplyDefinedNameError error if the function parametername was already defined in the context
checkContextFunctionParameterNameExists :: Context -> WithSourceInfo Text -> Checked Text
checkContextFunctionParameterNameExists context name = check *> (Right $ removeSourceInfo name) where
    check =
           (checkIntegerParameterExists      context name)
        *> (checkMacroNameExists             context name)
        *> (checkMacroIntegerParameterExists context name)
        *> (checkPredicateNameExists         context name)
        *> (checkProcessNameExists           context name)
        *> (checkTypeNameExists              context name)

-- | Add a channel identifier to the context
addChannelToContext :: Context -> WithSourceInfo Text -> Checked Context
addChannelToContext context name = fmap updateContext $ checkContextNameExists context name where
    updateContext n = context{
        contextChannelDeclarations = Hash.insert n (srcinfo, (Nothing, Nothing)) $ contextChannelDeclarations context,
        contextForLoopChannels = fmap (Set.insert n) $ contextForLoopChannels context
        }
    srcinfo = getSourceInfo name

-- | Add a list of channel identifiers to the context
addChannelsToContext :: Context -> [WithSourceInfo Text] -> Checked Context
addChannelsToContext = foldM addChannelToContext

-- | Adds a bus declaration to the context
addBusDeclarationToContext :: Int -> Context -> WithSourceInfo Text -> Checked Context
addBusDeclarationToContext size context name = fmap updateContext $ checkContextNameExists context name where
    updateContext n = context{
        contextBusDeclarations = Hash.insert n (srcinfo, (replicate size (Nothing, Nothing))) $ contextBusDeclarations context,
        contextForLoopChannels = fmap (Set.insert n) $ contextForLoopChannels context
        }
    srcinfo = getSourceInfo name

-- | Adds multiple bus declarations of the same size to the context
addBusDeclarationsToContext :: Int -> Context -> [WithSourceInfo Text] -> Checked Context
addBusDeclarationsToContext size = foldM $ addBusDeclarationToContext size

-- | Adds a function declaration to the context
addFunctionDeclarationToContext :: Context -> FunctionDeclaration -> Checked Context
addFunctionDeclarationToContext context (FunctionDeclaration header _) = fmap updateContext . checkContextNameExists context $ setSource name where
    updateContext n = context{contextFunctionDeclarations = Hash.insert n (map variableObject inputs, output) (contextFunctionDeclarations context)}
    FunctionHeader name inputs output = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Adds a function declaration to the context
addFunctionSignatureToContext :: Context -> WithSourceInfo FunctionSignature -> Checked Context
addFunctionSignatureToContext context signature = fmap updateContext . checkContextNameExists context $ setSource name where
    updateContext n = context{contextFunctionDeclarations = Hash.insert n (inputs, output) (contextFunctionDeclarations context)}
    FunctionSignature output name inputs = removeSourceInfo signature
    setSource = flip setSourceInfo signature

-- | Adds an integer parameter to the context
addIntegerParameterToContext :: Context -> WithSourceInfo Text -> Int -> Checked Context
addIntegerParameterToContext context name value = fmap updateContext $ checkContextNameExists context name where
    updateContext n = context{contextIntegerParameters = Hash.insert n value (contextIntegerParameters context)}

-- | Adds a macro integer parameter to the context
addMacroIntegerParameterToContext :: Context -> WithSourceInfo Text -> Checked Context
addMacroIntegerParameterToContext context name = fmap updateContext $ checkContextNameExists context name where
    updateContext n = context{contextMacroIntegerParameters = Set.insert n $ contextMacroIntegerParameters context}

-- | Adds a predicate declaration to the context
addPredicateDeclarationToContext :: Context -> PredicateDeclaration -> Checked Context
addPredicateDeclarationToContext context (PredicateDeclaration header _) = fmap updateContext . checkContextNameExists context $ setSource name where
    updateContext n = context{contextPredicateDeclarations = Hash.insert n (map variableObject inputs) (contextPredicateDeclarations context)}
    PredicateHeader name inputs = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Adds a type declaration to the context
addTypeDeclarationToContext :: Context -> WithSourceInfo Text -> TypeDeclaration -> Checked Context
addTypeDeclarationToContext context name typedeclaration = fmap updateContext $ checkContextNameExists context name where
    updateContext n = context{contextTypeDeclarations = Hash.insert n typedeclaration (contextTypeDeclarations context)}

-- | Returns the values corresponding to intexpr.
typecheckBusIndex :: Context -> Text -> WithSourceInfo IntegerExpression -> Checked Int
typecheckBusIndex context busname intexpr = join $ liftM2 checkInBusRange checkedName checkedIndex where
    checkInBusRange name index = case (0 <= index && index < (contextBusSize context name)) of
        True -> Right index
        False -> Left $ fmap (BusIndexError name) intexpr
    checkedIndex = if checkMacro $ contextCheckSettings context then fatal 403 "Illegal" else typecheckIntegerConstant context intexpr
    checkedName = case isBusNameDeclared context busname of
        True -> Right busname
        False -> Left . setSource $ UndeclaredBusNameError busname
    setSource = flip setSourceInfo intexpr

-- | Returns the size of the bus corresponding to name in the contextBusDeclarations map
-- Precondition: name is a valid key
contextBusSize :: Context -> Text -> Int
contextBusSize context name = length inputoutput where
    (_::SourceInformation, inputoutput::[InputOutputUsage]) = lookupM (src 578) name $ contextBusDeclarations context

-- | Replace the nth element of a list.
-- Precondition: the list has at least n elements.
replaceNthElement :: Int -> a -> [a] -> [a]
replaceNthElement n item lst = a ++ (item:b) where (a, (_:b)) = splitAt n lst

-- | Set the i-th bus input corresponding to name to True.
-- Precondition: (name, i) is a valid bus index
setBusInput ::  Text -> Context -> WithSourceInfo Int -> Checked Context
setBusInput name context iSrc =
    case left of
        Just s -> Left $ fmap (BusInputAlreadyAssignedError s name) iSrc
        Nothing -> Right $ context{contextBusDeclarations = Hash.insert name (srcinfo, (replaceNthElement i (Just sourceInfo, right) input_output_usages)) (contextBusDeclarations context)}
    where
        (left, right) = lookupM (src 433) i input_output_usages
        (srcinfo, input_output_usages) = lookupM (src 610) name (contextBusDeclarations context)
        i = removeSourceInfo iSrc
        sourceInfo = getSourceInfo iSrc

-- | Sets multiple bus inputs corresponding to name to True.
setBusInputs :: Text -> Context -> [WithSourceInfo Int] -> Checked Context
setBusInputs name = foldM $ setBusInput name

-- | Set the i-th bus output corresponding to name to True.
-- Precondition: (name, i) is a valid bus index
setBusOutput :: Text -> Context -> WithSourceInfo Int -> Checked Context
setBusOutput name context iSrc =
    case right of
        Just s -> Left $ fmap (BusOutputAlreadyAssignedError s name) iSrc
        Nothing -> Right $ context{contextBusDeclarations = Hash.insert name (srcinfo, (replaceNthElement i (left, Just sourceInfo) input_output_usages)) (contextBusDeclarations context)}
    where
        (left, right) = lookupM (src 453) i input_output_usages
        (srcinfo, input_output_usages) = lookupM (src 611) name (contextBusDeclarations context)
        i = removeSourceInfo iSrc
        sourceInfo = getSourceInfo iSrc

-- | Sets multiple bus outputs corresponding to name to True.
setBusOutputs :: Text -> Context -> [WithSourceInfo Int] -> Checked Context
setBusOutputs name = foldM $ setBusOutput name

-- | Set the channel input corresponding to name to True.
-- Precondition: name is a valid channel name
setChannelInput :: Context -> WithSourceInfo Text -> Checked Context
setChannelInput context nameSrc =
    case input of
        Just s -> Left $ fmap (ChannelInputAlreadyAssignedError s) nameSrc
        Nothing -> Right $ context{contextChannelDeclarations = Hash.insert name (srcinfo, (Just sourceInfo, output)) (contextChannelDeclarations context)}
    where
        (srcinfo, (input, output)) = lookupM (src 627) name (contextChannelDeclarations context)
        name = removeSourceInfo nameSrc
        sourceInfo = getSourceInfo nameSrc

-- | Set the channel inputs corresponding to names to True.
-- Precondition: the elements of names are valid channel names
setChannelInputs :: Context -> [WithSourceInfo Text] -> Checked Context
setChannelInputs = foldM setChannelInput

-- | Set the channel output corresponding to name to True.
-- Precondition: name is a valid channel name
setChannelOutput :: Context -> WithSourceInfo Text -> Checked Context
setChannelOutput context nameSrc =
    case output of
        Just s -> Left $ fmap (ChannelOutputAlreadyAssignedError s) nameSrc
        Nothing -> Right $ context{contextChannelDeclarations = Hash.insert name (srcinfo, (input, Just sourceInfo)) (contextChannelDeclarations context)}
    where
        (srcinfo, (input, output)) = lookupM (src 644) name (contextChannelDeclarations context)
        name = removeSourceInfo nameSrc
        sourceInfo = getSourceInfo nameSrc

-- | Checks if the input and output of the channel with the given name are used
checkChannelInputOutput :: Text -> (SourceInformation, InputOutputUsage) -> Checked ()
checkChannelInputOutput name (srcinfo, input_output_usage) =
    case input_output_usage of
        (Just{}, Just{}) -> Right ()
        _ -> Left . setSource $ ChannelInputOutputUsageError name input_output_usage
    where
        setSource = flip addSourceInfo srcinfo

-- | Check a list of channel @InputOutputUsage@s
checkChannelInputOutputs :: [(Text, (SourceInformation, InputOutputUsage))] -> Checked ()
checkChannelInputOutputs values = mapM (uncurry checkChannelInputOutput) values *> Right ()

-- | Check a bus @InputOutputUsage@
checkBusInputOutput :: Text -> (SourceInformation, [InputOutputUsage]) -> Checked ()
checkBusInputOutput name (srcinfo, input_output_usages) = mapM (uncurry checkIO) (zip [0..] input_output_usages) *> Right () where
    checkIO _ (Just{}, Just{}) = Right ()
    checkIO i _ =  Left . setSource . BusInputOutputUsageError name i $ lookupM (src 530) i input_output_usages
    setSource = flip addSourceInfo srcinfo

-- | Check a list of bus @InputOutputUsage@s
checkBusInputOutputs :: [(Text, (SourceInformation, [InputOutputUsage]))] -> Checked ()
checkBusInputOutputs values = mapM (uncurry checkBusInputOutput) values *> Right ()

-- | Checks if the inputs and outputs of all channel and bus variables have been set
checkInputOutputCompleteness :: Context -> Checked ()
checkInputOutputCompleteness context = checkChannels *> checkBusses where
    checkChannels = checkChannelInputOutputs $ Hash.assocs channels
    checkBusses = checkBusInputOutputs $ Hash.assocs busses
    channels = case contextForLoopChannels context of
        Nothing -> contextChannelDeclarations context
        Just names -> Hash.filterWithKey (\k _ -> Set.member k names) $ contextChannelDeclarations context
    busses = case contextForLoopChannels context of
        Nothing -> contextBusDeclarations context
        Just names -> Hash.filterWithKey (\k _ -> Set.member k names) $ contextBusDeclarations context

-- | Get the channel size of a primitive parameter
primitiveParameterSize :: Context -> WithSourceInfo Parameter -> Checked Int
primitiveParameterSize context parameter = case removeSourceInfo parameter of
    ChannelParameter{} -> Right 1
    BusParameter intexpr _ -> typecheckIntegerConstant context $ setSource intexpr
    IntParameter{} -> Right 0
    FunctionParameter{} -> Right 0
    where
        setSource = flip setSourceInfo parameter

-- | Check the combined channel size of a list primitive parameters
primitiveParametersSize :: Context -> [WithSourceInfo Parameter] -> Checked Int
primitiveParametersSize context parameters = fmap sum sizes where
    sizes = mapM (primitiveParameterSize context) parameters

-- | Returns the output size of the macro with the given name
-- Precondition: name refers to a macro in the context
primitiveOutputSize :: Context -> Text -> Checked Int
primitiveOutputSize context name = primitiveParametersSize context parameters where
    parameters = case Hash.lookup name $ contextMacros context of
        Just (srcinfo, _, _, outputparameters, _) -> map (flip addSourceInfo srcinfo) outputparameters
        Nothing -> case Hash.lookup name $ contextProcesses context of
            Nothing -> fatal 566 $ "Key " +++ name +++ " not found!"
            Just (srcinfo, _, outputparameters) -> map (flip addSourceInfo srcinfo) outputparameters

--------------------------------------------------------------------------------
-- Boolean expressions
--------------------------------------------------------------------------------

-- | Evaluate a @BooleanExpression@ to a boolean value
typecheckBooleanConstant :: Context -> WithSourceInfo BooleanExpression -> Checked Bool
typecheckBooleanConstant context boolexpression = case removeSourceInfo boolexpression of
    BooleanTrue -> Right True
    BooleanFalse -> Right False
    BooleanUnary op expr -> fmap f checkedOperand where
        checkedOperand = typecheckBooleanConstant context $ setSource expr
        f = case op of NOT -> not
    BooleanBinary op left right -> liftM2 f checkedLeft checkedRight where
        checkedLeft  = typecheckBooleanConstant context $ setSource left
        checkedRight = typecheckBooleanConstant context $ setSource right
        f = case op of AND -> (&&); OR -> (||)
    BooleanComparison op left right -> liftM2 f checkedLeft checkedRight where
        checkedLeft  = typecheckDataExpressionIntegerConstant context $ setSource left
        checkedRight = typecheckDataExpressionIntegerConstant context $ setSource right
        f = case op of EqualTo -> (==); NotEqualTo -> (/=); LessThan -> (<); AtMost -> (<=); GreaterThan -> (>); AtLeast -> (>=)
    BooleanPredicateApplication{} -> Left $ fmap BooleanPredicateNotConstantError boolexpression
    where
        setSource = flip setSourceInfo boolexpression

-- | Type check a boolean expression
typecheckBooleanExpression :: Context -> FunctionContext -> WithSourceInfo BooleanExpression -> Checked BooleanExpression
typecheckBooleanExpression context fcontext boolexpression = case removeSourceInfo boolexpression of
    b@BooleanTrue -> Right b
    b@BooleanFalse -> Right b
    BooleanUnary op expr -> fmap (BooleanUnary op) checkedOperand where
        checkedOperand = typecheckBooleanExpression context fcontext $ setSource expr
    BooleanBinary op left right -> liftM2 (BooleanBinary op) checkedLeft checkedRight where
        checkedLeft  = typecheckBooleanExpression context fcontext $ setSource left
        checkedRight = typecheckBooleanExpression context fcontext $ setSource right
    BooleanComparison op left right -> liftM2 (BooleanComparison op) checkedLeft checkedRight where
        checkedLeft  = typecheckDataExpression context fcontext $ setSource left
        checkedRight = typecheckDataExpression context fcontext $ setSource right
    BooleanPredicateApplication p dataIns -> liftM2 BooleanPredicateApplication checkedPredicate checkedDataIns where
        checkedDataIns = typecheckVariablesMatch context fcontext (setSource dataIns) =<< inputTypes
        inputTypes = fmap (evaluatePredicateExpression context) checkedPredicate
        checkedPredicate = typecheckPredicateExpression context $ setSource p
    where
        setSource = flip setSourceInfo boolexpression

-- | Check if a list of @DataExpression@ matches a list of @TypeExpression@
typecheckVariablesMatch :: Context -> FunctionContext -> WithSourceInfo [DataExpression] -> [TypeExpression] -> Checked [DataExpression]
typecheckVariablesMatch context fcontext dataInsSrc inputTypes = correctLength *> checkedDataIns where
    checkedDataIns = mapM (uncurry $ typecheckVariableMatch context fcontext) $ zip (map setSource dataIns) inputTypes
    correctLength = case length inputTypes == length dataIns of
        True -> Right ()
        False -> Left $ fmap (flip IncorrectNrOfArgumentsError $ length inputTypes) dataInsSrc
    dataIns = removeSourceInfo dataInsSrc
    setSource = flip setSourceInfo dataInsSrc

-- | Check if a @DataExpression@ matches a @TypeExpression@
typecheckVariableMatch :: Context -> FunctionContext -> WithSourceInfo DataExpression -> TypeExpression -> Checked DataExpression
typecheckVariableMatch context fcontext dataexpression vartype = checkedDataExpression >>= dataMatch where
    dataMatch expr = case expr of
        DataInteger{} -> Left invalidError
        DataType{} -> Left invalidError
        DataAttribute attr -> attrMatch =<< checkedAttribute where
            attrMatch attrType = case isSubtypeOfSUTypeExpression context attrType suVartype of
                True -> Right expr
                False -> Left invalidError
            checkedAttribute = evaluateFunctionAttribute context fcontext $ setSource attr
        DataFunctionApplication f _ -> case isSubtypeOfSUTypeExpression context returnType suVartype of
            True -> Right expr
            False -> Left invalidError
            where
                returnType = toSUTypeExpression context . snd $ evaluateFunctionExpression context f
        DataUnknown name -> fatal 638 $ "Untransformed DataUnknown " +++ name
    checkedDataExpression = typecheckDataExpression context fcontext dataexpression
    setSource = flip setSourceInfo dataexpression
    suVartype = toSUTypeExpression context vartype
    invalidError = fmap (flip InvalidArgumentError $ toSUTypeExpression context vartype) dataexpression

--------------------------------------------------------------------------------
-- Data expressions
--------------------------------------------------------------------------------

-- | Evaluate a @DataExpression@ to an integer value
typecheckDataExpressionIntegerConstant :: Context -> WithSourceInfo DataExpression -> Checked Int
typecheckDataExpressionIntegerConstant context dataexpression = case removeSourceInfo dataexpression of
    DataInteger integerexpression -> typecheckDataIntegerConstant context $ setSource integerexpression
    DataType{} -> Left $ fmap DataTypeNoIntegerConstantError dataexpression
    DataAttribute{} -> Left $ fmap DataAttributeNoIntegerConstantError dataexpression
    DataFunctionApplication{} -> Left $ fmap DataFunctionNoIntegerConstantError dataexpression
    DataUnknown name -> fatal 624 $ "Untransformed DataUnknown " +++ name
    where
        setSource = flip setSourceInfo dataexpression

-- | Evaluate a @DataIntegerExpression@ to an integer value
typecheckDataIntegerConstant :: Context -> WithSourceInfo DataIntegerExpression -> Checked Int
typecheckDataIntegerConstant context integerexpression = case removeSourceInfo integerexpression of
    DataIntegerNumber n -> Right $ fromIntegral n
    DataIntegerVariable name -> Right . lookupM (src 631) name $ contextIntegerParameters context
    DataIntegerAttribute{} -> Left $ fmap DataIntegerAttributeNotConstantError integerexpression
    DataIntegerBinary op left right -> liftM2 f checkedLeft checkedRight where
        checkedLeft  = typecheckDataIntegerConstant context $ setSource left
        checkedRight = typecheckDataIntegerConstant context $ setSource right
        f = case op of Plus -> (+); Minus -> (-); Mult -> (*); Mod -> mod
    DataIntegerUnknown name -> fatal 640 $ "Untransformed DataUnknown " +++ name
    where
        setSource = flip setSourceInfo integerexpression

-- | Type check a data expression, and remove all instances of @DataUnknown@
typecheckDataExpression :: Context -> FunctionContext -> WithSourceInfo DataExpression -> Checked DataExpression
typecheckDataExpression context fcontext dataexpression = case removeSourceInfo dataexpression of
    DataInteger integerexpression -> fmap DataInteger checkedIntegerExpression where
        checkedIntegerExpression = typecheckDataIntegerExpression context fcontext $ setSource integerexpression
    DataType typeexpression -> fmap DataType checkedTypeExpression where
        checkedTypeExpression = typecheckTypeExpression context $ setSource typeexpression
    d@(DataAttribute attr) -> checkedAttribute *> (Right d) where
        checkedAttribute = evaluateFunctionAttribute context fcontext $ setSource attr
    DataFunctionApplication f dataIns -> liftM2 DataFunctionApplication checkedFunction checkedDataIns where
        checkedDataIns = typecheckVariablesMatch context fcontext (setSource dataIns) =<< inputTypes
        inputTypes = fmap (fst . evaluateFunctionExpression context) checkedFunction
        checkedFunction = typecheckFunctionExpression context $ setSource f
    DataUnknown name -> typecheckDataUnknown context fcontext (setSource name) >>= typecheckDataExpression context fcontext
    where
        setSource = flip setSourceInfo dataexpression

-- | Type check a data integer expression, and removes all instances of @DataIntegerUnknown@
typecheckDataIntegerExpression :: Context -> FunctionContext -> WithSourceInfo DataIntegerExpression -> Checked DataIntegerExpression
typecheckDataIntegerExpression context fcontext integerexpression = case removeSourceInfo integerexpression of
    i@DataIntegerNumber{} -> Right i
    i@(DataIntegerVariable name) -> case isIntegerVariableDeclared context name of
        False -> Left . setSource $ UndeclaredIntegerParameterError name
        True -> Right i
    i@(DataIntegerAttribute attr) -> (checkedAttribute >>= integerAttribute) *> (Right i) where
        integerAttribute attrType = case attrType of
            SUTypeRange{} -> Right ()
            _ -> Left . setSource $ UnsuitableIntegerAttributeError attr
        checkedAttribute = evaluateFunctionAttribute context fcontext $ setSource attr
    DataIntegerBinary op left right -> liftM2 (DataIntegerBinary op) checkedLeft checkedRight where
        checkedLeft  = typecheckDataIntegerExpression context fcontext $ setSource left
        checkedRight = typecheckDataIntegerExpression context fcontext $ setSource right
    DataIntegerUnknown name -> typecheckDataIntegerUnknown context fcontext (setSource name) >>= typecheckDataIntegerExpression context fcontext
    where
        setSource = flip setSourceInfo integerexpression

-- | Tries to match a @DataUnknown@ to an integer parameter, type variable or single-field attribute
typecheckDataUnknown :: Context -> FunctionContext -> WithSourceInfo Text -> Checked (WithSourceInfo DataExpression)
typecheckDataUnknown context fcontext nameSrc = case matches of
    [] -> Left $ fmap UndefinedDataUnknownError nameSrc
    [x] -> Right $ setSourceInfo x nameSrc
    _ -> fatal 669 $ name +++ " was found in context multiple times: " +++ showT matches
    where
        matches = concat [
              [DataInteger $ DataIntegerVariable name | isIntegerVariableDeclared context name]
            , [DataType $ TypeVariable name | isTypeNameDeclared context name]
            , [DataAttribute [name] | isFunctionInputDeclared fcontext name]
            ]
        name = removeSourceInfo nameSrc

-- | Tries to match a @DataIntegerUnknown@ to an integer parameter or single-field attribute.
typecheckDataIntegerUnknown :: Context -> FunctionContext -> WithSourceInfo Text -> Checked (WithSourceInfo DataIntegerExpression)
typecheckDataIntegerUnknown context fcontext nameSrc = case matches of
    [] -> Left $ fmap UndefinedDataIntegerUnknownError nameSrc
    [x] -> Right $ setSourceInfo x nameSrc
    _ -> fatal 682 $ name +++ " was found in context multiple times: " +++ showT matches
    where
        matches = concat [
              [DataIntegerVariable name | isIntegerVariableDeclared context name]
            , [DataIntegerAttribute [name] | isFunctionInputDeclared fcontext name]
            ]
        name = removeSourceInfo nameSrc

--------------------------------------------------------------------------------
-- Function expressions / declarations
--------------------------------------------------------------------------------

-- | Type check a @FunctionDeclaration@
typecheckFunctionDeclaration :: Context -> FunctionDeclaration -> Checked FunctionDeclaration
typecheckFunctionDeclaration context (FunctionDeclaration header body) = checkedStatement where
    checkedStatement = liftM2 FunctionDeclaration (fmap (flip setSourceInfo header . snd) checkedHeader) checkedBody
    checkedBody = flip (typecheckFunctionBody context) body =<< fmap fst checkedHeader
    checkedHeader = typecheckFunctionHeader context header

-- | The context of function. I.e. its input variables and its output type.
data FunctionContext = FC {
    functionInputVariables :: Hash.Map Text SUTypeExpression,
    functionReturnType :: SUTypeExpression,
    functionInSwitch :: Bool
    }
-- | The empty function context
emptyFunctionContext :: FunctionContext
emptyFunctionContext = FC Hash.empty (SUTypeEnumeration []) False

-- | Type of a type check function for an object of type a
type FTypeCheck a = Context -> FunctionContext -> a -> Checked a

-- | Type check a @FunctionHeader@
typecheckFunctionHeader :: Context -> WithSourceInfo FunctionHeader -> Checked (FunctionContext, FunctionHeader)
typecheckFunctionHeader context header = liftM2 (\c h -> (c, h)) checkedContext checkedHeader where
    checkedContext = fmap fcontext checkedInputVars
    fcontext vars = emptyFunctionContext{
          functionInputVariables = Hash.fromList $ map (\(VariableDeclaration n t) -> (n, toSUTypeExpression context t)) vars
        , functionReturnType = toSUTypeExpression context outputType
    }
    checkedHeader = liftM2 (FunctionHeader name) checkedInputVars checkedOutputType

    checkedOutputType = typecheckTypeExpression context $ setSource outputType
    checkedInputVars = typecheckVariableDeclarations context err checkName checkType inputVars
    err = setSource . DuplicateVariableNamesError
    checkName cntxt = checkContextVariableNameExists cntxt . setSource
    checkType cntxt = typecheckTypeExpression cntxt . setSource
    FunctionHeader name inputVars outputType = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Type check a switch statement
typecheckSwitchStatement :: Context -> FunctionContext -> WithSourceInfo (SwitchStatement a) -> FTypeCheck a -> Checked (SwitchStatement a)
typecheckSwitchStatement context fcontext statement typecheckCase = checkedStatement where
    checkedStatement = liftM2 SwitchStatement (completeNames =<< switchNames) checkedCases
    checkedCases = mapM typecheckCase' cases

    typecheckCase' (SwitchCase name body) = fmap (SwitchCase name) checkedBody where
        checkedBody = typecheckCase context (updateFunctionInputVariable fcontext attr name) body

    completeNames names = case names == (Set.fromList declaredNames) of
        True -> Right attr
        False -> Left . setSource $ IncorrectSwitchCasesError attr declaredNames (Set.toList names)
    switchNames = evaluateSwitchAttribute context fcontext $ setSource attr
    declaredNames = map (\(SwitchCase name _) -> name) cases
    SwitchStatement attr cases = removeSourceInfo statement
    setSource = flip setSourceInfo statement

-- | Update a functioncontext with a choice made in a switchstatement
updateFunctionInputVariable :: FunctionContext -> Attribute -> Text -> FunctionContext
updateFunctionInputVariable _ [] _ = fatal 774 "Unreachable"
updateFunctionInputVariable fcontext (first:others) choice = fcontext' where
    fcontext' = fcontext{functionInputVariables = Hash.adjust (updateInput others) first $ functionInputVariables fcontext}
    updateInput :: Attribute -> SUTypeExpression -> SUTypeExpression
    updateInput [] SUTypeEnumeration{} = SUTypeEnumeration [choice]
    updateInput [] (SUTypeUnion flds) = case findVariable choice flds of
        Nothing -> fatal 777 "Unreachable"
        Just val -> SUTypeUnion [VariableDeclaration choice val]
    updateInput (fld:flds) (SUTypeUnion uflds) = case findVariable fld uflds of
        Nothing -> fatal 780 "Unreachable"
        Just val -> SUTypeUnion $ updateVariable fld (updateInput flds val) uflds
    updateInput (fld:flds) (SUTypeStruct sflds) = case findVariable fld sflds of
        Nothing -> fatal 780 "Unreachable"
        Just val -> SUTypeStruct $ updateVariable fld (updateInput flds val) sflds
    updateInput _ _ = fatal 785 "Unreachable"

-- | Type check an if-then-else statement
typecheckIfThenElse :: Context -> FunctionContext -> WithSourceInfo (IfThenElse a) -> FTypeCheck a -> Checked (IfThenElse a)
typecheckIfThenElse context fcontext ifthenelse typecheckCase = checkedStatement where
    checkedStatement = liftM3 IfThenElse checkedBool checkedThenCase checkedElseCase
    checkedElseCase = typecheckCase context fcontext elsecase
    checkedThenCase = typecheckCase context fcontext thencase
    checkedBool = typecheckBooleanExpression context fcontext $ setSource bool
    IfThenElse bool thencase elsecase = removeSourceInfo ifthenelse
    setSource = flip setSourceInfo ifthenelse

-- | Type check a @FunctionBody@
typecheckFunctionBody :: Context -> FunctionContext -> FunctionBodySrc -> Checked FunctionBodySrc
typecheckFunctionBody context fcontext functionbody = fmap setSource $ case removeSourceInfo functionbody of
    FunctionBodySwitch switchstatement -> fmap FunctionBodySwitch checkedSwitchStatement where
        checkedSwitchStatement = typecheckSwitchStatement context fcontext (setSource switchstatement) typecheckFunctionBody
    FunctionBodyAssignment assignments -> fmap FunctionBodyAssignment checkedAssignments where
        checkedAssignments = mapM typecheckAssignment =<< completeError assignments
        -- Check if an assignment body has the correct type
        typecheckAssignment :: FunctionAssignment -> Checked FunctionAssignment
        typecheckAssignment (FunctionAssignment attr body) = fmap (FunctionAssignment attr) checkedBody where
            checkedBody = (\rt -> typecheckFunctionBody context fcontext{functionReturnType=rt} body) =<< returnType
            returnType = evaluateAttribute context (functionReturnType fcontext) $ setSource attr

        -- Check if all assignments together result in the correct returnType
        completeError assigns = case foldM removeAttribute (functionReturnType fcontext) $ map (\(FunctionAssignment attr _) -> attr) assigns of
            Right (SUTypeEnumeration []) -> Right assigns
            Right{} -> Left . setSource . IncompleteFunctionAssignmentError $ functionReturnType fcontext
            Left err -> Left err

        -- Remove a single attribute from a type expression.
        removeAttribute :: SUTypeExpression -> Attribute -> Checked SUTypeExpression
        removeAttribute expression attr = fmap (fromMaybe $ SUTypeEnumeration []) result where
            result = returnType *> (Right $ removeAttributeFromSUTypeExpression context attr expression)
            returnType = evaluateAttribute context expression $ setSource attr

    FunctionBodyTypeSelection name body -> fmap (FunctionBodyTypeSelection name) $ checkedBody =<< checkedReturnType where
        checkedBody rt = case body of
            Nothing -> (fmap setSource checkedReturnType >>= checkEmptySUTypeExpression context) *> Right Nothing
            Just body' -> fmap Just $ typecheckFunctionBody context fcontext{functionReturnType = rt} body'
        checkedReturnType = case returnType of
            SUTypeEnumeration vals -> case Set.member name (Set.fromList vals) of
                True -> Right $ SUTypeEnumeration []
                False -> Left . setSource $ IllegalTypeSelectionError name returnType
            SUTypeUnion vals -> case findVariable name vals of
                Nothing -> Left . setSource $ IllegalTypeSelectionError name returnType
                Just t -> Right t
            _ -> Left . setSource $ IllegalTypeSelectionError name returnType

        returnType = functionReturnType fcontext

    FunctionBodyContent dataexpression -> fmap FunctionBodyContent $ dataMatches =<< checkedDataExpression where
        checkedDataExpression = typecheckDataExpression context fcontext $ setSource dataexpression
        dataMatches expr = case dataExpressionMatchesReturnType expr (functionReturnType fcontext) of
            True -> Right expr
            False -> Left . setSource $ IncorrectReturnTypeError (functionReturnType fcontext)

        dataExpressionMatchesReturnType :: DataExpression -> SUTypeExpression -> Bool
        dataExpressionMatchesReturnType expr returnType = case expr of
            DataInteger{} -> case returnType of SUTypeRange{} -> True; _ -> False
            DataType typeexpr -> isSubtypeOfSUTypeExpression context (toSUTypeExpression context typeexpr) returnType
            DataAttribute attr -> isSubtypeOfSUTypeExpression context (fromRight $ evaluateFunctionAttribute context fcontext $ setSource attr) returnType
            DataFunctionApplication f _ -> isSubtypeOfSUTypeExpression context (toSUTypeExpression context . snd $ evaluateFunctionExpression context f) returnType
            DataUnknown{} -> fatal 800 "Unreachable"
    FunctionBodyIfThenElse ifthenelse -> fmap FunctionBodyIfThenElse checkedIfThenElse where
        checkedIfThenElse = typecheckIfThenElse context fcontext (setSource ifthenelse) typecheckFunctionBody
    where
        setSource = flip setSourceInfo functionbody

-- | Check if the given SUTypeExpression is empty
checkEmptySUTypeExpression :: Context -> WithSourceInfo SUTypeExpression -> Checked ()
checkEmptySUTypeExpression context expression = case removeSourceInfo expression of
    SUTypeEnumeration vals -> if null vals then Right () else Left $ fmap TypeNotEmptyError expression
    SUTypeRange{} -> Left $ fmap TypeNotEmptyError expression
    SUTypeStruct flds -> if null flds then Right () else Left $ fmap TypeNotEmptyError expression
    SUTypeUnion flds -> if null flds then Right () else Left $ fmap TypeNotEmptyError expression
    SUTypeVariable expr -> checkEmptySUTypeExpression context . setSource $ toSUTypeExpression context expr
    where
        setSource = flip setSourceInfo expression

-- | Check if two SUTypeExpressions are equivalent
equalsSUTypeExpression :: Context -> SUTypeExpression -> SUTypeExpression -> Bool
equalsSUTypeExpression context expr1 expr2 = cond1 && cond2 where
    cond1 = isSubtypeOfSUTypeExpression context expr1 expr2
    cond2 = isSubtypeOfSUTypeExpression context expr2 expr1

-- | Check if an SUTypeExpression is a subtype of another SUTypeExpression
isSubtypeOfSUTypeExpression :: Context -> SUTypeExpression -> SUTypeExpression -> Bool
isSubtypeOfSUTypeExpression context expr1 expr2 = case (expr1, expr2) of
    (SUTypeVariable expr, _) -> isSubtypeOfSUTypeExpression context (toSUTypeExpression context expr) expr2
    (_, SUTypeVariable expr) -> isSubtypeOfSUTypeExpression context expr1 (toSUTypeExpression context expr)
    (SUTypeEnumeration vals, _) -> isSubtypeOfSUTypeExpression context (SUTypeUnion $ map (\val -> VariableDeclaration val $ SUTypeStruct []) vals) expr2
    (_, SUTypeEnumeration vals) -> isSubtypeOfSUTypeExpression context expr1 (SUTypeUnion $ map (\val -> VariableDeclaration val $ SUTypeStruct []) vals)
    (SUTypeUnion [], SUTypeStruct{}) -> True
    (SUTypeUnion vals1, SUTypeUnion vals2) -> all (includedIn vals2) vals1
    (SUTypeStruct [], SUTypeUnion{}) -> True
    (SUTypeStruct vals1, SUTypeStruct vals2) -> all (includedIn vals2) vals1
    (SUTypeRange{}, SUTypeRange{}) -> True
    _ -> False
    where
        includedIn :: [VariableDeclaration SUTypeExpression] -> VariableDeclaration SUTypeExpression -> Bool
        includedIn vals (VariableDeclaration name expr) = case findVariable name vals of
            Nothing -> False
            Just expr' -> isSubtypeOfSUTypeExpression context expr expr'

-- | Type check a function expression
typecheckFunctionExpression :: Context -> WithSourceInfo FunctionExpression -> Checked FunctionExpression
typecheckFunctionExpression context expression = case removeSourceInfo expression of
    e@(FunctionVariable name) -> case Hash.lookup name (contextFunctionDeclarations context) of
        Nothing -> Left . setSource $ UndeclaredFunctionError name
        Just{} -> Right e
    where
        setSource = flip setSourceInfo expression

-- | Evaluate a function expression
evaluateFunctionExpression :: Context -> FunctionExpression -> FunctionParameters
evaluateFunctionExpression context functionexpression = case functionexpression of
    FunctionVariable name -> lookupM (src 806) name (contextFunctionDeclarations context)

-- | Transform a @TypeExpression@ to an @SUTypeExpression@
toSUTypeExpression :: Context -> TypeExpression -> SUTypeExpression
toSUTypeExpression context typeexpression = case typeexpression of
    TypeVariable name -> case Hash.lookup name $ contextTypeDeclarations context of
        Nothing -> fatal 767 $ "Undeclared type variable " +++ name
        Just (TypeConst n) -> SUTypeEnumeration [n]
        Just (TypeEnum _name vals) -> SUTypeEnumeration vals
        Just (TypeStruct _name flds) -> SUTypeStruct flds
        Just (TypeUnion _name flds) -> SUTypeUnion flds

-- | Find the set of names identified by an attribute
evaluateSwitchAttribute :: Context -> FunctionContext -> WithSourceInfo Attribute -> Checked (Set Text)
evaluateSwitchAttribute context fcontext attr = case evaluateFunctionAttribute context fcontext attr of
    Right expr@(SUTypeEnumeration []) -> Left . setSource $ UnsuitableSwitchExpressionError (removeSourceInfo attr) expr
    Right (SUTypeEnumeration vals) -> Right $ Set.fromList vals
    Right expr@SUTypeRange{} -> Left . setSource $ UnsuitableSwitchExpressionError (removeSourceInfo attr) expr
    Right expr@SUTypeStruct{} -> Left . setSource $ UnsuitableSwitchExpressionError (removeSourceInfo attr) expr
    Right expr@(SUTypeUnion []) -> Left . setSource $ UnsuitableSwitchExpressionError (removeSourceInfo attr) expr
    Right (SUTypeUnion uflds) -> Right . Set.fromList $ map variableName uflds
    Right SUTypeVariable{} -> fatal 776 "Unreachable"
    Left err -> Left err
    where
        setSource = flip setSourceInfo attr

-- | Find the type expression identified by an attribute of which the first argument is a function parameter
evaluateFunctionAttribute :: Context -> FunctionContext -> WithSourceInfo Attribute -> Checked SUTypeExpression
evaluateFunctionAttribute context (FC inputvars _ inSwitch) attr = case removeSourceInfo attr of
    [] -> fatal 775 "Unreachable: empty attributes cannot be parsed"
    first:others -> case Hash.lookup first variablemap of
        Nothing -> Left . setSource $ UndeclaredParameterError first
        Just t -> evaluateAttribute context t $ setSource others
    where
        variablemap = case inSwitch of
            True -> Hash.fromList . map (\name -> (name, toSUTypeExpression context $ TypeVariable name)) . Hash.keys $ contextTypeDeclarations context
            False -> inputvars
        setSource = flip setSourceInfo attr

-- | Find the type expression identified by an attribute
evaluateAttribute :: Context -> SUTypeExpression -> WithSourceInfo Attribute -> Checked SUTypeExpression
evaluateAttribute context expression attr = case removeSourceInfo attr of
    [] -> Right expression
    fld:flds -> case expression of
        SUTypeEnumeration{} -> Left $ fmap (IllegalAttributeError expression) attr
        SUTypeRange{} -> Left $ fmap (IllegalAttributeError expression) attr
        SUTypeStruct sflds -> case findVariable fld sflds of
            Nothing -> Left $ fmap (IllegalAttributeError expression) attr
            Just t -> evaluateAttribute context t $ setSource flds
        SUTypeUnion uflds -> case findVariable fld uflds of
            Nothing -> Left $ fmap (IllegalAttributeError expression) attr
            Just t -> evaluateAttribute context t $ setSource flds
        SUTypeVariable expr -> evaluateAttribute context (toSUTypeExpression context expr) attr
    where
        setSource = flip setSourceInfo attr

-- | Remove the type identified by the given attribute from the given type. Returns Nothing if the resulting type is empty
removeAttributeFromSUTypeExpression :: Context -> Attribute -> SUTypeExpression -> Maybe SUTypeExpression
removeAttributeFromSUTypeExpression _ [] _ = Nothing
removeAttributeFromSUTypeExpression context attr@(fld:flds) expression = case expression of
    SUTypeEnumeration{} -> fatal 766 "Unreachable"
    SUTypeRange{} -> fatal 767 "Unreachable"
    SUTypeVariable expr -> removeAttributeFromSUTypeExpression context attr (toSUTypeExpression context expr)
    SUTypeUnion uflds -> case findVariable fld uflds of
        Nothing -> fatal 784 "Unreachable"
        Just t -> case removeAttributeFromSUTypeExpression context flds t of
            Nothing -> case removeVariable fld uflds of
                [] -> Nothing
                uflds' -> Just $ SUTypeUnion uflds'
            Just expr -> Just . SUTypeUnion $ updateVariable fld expr uflds
    SUTypeStruct sflds -> case findVariable fld sflds of
        Nothing -> fatal 783 "Unreachable"
        Just t -> case removeAttributeFromSUTypeExpression context flds t of
            Nothing -> case removeVariable fld sflds of
                [] -> Nothing
                sflds' -> Just $ SUTypeStruct sflds'
            Just expr -> Just . SUTypeStruct $ updateVariable fld expr sflds

-- | Find the variable with the given name
findVariable :: Text -> [VariableDeclaration a] -> Maybe a
findVariable name = listToMaybe . map variableObject . filter ((== name) . variableName)

-- | Remove the variable with the given name
removeVariable :: Text -> [VariableDeclaration a] -> [VariableDeclaration a]
removeVariable _ [] = []
removeVariable name (var:vars) = case name == variableName var of
    True -> vars
    False -> var:(removeVariable name vars)

-- | Update the variable with the given name to the given value
updateVariable :: Text -> a -> [VariableDeclaration a] -> [VariableDeclaration a]
updateVariable _ _ [] = []
updateVariable name val (var:vars) = case name == variableName var of
    True -> (VariableDeclaration name val):vars
    False -> var:(updateVariable name val vars)

-- | Check if the given function expression had the given amount of input variables
checkFunctionInputSize :: Context -> Int -> WithSourceInfo FunctionExpression -> Checked FunctionExpression
checkFunctionInputSize context size functionexpression = case removeSourceInfo functionexpression of
  f@(FunctionVariable name) -> case Hash.lookup name $ contextFunctionDeclarations context of
      Nothing -> fatal 912 $ "Undeclared function " +++ name
      Just (input, _) -> case size == length input of
          True -> Right f
          False -> Left $ fmap (IncorrectNrOfArgumentsFunctionError (length input) size) functionexpression

--------------------------------------------------------------------------------
-- Integer expressions
--------------------------------------------------------------------------------

-- | Type check an @IntegerExpression@
typecheckIntegerExpression :: Context -> WithSourceInfo IntegerExpression -> Checked IntegerExpression
typecheckIntegerExpression context integerexpression = case removeSourceInfo integerexpression of
    i@IntegerNumber{} -> Right i
    i@(IntegerVariable name) -> case isIntegerVariableDeclared context name of
        True -> Right i
        False -> Left . setSource $ UndeclaredIntegerParameterError name
    IntegerBinary op left right -> liftM2 (IntegerBinary op) checkedLeft checkedRight where
        checkedLeft  = typecheckIntegerExpression context $ setSource left
        checkedRight = typecheckIntegerExpression context $ setSource right
    where
        setSource = flip setSourceInfo integerexpression

-- | Checks if the given @IntegerExpression@ is a valid expression that evaluates to a constant
typecheckIntegerConstant :: Context -> WithSourceInfo IntegerExpression -> Checked Int
typecheckIntegerConstant context integerexpression = case checkMacro $ contextCheckSettings context of
    True -> fatal 961 "Cannot evaluate integerexpression to constant inside macro"
    False -> case removeSourceInfo integerexpression of
        IntegerNumber n -> Right $ fromIntegral n
        IntegerVariable name -> case Hash.lookup name (contextIntegerParameters context) of
            Just value -> Right value
            Nothing -> Left . setSource $ UndeclaredIntegerParameterError name
        IntegerBinary op left right -> liftM2 f checkedLeft checkedRight where
            checkedLeft  = typecheckIntegerConstant context $ setSource left
            checkedRight = typecheckIntegerConstant context $ setSource right
            f = case op of Plus -> (+); Minus -> (-); Mult -> (*); Mod -> mod
    where
        setSource = flip setSourceInfo integerexpression

-- | Checks if the given @IntegerExpression@ evaluates to a value > 0
typecheckIntegerPositive :: Context -> WithSourceInfo IntegerExpression -> Checked Int
typecheckIntegerPositive context intexpr = atLeastOne =<< checkedInteger where
    atLeastOne n = case n > 0 of
        True -> Right n
        False -> Left $ fmap (flip IntegerNotPositiveError n) intexpr
    checkedInteger = if checkMacro $ contextCheckSettings context then Right 1 else typecheckIntegerConstant context intexpr

--------------------------------------------------------------------------------
-- Joitch expressions
--------------------------------------------------------------------------------

-- | Check if a list of joitch expressions contains at most one @JoitchOtherwise@ expression
typecheckJoitchOtherwise :: WithSourceInfo [JoitchExpression] -> Checked [JoitchExpression]
typecheckJoitchOtherwise jssExpressions = if nrOtherwise > 1
    then Left $ fmap MultipleJoitchOtherwiseError jssExpressions
    else Right $ removeSourceInfo jssExpressions
    where
        nrOtherwise = length . filter (\s -> case s of JoitchOtherwise -> True; _ -> False) $ removeSourceInfo jssExpressions

-- | Type check a @JoitchExpression@
typecheckJoitchExpression :: Context -> WithSourceInfo JoitchExpression -> Checked JoitchExpression
typecheckJoitchExpression context joitchexpression = case removeSourceInfo joitchexpression of
    j@JoitchOtherwise -> Right j
    JoitchPredicate predicateexpression -> fmap JoitchPredicate $ checkPredicateInputSize context 2 =<< checkedPredicate where
        checkedPredicate = fmap setSource . typecheckPredicateExpression context $ setSource predicateexpression
    where
        setSource = flip setSourceInfo joitchexpression

--------------------------------------------------------------------------------
-- Predicate expressions / declarations
--------------------------------------------------------------------------------

-- | Type check a @PredicateDeclaration@
typecheckPredicateDeclaration :: Context -> PredicateDeclaration -> Checked PredicateDeclaration
typecheckPredicateDeclaration context (PredicateDeclaration header body) = checkedDeclaration where
    checkedDeclaration = liftM2 PredicateDeclaration (fmap (flip setSourceInfo header . snd) checkedHeader) checkedBody
    checkedBody = flip (typecheckPredicateBody context) body =<< fmap fst checkedHeader
    checkedHeader = typecheckPredicateHeader context header

-- | Type check a @PredicateHeader@
typecheckPredicateHeader :: Context -> WithSourceInfo PredicateHeader -> Checked (FunctionContext, PredicateHeader)
typecheckPredicateHeader context header = liftM2 (\c h -> (c, h)) checkedContext checkedHeader where
    checkedContext = fmap fcontext checkedInputVars
    fcontext vars = emptyFunctionContext{
          functionInputVariables = Hash.fromList $ map (\(VariableDeclaration n t) -> (n, toSUTypeExpression context t)) vars
    }
    checkedInputVars = typecheckVariableDeclarations context err checkName checkType inputVars
    checkName cntxt = checkContextVariableNameExists cntxt . setSource
    checkType cntxt = typecheckTypeExpression cntxt . setSource
    err = setSource . DuplicateVariableNamesError
    checkedHeader = fmap (PredicateHeader name) checkedInputVars
    PredicateHeader name inputVars = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Type check a @PredicateBody@
typecheckPredicateBody :: Context -> FunctionContext -> PredicateBodySrc -> Checked PredicateBodySrc
typecheckPredicateBody context fcontext predicatebody = fmap setSource $ case removeSourceInfo predicatebody of
    PredicateBodyBool expression -> fmap PredicateBodyBool . typecheckBooleanExpression context fcontext $ setSource expression
    PredicateBodySwitch switchstatement -> fmap PredicateBodySwitch checkedSwitchStatement where
        checkedSwitchStatement = typecheckSwitchStatement context fcontext (setSource switchstatement) typecheckPredicateBody
    PredicateBodyIfThenElse ifthenelse -> fmap PredicateBodyIfThenElse checkedIfThenElse where
        checkedIfThenElse = typecheckIfThenElse context fcontext (setSource ifthenelse) typecheckPredicateBody
    where
        setSource = flip setSourceInfo predicatebody

-- | Type check a @PredicateExpression
typecheckPredicateExpression :: Context -> WithSourceInfo PredicateExpression -> Checked PredicateExpression
typecheckPredicateExpression context predicateexpression = case removeSourceInfo predicateexpression of
    p@(PredicateVariable name) -> case isPredicateNameDeclared context name of
        True -> Right p
        False -> Left $ setSourceInfo (UndeclaredPredicateError name) predicateexpression

-- | Evaluate a predicate expression
evaluatePredicateExpression :: Context -> PredicateExpression -> PredicateParameters
evaluatePredicateExpression context predicateexpression = case predicateexpression of
    PredicateVariable name -> lookupM (src 806) name (contextPredicateDeclarations context)

-- | Check if the given predicate expression had the given amount of input variables
checkPredicateInputSize :: Context -> Int -> WithSourceInfo PredicateExpression -> Checked PredicateExpression
checkPredicateInputSize context size predicateexpression = case removeSourceInfo predicateexpression of
  p@(PredicateVariable name) -> case Hash.lookup name $ contextPredicateDeclarations context of
      Nothing -> fatal 912 $ "Undeclared predicate " +++ name
      Just input -> case size == length input of
          True -> Right p
          False -> Left $ fmap (IncorrectNrOfArgumentsPredicateError (length input) size) predicateexpression

--------------------------------------------------------------------------------
-- Switch expressions
--------------------------------------------------------------------------------

-- | Check if a list of switch expressions contains at most one @SwitchOtherwise@ expression
typecheckSwitchOtherwise :: WithSourceInfo [SwitchExpression] -> Checked [SwitchExpression]
typecheckSwitchOtherwise swsExpressions = if nrOtherwise > 1
    then Left $ fmap MultipleSwitchOtherwiseError swsExpressions
    else Right $ removeSourceInfo swsExpressions
    where
        nrOtherwise = length . filter (\s -> case s of SwitchOtherwise -> True; _ -> False) $ removeSourceInfo swsExpressions

-- | Type check a @SwitchExpression@
typecheckSwitchExpression :: Context -> WithSourceInfo SwitchExpression -> Checked SwitchExpression
typecheckSwitchExpression context switchexpression = case removeSourceInfo switchexpression of
    SwitchTypeExpression typeexpression -> fmap SwitchTypeExpression . typecheckTypeExpression context $ setSource typeexpression
    SwitchPredicate predicateexpression -> fmap SwitchPredicate $ checkPredicateInputSize context 1 =<< checkedPredicate where
        checkedPredicate = fmap setSource . typecheckPredicateExpression context $ setSource predicateexpression
    SwitchBooleanExpression booleanexpression -> fmap SwitchBooleanExpression . typecheckBooleanExpression context fcontext $ setSource booleanexpression where
        fcontext = emptyFunctionContext{functionInSwitch = True}
    s@SwitchOtherwise -> Right s
    SwitchUnknown name -> typecheckSwitchUnknown context (setSource name) >>= typecheckSwitchExpression context
    where
        setSource = flip setSourceInfo switchexpression

-- | Tries to match a @SwitchUnknown@ to a type or predicate expression.
typecheckSwitchUnknown :: Context -> WithSourceInfo Text -> Checked (WithSourceInfo SwitchExpression)
typecheckSwitchUnknown context nameSrc = case matches of
    [] -> Left $ fmap UndefinedSwitchUnknownError nameSrc
    [x] -> Right $ setSourceInfo x nameSrc
    _ -> fatal 1142 $ name +++ " was found in context multiple times: " +++ showT matches
    where
        matches = concat [
              [SwitchTypeExpression $ TypeVariable name | isTypeNameDeclared context name]
            , [SwitchPredicate $ PredicateVariable name | isPredicateNameDeclared context name]
            ]
        name = removeSourceInfo nameSrc

--------------------------------------------------------------------------------
-- Type expressions / declaration
--------------------------------------------------------------------------------

-- | Type check a @TypeDeclaration@
typecheckTypeDeclaration :: Context -> WithSourceInfo TypeDeclaration -> Checked TypeDeclaration
typecheckTypeDeclaration context typedeclaration = case removeSourceInfo typedeclaration of
    t@TypeConst{} -> Right t
    t@(TypeEnum _ vals) -> case listContainsDuplicates vals of
        True -> Left . setSource $ InvalidEnumerationError vals
        False -> Right t
    TypeUnion name flds -> fmap (TypeUnion name) $ typecheckVariableDeclarations context err (const Right) checkType flds where
        err = setSource . InvalidUnionError
    TypeStruct name flds -> fmap (TypeStruct name) $ typecheckVariableDeclarations context err (const Right) checkType flds where
        err = setSource . InvalidStructError
    where
        setSource = flip setSourceInfo typedeclaration
        checkType cntxt = typecheckSUTypeExpression cntxt . setSource

-- | Type check a @SUTypeExpression@
typecheckSUTypeExpression :: Context -> WithSourceInfo SUTypeExpression -> Checked SUTypeExpression
typecheckSUTypeExpression context sutypeexpression = case removeSourceInfo sutypeexpression of
    SUTypeVariable expr -> fmap SUTypeVariable . typecheckTypeExpression context $ setSource expr
    e@(SUTypeEnumeration vals) -> case listContainsDuplicates vals of
        True -> Left . setSource $ InvalidEnumerationError vals
        False -> Right e
    SUTypeUnion flds -> fmap SUTypeUnion $ typecheckVariableDeclarations context err (const Right) checkType flds where
        err = setSource . InvalidUnionError
    SUTypeStruct flds -> fmap SUTypeStruct $ typecheckVariableDeclarations context err (const Right) checkType flds where
        err = setSource . InvalidStructError
    SUTypeRange (RangeExpression low high) -> fmap SUTypeRange $ liftM2 RangeExpression checkedLow checkedHigh where
        checkedLow = typecheckIntegerExpression context $ setSource low
        checkedHigh = typecheckIntegerExpression context $ setSource high
    where
        setSource = flip setSourceInfo sutypeexpression
        checkType cntxt = typecheckSUTypeExpression cntxt . setSource

-- | Type check a @TypeExpression@
typecheckTypeExpression :: Context -> WithSourceInfo TypeExpression -> Checked TypeExpression
typecheckTypeExpression context typeexpression = case removeSourceInfo typeexpression of
    t@(TypeVariable name) -> case isTypeNameDeclared context name of
        False -> Left $ setSourceInfo (UndeclaredTypeVariableError name) typeexpression
        True -> Right t

--------------------------------------------------------------------------------
-- Channel expressions
--------------------------------------------------------------------------------

-- | Typecheck a list of channel expressions. For each channel expression the output size is computed
typecheckChannelExpressions :: Context -> WithSourceInfo [ChannelExpression] -> Checked (Context, [(ChannelExpression, Maybe Int)])
typecheckChannelExpressions context expressions = postProcess . foldM processExpression (context, []) $ removeSourceInfo expressions where
    postProcess = fmap (\(c, es) -> (c, reverse es))
    processExpression :: (Context, [(ChannelExpression, Maybe Int)]) -> ChannelExpression -> Checked (Context, [(ChannelExpression, Maybe Int)])
    processExpression (cntxt, es) = fmap (\(c, e, s) -> (c, (e, s):es)) . typecheckChannelExpression cntxt . flip setSourceInfo expressions

-- | typecheck a channel expression
-- The last element of the result is the output size of the expression
typecheckChannelExpression :: Context -> WithSourceInfo ChannelExpression -> Checked (Context, ChannelExpression, Maybe Int)
typecheckChannelExpression context chanexpr = case removeSourceInfo chanexpr of
    ChannelPrimitive networkprimitive -> combine (fmap fst3 checkedPrim) (fmap (ChannelPrimitive . snd3) checkedPrim) (fmap thrd3 checkedPrim) where
        checkedPrim = typecheckNetworkPrimitive context networkprimitive
    ChannelId channelvar -> combine checkedContext (fmap (ChannelId . fst) checkedVar) (fmap (Just . snd) checkedVar) where
        checkedContext = setChannelVariableOutputs context =<< fmap (setSource . fst) checkedVar
        checkedVar = typecheckChannelVariable context $ setSource channelvar
    where
        combine :: Checked Context -> Checked ChannelExpression -> Checked (Maybe Int) -> Checked (Context, ChannelExpression, Maybe Int)
        combine = liftM3 (\c x s -> (c, x, s))
        setSource = flip setSourceInfo chanexpr

--------------------------------------------------------------------------------
-- Channel variable
--------------------------------------------------------------------------------

-- | Typechecks a list of channel variables. The last element of the result is the combined output size of all variables
typecheckChannelVariables :: Context -> WithSourceInfo [ChannelVariable] -> Checked ([ChannelVariable], Int)
typecheckChannelVariables context variables = fmap transformResult checkedVariables where
    checkedVariables = mapM (typecheckChannelVariable context . flip setSourceInfo variables) $ removeSourceInfo variables
    transformResult vars = (map fst vars, sum $ map snd vars)

-- | Typecheck a channel variable. The last element of the result is the output size of the variable.
typecheckChannelVariable :: Context -> WithSourceInfo ChannelVariable -> Checked (ChannelVariable, Int)
typecheckChannelVariable context channelvariable = case removeSourceInfo channelvariable of
    x@ChannelVariable{} -> Right (x, 1) -- No need to typecheck name at this point
    x@(BusVariable name) -> Right (x, contextBusSize context name) -- No need to typecheck name at this point
    BusIndex name intexpr -> fmap ((\c -> (c, 1)) . BusIndex name) checkedInteger where
        checkedInteger = typecheckIntegerExpression context $ setSource intexpr
    UnknownVariable name -> typecheckUnknownVariable context (setSource name) >>= typecheckChannelVariable context
    where
        setSource = flip setSourceInfo channelvariable

-- | Tries to match an unknown variable to a channel or bus variable.
typecheckUnknownVariable :: Context -> WithSourceInfo Text -> Checked (WithSourceInfo ChannelVariable)
typecheckUnknownVariable context nameSrc = case matches of
    []  -> Left $ fmap UndeclaredChannelNameError nameSrc
    [x] -> Right $ setSourceInfo x nameSrc
    _ -> fatal 1239 $ name +++ " was found in context multiple times: " +++ showT matches
    where
        matches = concat [
                [BusVariable name | isBusNameDeclared context name]
              , [ChannelVariable name | isChannelNameDeclared context name]
              ]
        name = removeSourceInfo nameSrc

-- | Sets the channel inputs corresponding to variables to True.
setChannelVariableInputs :: Context -> [WithSourceInfo ChannelVariable] -> Checked Context
setChannelVariableInputs = foldM setChannelVariableInput

-- | Set inputs of the given channel variable
setChannelVariableInput :: Context -> WithSourceInfo ChannelVariable -> Checked Context
setChannelVariableInput context channelvariable = if inMacro then Right context else
    case removeSourceInfo channelvariable of
        ChannelVariable name -> setChannelInput context $ setSource name
        BusVariable name -> setBusInputs name context $ map setSource [0..(contextBusSize context name) - 1]
        BusIndex name intexpr -> setBusInputs name context =<< fmap (\i -> [setSource i]) (typecheckBusIndex context name $ setSource intexpr)
        UnknownVariable name -> fatal 1238 $ "Untransformed UnknownVariable " +++ name
    where
        inMacro = checkMacro $ contextCheckSettings context
        setSource = flip setSourceInfo channelvariable

-- | Set outputs of the given channel variable
setChannelVariableOutputs :: Context -> WithSourceInfo ChannelVariable -> Checked Context
setChannelVariableOutputs context channelvariable = if inMacro then Right context else
    case removeSourceInfo channelvariable of
        ChannelVariable name -> setChannelOutput context $ setSource name
        BusVariable name -> setBusOutputs name context $ map setSource [0..(contextBusSize context name) - 1]
        BusIndex name intexpr -> setBusOutputs name context =<< fmap (\i -> [setSource i]) (typecheckBusIndex context name $ setSource intexpr)
        UnknownVariable name -> fatal 1244 $ "Untransformed UnknownVariable " +++ name
    where
        inMacro = checkMacro $ contextCheckSettings context
        setSource = flip setSourceInfo channelvariable

--------------------------------------------------------------------------------
-- Primitive expressions (arguments of network primitives)
--------------------------------------------------------------------------------

-- | Tries to match a PrimitiveUnknown to a channel, integer parameter or type variable.
typecheckPrimitiveUnknown :: Context -> WithSourceInfo Text -> Checked (WithSourceInfo PrimitiveExpression)
typecheckPrimitiveUnknown context nameSrc = case matches of
    [] -> Left $ fmap UndefinedPrimitiveUnknownError nameSrc
    [x] -> Right $ setSourceInfo x nameSrc
    _ -> fatal 1232 $ name +++ " was found in context multiple times: " +++ showT matches
    where
        matches = concat [
              [PrimitiveChannel . ChannelId $ BusVariable name | isBusNameDeclared context name]
            , [PrimitiveChannel . ChannelId $ ChannelVariable name | isChannelNameDeclared context name]
            , [PrimitiveInteger $ IntegerVariable name | isIntegerVariableDeclared context name]
            , [PrimitiveType $ TypeVariable name | isTypeNameDeclared context name]
            , [PrimitiveFunction $ FunctionVariable name | isFunctionNameDeclared context name]
            , [PrimitivePredicate $ PredicateVariable name | isPredicateNameDeclared context name]
            ]
        name = removeSourceInfo nameSrc

-- | Typecheck a primitive expression
-- The last element of the result is the output size of the expression
typecheckPrimitiveExpression :: Context -> WithSourceInfo PrimitiveExpression -> Checked (Context, PrimitiveExpression, Maybe Int)
typecheckPrimitiveExpression context primexpr = case removeSourceInfo primexpr of
    PrimitiveChannel chanexpr -> combine (fmap fst3 checkedChan) (fmap (PrimitiveChannel . snd3) checkedChan) (fmap thrd3 checkedChan) where
        checkedChan = typecheckChannelExpression context $ setSource chanexpr
    PrimitiveInteger intexpr -> combine (Right context) (fmap PrimitiveInteger checkedIntegerExpression) (Right $ Just 0) where
        checkedIntegerExpression = typecheckIntegerExpression context $ setSource intexpr
    PrimitiveType typeexpr -> combine (Right context) (fmap PrimitiveType checkedTypeExpression) (Right $ Just 0) where
        checkedTypeExpression = typecheckTypeExpression context $ setSource typeexpr
    PrimitiveFunction fexpr -> combine (Right context) (fmap PrimitiveFunction checkedFunctionExpression) (Right $ Just 0) where
        checkedFunctionExpression = typecheckFunctionExpression context $ setSource fexpr
    PrimitiveUnknown name -> typecheckPrimitiveUnknown context (setSource name) >>= typecheckPrimitiveExpression context
    PrimitivePredicate predexpr -> combine (Right context) (fmap PrimitivePredicate checkedPredicateExpression) (Right $ Just 0) where
        checkedPredicateExpression = typecheckPredicateExpression context $ setSource predexpr
    PrimitiveJoitch joitchexpr -> combine (Right context) (fmap PrimitiveJoitch checkedJoitchExpression) (Right $ Just 0) where
        checkedJoitchExpression = typecheckJoitchExpression context $ setSource joitchexpr
    PrimitiveSwitch switchexpr -> combine (Right context) (fmap PrimitiveSwitch checkedSwitchExpression) (Right $ Just 0) where
        checkedSwitchExpression = typecheckSwitchExpression context $ setSource switchexpr
    where
        combine :: Checked Context -> Checked PrimitiveExpression -> Checked (Maybe Int) -> Checked (Context, PrimitiveExpression, Maybe Int)
        combine = liftM3 (\c p s -> (c, p, s))
        setSource = flip setSourceInfo primexpr

-- | Typecheck a list of primitive expressions
-- The last element of the result is the sum of the output sizes of the expressions
typecheckPrimitiveExpressions :: Context -> WithSourceInfo [PrimitiveExpression] -> Checked (Context, [PrimitiveExpression], Maybe Int)
typecheckPrimitiveExpressions context expressions = postProcess . foldM processExpression (context, [], Just 0) $ removeSourceInfo expressions where
    postProcess = fmap (\(c, es, s) -> (c, reverse es, s))
    processExpression :: (Context, [PrimitiveExpression], Maybe Int) -> PrimitiveExpression -> Checked (Context, [PrimitiveExpression], Maybe Int)
    processExpression (cntxt, es, size) expr = fmap (\(c, e, s) -> (c, e:es, liftM2 (+) s size)) result where
        result = typecheckPrimitiveExpression cntxt $ setSourceInfo expr expressions

--------------------------------------------------------------------------------
-- Network primitives
--------------------------------------------------------------------------------

-- | Checks if the input and output size are as expected for the given index
checkInputOutputSize :: (Int, Maybe Int, Maybe Int) -> NetworkPrimitiveSrc -> Checked ()
checkInputOutputSize (i, value, expectedValue) networkprimitive = case (value, expectedValue) of
    (Nothing, Nothing) -> Left $ setSourceInfo (AmbiguousInputOutputSizeError i) networkprimitive
    (Just val, Just expVal) -> if val == expVal then Right()
        else Left $ setSourceInfo (InputOutputSizeError i val expVal) networkprimitive
    _ -> Right ()

-- | Checks if the input and output sizes are as expected
checkInputOutputSizes :: [Maybe Int] -> [Maybe Int] -> NetworkPrimitiveSrc -> Checked NetworkPrimitive
checkInputOutputSizes expectedValues values networkprimitive = fmap (const $ removeSourceInfo networkprimitive) result where
    result = mapM (\x -> checkInputOutputSize x networkprimitive) $ zip3 [0..] values expectedValues

-- | Get the name of an integer parameter
integerParameterName :: Parameter -> Maybe Text
integerParameterName parameter = case parameter of
    IntParameter{} -> Just $ parameterName parameter
    _ -> Nothing

-- | Get the name of an integer parameter
functionParameterName :: Parameter -> Maybe Text
functionParameterName parameter = case parameter of
    FunctionParameter{} -> Just $ parameterName parameter
    _ -> Nothing

-- | Drop channel/bus parameters with a combined size of n
dropChannelParameters :: Context -> WithSourceInfo [PrimitiveExpression] -> WithSourceInfo [Parameter] -> Maybe Int -> Checked [Parameter]
dropChannelParameters context es parameters dropsize = case (removeSourceInfo parameters, dropsize) of
    ([], Nothing) -> Right []
    ([], Just 0) -> Right []
    ([], Just{}) -> Left . setSourceEs $ NoParameterPresentError (removeSourceInfo es)
    (params@(first:others), number) -> case number of
        Just 0 -> Right params
        Just n -> case first of
            ChannelParameter{} -> dropChannelParameters context es (setSourcePs others) (Just $ n-1)
            BusParameter intexpr name -> join $ liftM2 (dropChannelParameters context es) (fmap resultingParams bussize) (fmap resultingNumber bussize) where
                resultingParams size = setSourcePs $ case n < size of
                    True -> (BusParameter (IntegerBinary Minus intexpr . IntegerNumber $ toInteger n) name):others
                    False -> others
                resultingNumber size = Just $ max 0 (n - size)
                bussize = typecheckIntegerConstant context $ setSourcePs intexpr
            _ -> Left mismatchError
        Nothing -> case first of
            ChannelParameter{} -> Right $ dropAllChannelParameters others
            BusParameter{} -> Right $ dropAllChannelParameters others
            _ -> Left mismatchError
            where
                dropAllChannelParameters (ChannelParameter{}:ps) = dropAllChannelParameters ps
                dropAllChannelParameters (BusParameter{}:ps) = dropAllChannelParameters ps
                dropAllChannelParameters ps = ps
        where
            mismatchError = setSourceEs $ ParameterMismatchError (getSourceInfo parameters) first e
    where
        e:_ = removeSourceInfo es
        setSourcePs = flip setSourceInfo parameters
        setSourceEs = flip setSourceInfo es

-- | Checks if a list of parameters matches a list of primitive expressions
matchParameters :: Context -> WithSourceInfo [Parameter] -> WithSourceInfo [PrimitiveExpression] -> Checked ()
matchParameters context parameters expressions = case (removeSourceInfo parameters, removeSourceInfo expressions) of
  ([], []) -> Right ()
  ([], es) -> Left $ setSourceInfo (NoParameterPresentError es) expressions
  (ps, []) -> Left $ setSourceInfo (UninstantiatedParametersError ps) expressions
  (params, first:others) -> case first of
      PrimitiveChannel chanexpr -> flip (matchParameters context) (setSourceInfo others expressions) =<< resultingParams where
          resultingParams = fmap (flip setSourceInfo parameters) $ dropChannelParameters context expressions parameters =<< checkedSize
          checkedSize = fmap thrd3 $ typecheckChannelExpression context $ setSourceInfo chanexpr expressions
      _ -> matchFirst *> matchOthers where
          matchFirst = matchParameter context (setSourceInfo (head params) parameters) (setSourceInfo first expressions)
          matchOthers = matchParameters context (setSourceInfo (tail params) parameters) (setSourceInfo others expressions)

-- | Match a single parameter and primitive expression. Assumption: primitive expression is not a channel or bus expression
matchParameter :: Context -> WithSourceInfo Parameter -> WithSourceInfo PrimitiveExpression -> Checked ()
matchParameter context parameter expression = case (removeSourceInfo expression, removeSourceInfo parameter) of
    (PrimitiveInteger{}, IntParameter{}) -> Right ()
    (PrimitiveFunction fexpr, FunctionParameter sig) -> checkInputLength *> checkInputTypes *> checkReturnType *> Right () where
        checkInputLength = case length exprInputTypes == length paramInputTypes of True -> Right (); False -> Left mismatchError
        checkInputTypes = mapM (uncurry matchTypeExpressions) $ zip paramInputTypes exprInputTypes
        checkReturnType = matchTypeExpressions paramReturnType exprReturnType
        FunctionSignature paramReturnType _ paramInputTypes = sig
        (exprInputTypes, exprReturnType) = evaluateFunctionExpression context fexpr
        matchTypeExpressions te1 te2 = case equalsSUTypeExpression context (toSUTypeExpression context te1) (toSUTypeExpression context te2) of
            True -> Right ()
            False -> Left mismatchError
    _ -> Left mismatchError
    where
        mismatchError = setSourceInfo (ParameterMismatchError (getSourceInfo parameter) (removeSourceInfo parameter) $ removeSourceInfo expression) expression

-- | Typecheck a network primitive
-- The last element of the result is the output size of the primitive, or the Nothing if the outputsize is unknown
typecheckNetworkPrimitive :: Context -> NetworkPrimitiveSrc -> Checked (Context, NetworkPrimitiveSrc, Maybe Int)
typecheckNetworkPrimitive context networkprimitive = case removeSourceInfo networkprimitive of
    ControlJoin a b l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1, Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\a' b' -> ControlJoin a' b' l) (chan 0 checkedChannels) (chan 1 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [a, b]
    DeadSink i l-> combine (Just 0) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap (setSource . (\i' -> DeadSink i' l)) (chan 0 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    FControlJoin p a b l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1, Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM3 (\p' a' b' -> FControlJoin p' a' b' l) checkedPredicate (chan 0 checkedChannels) (chan 1 checkedChannels)
        checkedPredicate = checkPredicateInputSize context 2 =<< fmap setSource (typecheckPredicateExpression context $ setSource p)
        checkedChannels = typecheckChannelExpressions context $ setSource [a, b]
    Fork i l -> combine Nothing (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap (setSource . (\i' -> Fork i' l)) (chan 0 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Function f i l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\f' i' -> Function f' i' l) checkedFunction (chan 0 checkedChannels)
        checkedFunction = checkFunctionInputSize context 1 =<< fmap setSource (typecheckFunctionExpression context $ setSource f)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    GuardQueue s ib ig l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1, Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM3 (\a' b' c' -> GuardQueue a' b' c' l) checkedCapacity (chan 0 checkedChannels) (chan 1 checkedChannels)
        checkedCapacity = typecheckIntegerExpression context (setSource s) <* typecheckIntegerPositive context (setSource s)
        checkedChannels = typecheckChannelExpressions context $ setSource [ib, ig]
    Joitch a b jss l -> combine (Just $ 2 * length jss) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1, Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM3 (\a' b' jss' -> Joitch a' b' jss' l) (chan 0 checkedChannels) (chan 1 checkedChannels) checkedJoitchExpressions
        checkedJoitchExpressions = mapM (typecheckJoitchExpression context . setSource) =<< typecheckJoitchOtherwise (setSource jss)
        checkedChannels = typecheckChannelExpressions context $ setSource [a, b]
    LoadBalancer i l -> combine Nothing (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap (setSource . (\i' -> LoadBalancer i' l)) (chan 0 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Match p a b l -> combine (Just 2) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1, Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM3 (\p' a' b' -> Match p' a' b' l) checkedPredicate (chan 0 checkedChannels) (chan 1 checkedChannels)
        checkedPredicate = checkPredicateInputSize context 2 =<< fmap setSource (typecheckPredicateExpression context $ setSource p)
        checkedChannels = typecheckChannelExpressions context $ setSource [a, b]
    Merge a b l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1, Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\a' b' -> Merge a' b' l) (chan 0 checkedChannels) (chan 1 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [a, b]
    MultiMatch p a l -> combine Nothing (fmap fst checkedChannels) checkedPrimitive2 where --todo(tssb) check total input size at least 2
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes $ repeat Nothing) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\p' a' -> MultiMatch p' a' l) checkedPredicate (chans checkedChannels)
        checkedPredicate = checkPredicateInputSize context 2 =<< fmap setSource (typecheckPredicateExpression context $ setSource p)
        checkedChannels = typecheckChannelExpressions context $ setSource a
    PatientSource e l -> combine (Just 1) (Right context)
                         (fmap (\e' -> PatientSource e' l). typecheckTypeExpression context $ setSource e)
    Queue k i l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\k' i' -> Queue k' i' l) checkedCapacity (chan 0 checkedChannels)
        checkedCapacity = typecheckIntegerExpression context (setSource k) <* typecheckIntegerPositive context (setSource k)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Buffer k i l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\k' i' -> Buffer k' i' l) checkedCapacity (chan 0 checkedChannels)
        checkedCapacity = typecheckIntegerExpression context (setSource k) <* typecheckIntegerPositive context (setSource k)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Sink i l -> combine (Just 0) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
--        checkedPrimitive = fmap (setSource . Sink) (chan 0 checkedChannels)
        checkedPrimitive = fmap setSource $ liftM (\i' -> Sink i' l) (chan 0 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Source e l-> combine (Just 1) (Right context) (fmap (\e' -> Source e' l) . typecheckTypeExpression context $ setSource e)
    Switch i sws l -> combine (Just $ length sws) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap setSource $ liftM2 (\i' sws' -> Switch i' sws' l) (chan 0 checkedChannels) checkedSwitchExpressions
        checkedSwitchExpressions = mapM (typecheckSwitchExpression context . setSource) =<< typecheckSwitchOtherwise (setSource sws)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Vars i l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap (setSource . (\i' -> Vars i' l)) (chan 0 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    Cut i l -> combine (Just 1) (fmap fst checkedChannels) checkedPrimitive2 where
        checkedPrimitive2 = join $ liftM2 (checkInputOutputSizes [Just 1]) (sizes checkedChannels) checkedPrimitive
        checkedPrimitive = fmap (setSource . (\i' -> Cut i' l)) (chan 0 checkedChannels)
        checkedChannels = typecheckChannelExpressions context $ setSource [i]
    UserDefinedPrimitive primitivename primitive_expressions l -> (\s -> combine (Just s) (fmap fst3 checkedExpressions) checkedPrimitive) =<< checkedSize where
        checkedPrimitive = checkMatch *> checkInstantiation *> liftM2 (\pn pe -> UserDefinedPrimitive pn pe l) checkedName (fmap snd3 checkedExpressions)
        checkedSize = if inMacro then Right 1 else primitiveOutputSize context =<< checkedName
        checkInstantiation = if inMacro then Right () else if isMacroNameDeclared context primitivename
            then (typecheckMacroInstantiation context primitivename =<< fmap snd3 checkedExpressions)
            else Right ()
        checkMatch = if inMacro then Right () else join $ liftM2 (matchParameters context) checkedParameters checkedExpressionsSrc
        checkedExpressionsSrc = fmap (setSource . snd3) checkedExpressions
        checkedExpressions = typecheckPrimitiveExpressions context $ setSource primitive_expressions
        checkedName = fmap fst findPrimitive
        checkedParameters = fmap snd findPrimitive
        findPrimitive = case Hash.lookup primitivename $ contextMacros context of
            Just (srcinfo, _, inputparameters, _, _) -> Right (primitivename, addSourceInfo inputparameters srcinfo)
            Nothing -> case Hash.lookup primitivename $ contextProcesses context of
                Just (srcinfo, inputparameters, _) -> Right (primitivename, addSourceInfo inputparameters srcinfo)
                Nothing -> Left . setSource $ UndeclaredPrimitiveError primitivename
    where
        combine size = liftM2 (\cntxt prim -> (cntxt, setSource prim, size))
        chans :: Checked (Context, [(ChannelExpression, Maybe Int)]) -> Checked [ChannelExpression]
        chans = fmap (map fst . snd)
        chan :: Int -> Checked (Context, [(ChannelExpression, Maybe Int)]) -> Checked ChannelExpression
        chan i = fmap (lookupM (src 1401) i) . chans
        sizes :: Checked (Context, [(ChannelExpression, Maybe Int)]) -> Checked [Maybe Int]
        sizes = fmap (map snd . snd)
        inMacro = checkMacro $ contextCheckSettings context
        setSource = flip setSourceInfo networkprimitive

--------------------------------------------------------------------------------
-- For Loops
--------------------------------------------------------------------------------

-- | Typecheck a for loop header
typecheckForLoopHeader :: Context -> WithSourceInfo ForLoopHeader -> Checked (WithSourceInfo ForLoopHeader)
typecheckForLoopHeader context header = fmap setSource checkedHeader where
    checkedHeader = liftM3 ForLoopHeader checkedName checkedStart checkedEnd
    checkedName = checkContextForLoopNameExists context $ setSource name
    checkedStart = typecheckIntegerExpression context $ setSource start
    checkedEnd = typecheckIntegerExpression context $ setSource end
    ForLoopHeader name start end = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Loosely typecheck for loop statements. I.e. treat the statements as statements in an uninstantiated macro.
typecheckForLoopStatements :: Context -> [NetworkStatementSrc] -> ForLoopHeader -> Checked [NetworkStatementSrc]
typecheckForLoopStatements context statements (ForLoopHeader name _ _) = fmap snd checkedStatements where
    checkedStatements = typecheckNetworkStatements statements forloopContext
    -- Check statements as if we are in an uninstantiated macro
    forloopContext = context{
        contextIntegerParameters = Hash.delete name $ contextIntegerParameters context,
        contextMacroIntegerParameters = Set.insert name $ contextMacroIntegerParameters context,
        contextCheckSettings = CS False True
        }

-- | Typecheck the statements of a for loop strict.
typecheckForLoopInstances :: Context -> ForLoop -> Checked Context
typecheckForLoopInstances context (ForLoop header statements) = if inMacro then Right context else checkedContext where
    checkedContext = foldM checkIteration context =<< checkedIndices

    checkIteration :: Context -> Int -> Checked Context
    checkIteration cntxt i = fmap (resetContext . fst) $ typecheckNetworkStatements statements cntxt' where
        resetContext c = cntxt {
            contextChannelDeclarations = foldr Hash.delete (contextChannelDeclarations c) forloopChannels,
            contextBusDeclarations = foldr Hash.delete (contextBusDeclarations c) forloopChannels
            } where
                Just forloopChannels = contextForLoopChannels c
        cntxt' = cntxt{
            contextIntegerParameters = Hash.insert name i $ contextIntegerParameters cntxt,
            contextForLoopChannels = Just Set.empty
            }

    checkedIndices = liftM2 (\a b -> [a..b-1]) checkedMin checkedMax
    checkedMin = typecheckIntegerConstant context $ setSource minvalue
    checkedMax = typecheckIntegerConstant context $ setSource maxvalue

    ForLoopHeader name minvalue maxvalue = removeSourceInfo header
    setSource = flip setSourceInfo header
    inMacro = checkMacro $ contextCheckSettings context

--------------------------------------------------------------------------------
-- Macros
--------------------------------------------------------------------------------

-- | Add a channel or bus macro parameter to the context
typecheckMacroParameter :: Context -> WithSourceInfo Parameter -> Checked Context
typecheckMacroParameter context parameter = case removeSourceInfo parameter of
    (ChannelParameter name) -> addChannelToContext context $ setSource name
    (BusParameter intexpr busname) -> typecheckBusDeclaration (setSource intexpr) busname context
    _ -> Right context
    where
        setSource = flip setSourceInfo parameter

-- | Add a macro input parameter to the context
typecheckMacroInputParameter :: Context -> WithSourceInfo Parameter -> Checked Context
typecheckMacroInputParameter context parameter = setInput =<< typecheckMacroParameter context parameter where
    setInput cntxt = case removeSourceInfo parameter of
        ChannelParameter name -> setChannelInput cntxt $ setSource name
        BusParameter _intexpr busname -> setBusInputs busname cntxt $ map setSource [0 .. (contextBusSize cntxt busname) - 1]
        IntParameter name -> addMacroIntegerParameterToContext context $ setSource name
        FunctionParameter sig -> addFunctionSignatureToContext context $ setSource sig
    setSource = flip setSourceInfo parameter

-- | Add a macro output parameter to the context
typecheckMacroOutputParameter :: Context -> WithSourceInfo Parameter -> Checked Context
typecheckMacroOutputParameter context parameter = setOutput =<< typecheckMacroParameter context parameter where
    setOutput cntxt = case removeSourceInfo parameter of
        ChannelParameter name -> setChannelOutput cntxt $ setSource name
        BusParameter _intexpr busname -> setBusOutputs busname cntxt $ map setSource [0 .. (contextBusSize cntxt busname) - 1]
        IntParameter{} -> fatal 1466 "Illegal"
        FunctionParameter{} -> fatal 1467 "Illegal"
    setSource = flip setSourceInfo parameter

-- | Typecheck a list of macro input parameters
typecheckMacroInputParameters :: [WithSourceInfo Parameter] -> Context -> Checked Context
typecheckMacroInputParameters = flip $ foldM typecheckMacroInputParameter

-- | Typecheck a list of macro output parameters
typecheckMacroOutputParameters :: [WithSourceInfo Parameter] -> Context -> Checked Context
typecheckMacroOutputParameters = flip $ foldM typecheckMacroOutputParameter

-- | Get the name of the variable defined by a parameter
parameterName :: Parameter -> Text
parameterName parameter = case parameter of
    ChannelParameter name -> name
    BusParameter _ name -> name
    IntParameter name -> name
    FunctionParameter (FunctionSignature _ name _) -> name

-- | Type checks a parameter
typecheckParameter :: Context -> WithSourceInfo Parameter -> Checked Parameter
typecheckParameter context parameter = case removeSourceInfo parameter of
    p@(ChannelParameter name) -> checkContextChannelParameterNameExists context (setSource name) *> Right p
    BusParameter intexpr name -> checkName *> checkSize *> fmap (flip BusParameter name) checkedIntegerExpression where
        checkName = checkContextChannelParameterNameExists context (setSource name)
        checkSize = typecheckIntegerPositive context =<< fmap setSource checkedIntegerExpression
        checkedIntegerExpression = typecheckIntegerExpression context $ setSource intexpr
    p@(IntParameter name) -> checkContextIntegerParameterNameExists context (setSource name) *> Right p
    FunctionParameter sig -> checkName *> fmap FunctionParameter checkedSignature where
        checkName = checkContextFunctionParameterNameExists context (setSource name)
        checkedSignature = liftM3 FunctionSignature checkedReturnType (Right name) checkedInputTypes
        checkedReturnType = typecheckTypeExpression context $ setSource returnType
        checkedInputTypes = mapM (typecheckTypeExpression context . setSource) inputTypes
        FunctionSignature returnType name inputTypes = sig
    where
        setSource = flip setSourceInfo parameter

-- | Type check a macro header
typecheckMacroHeader ::  Context -> WithSourceInfo MacroHeader -> Checked (WithSourceInfo MacroHeader)
typecheckMacroHeader context header = fmap setSource checkedHeader where
    checkedHeader = liftM3 MacroHeader checkedName checkedInputParameters checkedOutputParameters
    checkedInputParameters = mapM (typecheckParameter context . setSource) =<< (fmap fst checkedDuplicateNames)
    checkedOutputParameters = mapM (typecheckParameter context . setSource) =<< (fmap snd checkedDuplicateNames)
    checkedDuplicateNames = checkCondition checkDuplicateNames (inputparameters, outputparameters)
    checkedName = checkContextNameExists context $ setSource name

    checkDuplicateNames (i, o) = case listContainsDuplicates $ map parameterName (i ++ o) of
        True -> Left $ setSource DuplicateParameterNamesError
        False -> Right ()

    MacroHeader name inputparameters outputparameters = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Add a macro to the context. Precondition: header has been typechecked
addMacroToContext :: Context -> Macro -> Context
addMacroToContext context (Macro header statements) = addMacro $ removeSourceInfo header where
    addMacro (MacroHeader name i o) = context{contextMacros = Hash.insert name (getSourceInfo header, initialMacroContext i context, i, o, statements) (contextMacros context)}

-- | Type check the macro statement of a macro declaration. I.e. an uninstantiated macro.
typecheckMacroStatements :: Context -> WithSourceInfo MacroHeader -> [NetworkStatementSrc] -> Checked [NetworkStatementSrc]
typecheckMacroStatements context header statements = checkedStatements where
    checkedStatements = fmap snd $ typecheckNetworkStatements statements =<< fmap setInMacro checkedContext
    checkedContext = typecheckMacroOutputParameters (map setSource outputparameters) =<< typecheckMacroInputParameters (map setSource inputparameters) context'
    context' = initialMacroContext inputparameters context
    setInMacro cntxt = cntxt{contextCheckSettings = CS False True}
    MacroHeader _ inputparameters outputparameters = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Instantiate a list of parameters with a list of primitive expressions
instantiateMacroInputParameters :: Context -> WithSourceInfo [Parameter] -> [PrimitiveExpression] -> Context -> Checked Context
instantiateMacroInputParameters evalcontext parameters expressions context = case (removeSourceInfo parameters, expressions) of
    ([], []) -> Right context
    (p@BusParameter{}:params, exprs) -> instantiateMacroInputParameters evalcontext (setSource params) exprs =<< checkParam where
        checkParam = typecheckMacroInputParameter context $ setSource p
    (p@ChannelParameter{}:params, exprs) -> instantiateMacroInputParameters evalcontext (setSource params) exprs =<< checkParam where
        checkParam = typecheckMacroInputParameter context $ setSource p
    (_, PrimitiveChannel{}:exprs) -> instantiateMacroInputParameters evalcontext parameters exprs context
    ((IntParameter name):params, (PrimitiveInteger intexpr):exprs) -> instantiateMacroInputParameters evalcontext (setSource params) exprs =<< addInt where
        addInt = addIntegerParameterToContext context (setSource name) =<< typecheckIntegerConstant evalcontext (setSource intexpr)
    ((FunctionParameter sig):params, PrimitiveFunction{}:exprs) -> instantiateMacroInputParameters evalcontext (setSource params) exprs =<< addFunction where
        addFunction = addFunctionSignatureToContext context $ setSource sig
    _ -> fatal 1541 "Illegal"
    where
        setSource = flip setSourceInfo parameters

-- | Type check the macro statements of a macro instantiation.
typecheckMacroInstantiation :: Context -> Text -> [PrimitiveExpression] -> Checked ()
typecheckMacroInstantiation context macroname primitiveexpressions = checkedStatements *> Right () where
    checkedStatements = typecheckNetworkStatements statements =<< checkedContext
    checkedContext = typecheckMacroOutputParameters (map setSource outputs) =<< instantiateMacroInputParameters context (setSource inputs) primitiveexpressions context'
    (srcinfo, initialContext, inputs, outputs, statements) = lookupM (src 1524) macroname $ contextMacros context
    context' = initialContext{contextCheckSettings = CS True False}
    setSource = flip addSourceInfo srcinfo

-- | The initial macro context
initialMacroContext :: [Parameter] -> Context -> Context
initialMacroContext inputparameters context = context {
      contextBusDeclarations = Hash.empty -- previous bus declarations are no longer in scope
    , contextChannelDeclarations = Hash.empty -- previous channel declarations are no longer in scope
    , contextIntegerParameters = foldr Hash.delete (contextIntegerParameters context) integerParamNames -- Integer variables overridden by parameters are no longer in scope
    , contextMacroIntegerParameters = foldr Set.delete (contextMacroIntegerParameters context) integerParamNames -- Integer variables overridden by parameters are no longer in scope
    , contextForLoopChannels = Nothing
    , contextFunctionDeclarations = foldr Hash.delete (contextFunctionDeclarations context) functionParamNames -- Integer variables overridden by parameters are no longer in scope
    }
    where
        integerParamNames = mapMaybe integerParameterName inputparameters
        functionParamNames = mapMaybe functionParameterName inputparameters

--------------------------------------------------------------------------------
-- Processes
--------------------------------------------------------------------------------

-- | Add a process to the context. Precondition: header has been typechecked.
addProcessToContext :: Context -> Process -> Context
addProcessToContext context (Process header _) = addProcess $ removeSourceInfo header where
    addProcess (MacroHeader name i o) = context{contextProcesses = Hash.insert name (getSourceInfo header, i, o) (contextProcesses context)}

-- | Type check process contents
typecheckProcessContents :: Context -> WithSourceInfo ProcessHeader -> [WithSourceInfo ProcessContent] -> Checked [WithSourceInfo ProcessContent]
typecheckProcessContents context header contents = checkedContents =<< fmap setInMacro checkedContext where
    checkedContents cntxt = mapM (\c -> flip (typecheckProcessContent cntxt) c =<< pcontext) =<< typecheckInitialState contents
    checkedContext = typecheckMacroOutputParameters (map setSource outputparameters) =<< typecheckMacroInputParameters (map setSource inputparameters) context'
    context' = initialMacroContext inputparameters context
    setInMacro cntxt = cntxt{contextCheckSettings = CS False True}
    pcontext = foldM (addStateToContext context) emptyProcessContext contents
    MacroHeader _ inputparameters outputparameters = removeSourceInfo header
    setSource = flip setSourceInfo header

-- | Ensure there is exactly one initial state. If an initial state is not present, the first state is used as the initial state
typecheckInitialState :: [WithSourceInfo ProcessContent] -> Checked [WithSourceInfo ProcessContent]
typecheckInitialState contents = case filter (\c -> case removeSourceInfo c of InitialState{} -> True; _ -> False) contents of
    [] -> Right $ setInitialState contents
    [_] -> Right contents
    _:s2:_ -> Left $ setSourceInfo MultipleInitialStatesError s2
    where
        setInitialState [] = []
        setInitialState (c:cs) = case removeSourceInfo c of
            ContentState state -> (setSourceInfo (InitialState state) c):cs
            _ -> c:(setInitialState cs)

-- | Type check process content
typecheckProcessContent :: Context -> ProcessContext -> WithSourceInfo ProcessContent -> Checked (WithSourceInfo ProcessContent)
typecheckProcessContent context pcontext content = fmap (flip setSourceInfo content) $ case removeSourceInfo content of
    InitialState state -> fmap InitialState (typecheckProcessState context pcontext (setSourceInfo state content) <* checkNoParams) where
        checkNoParams = case params of
            [] -> Right ();
            _ -> Left $ setSourceInfo ProcessInitialStateParamsError content
        State _ params _ = state
    ContentState state -> fmap ContentState $ typecheckProcessState context pcontext (setSourceInfo state content)

-- | Type check a process state
typecheckProcessState :: Context -> ProcessContext -> WithSourceInfo ProcessState -> Checked ProcessState
typecheckProcessState context pcontext state = checkedState where
    checkedState = liftM2 (State name) checkedParams checkedContents
    checkedParams = typecheckVariableDeclarations context err checkName checkType params
    checkName cntxt = checkContextVariableNameExists cntxt . setSource
    checkType cntxt = typecheckTypeExpression cntxt . setSource
    checkedContents = mapM (\c -> flip (typecheckStateContent context) c =<< checkedPContext) contents
    checkedPContext = foldM addVarToPContext pcontext =<< checkedParams
    addVarToPContext c v = addVariableToProcessContext context c (setSource $ variableName v) (variableObject v)
    err = setSource . DuplicateVariableNamesError
    State name params contents = removeSourceInfo state
    setSource = flip setSourceInfo state

-- | Type check process state content
typecheckStateContent :: Context -> ProcessContext -> WithSourceInfo StateContent -> Checked (WithSourceInfo StateContent)
typecheckStateContent context pcontext content = fmap (flip setSourceInfo content) $ case removeSourceInfo content of
    StateTransition transition -> fmap StateTransition $ typecheckProcessTransition context pcontext (setSourceInfo transition content)

-- | Type check a process transition
typecheckProcessTransition :: Context -> ProcessContext -> WithSourceInfo ProcessTransition -> Checked ProcessTransition
typecheckProcessTransition context pcontext transition = fmap (Transition . reverse . snd) checkedContents where
    checkedContents = checkAtMostOneRead *> checkAtMostOneWrite *> checkOneNext *> foldM (typecheckTransitionContent context) (pcontext, []) contentsSrc
    checkAtMostOneRead = case length (filter (\c -> case c of TransitionRead{} -> True; _ -> False) contents) < 2 of
        True -> Right ()
        False -> Left $ setSourceInfo MultipleReadActionsError transition
    checkAtMostOneWrite = case length (filter (\c -> case c of TransitionWrite{} -> True; _ -> False) contents) < 2 of
        True -> Right ()
        False -> Left $ setSourceInfo MultipleWriteActionsError transition
    checkOneNext = case filter (\c -> case c of TransitionNext{} -> True; _ -> False) contents of
        [] -> Left $ setSourceInfo NoNextActionError transition
        [_] -> Right ()
        _ -> Left $ setSourceInfo MultipleNextActionsError transition
    Transition contentsSrc = removeSourceInfo transition
    contents = map removeSourceInfo contentsSrc

-- | Type check process transition content
typecheckTransitionContent :: Context -> (ProcessContext, [WithSourceInfo TransitionContent])
                          -> WithSourceInfo TransitionContent -> Checked (ProcessContext, [WithSourceInfo TransitionContent])
typecheckTransitionContent context (pcontext, checkedcontents) content = case removeSourceInfo content of
    TransitionRead channelname vtype vname -> combine checkedContext checkedContent where
        checkedContent = liftM3 TransitionRead checkedChannel checkedType (Right vname)
        checkedContext = addVariableToProcessContext context pcontext (setSource vname) vtype
        checkedChannel = checkChannelSize =<< typecheckChannelVariable context (setSource channelname)
        checkedType = typecheckTypeExpression context $ setSource vtype
    TransitionWrite channelname dataexpr -> combine (Right pcontext) checkedContent where
        checkedContent = liftM2 TransitionWrite checkedChannel checkedData
        checkedChannel = checkChannelSize =<< typecheckChannelVariable context (setSource channelname)
        checkedData = typecheckDataExpression context (toFunctionContext context pcontext) $ setSource dataexpr
    TransitionNext state arguments -> combine (Right pcontext) checkedContent where
        checkedContent = fmap (TransitionNext state) checkedArguments
        checkedArguments = typecheckVariablesMatch context fcontext (setSource arguments) =<< inputTypes
        fcontext = toFunctionContext context pcontext
        inputTypes = case Hash.lookup state $ processStates pcontext of
            Nothing -> Left . setSource $ UnknownStateError state
            Just (_, ts) -> Right ts
    TransitionGuard bool -> combine (Right pcontext) checkedContent where
        checkedContent = fmap TransitionGuard checkedBool
        checkedBool = typecheckBooleanExpression context (toFunctionContext context pcontext) $ setSource bool
    where
        combine = liftM2 (\cntxt cntnt -> (cntxt, (setSource cntnt):checkedcontents))
        checkChannelSize (chan, size) = case size of
            1 -> Right chan;
            s -> Left $ setSourceInfo (IllegalProcessChannelError chan s) content
        setSource = flip setSourceInfo content

-- | Context of a process
data ProcessContext = PC {
    processStates :: Hash.Map Text (SourceInformation, [TypeExpression]),
    processInputVariables :: Hash.Map Text TypeExpression
    }

-- | The empty process context
emptyProcessContext :: ProcessContext
emptyProcessContext = PC Hash.empty Hash.empty

-- | Transforms a process context to a function context
toFunctionContext :: Context -> ProcessContext -> FunctionContext
toFunctionContext context pcontext = emptyFunctionContext {
    functionInputVariables = fmap (toSUTypeExpression context) $ processInputVariables pcontext
    }

-- | Add a process state to the process context
addStateToContext :: Context -> ProcessContext -> WithSourceInfo ProcessContent -> Checked ProcessContext
addStateToContext context pcontext content = case removeSourceInfo content of
    InitialState state -> addStateToContext' state
    ContentState state -> addStateToContext' state
    where
        addStateToContext' :: ProcessState -> Checked ProcessContext
        addStateToContext' (State name params _) = liftM2 updateContext checkedName checkedTypes where
            updateContext n ts = pcontext{processStates = Hash.insert n (getSourceInfo content, ts) $ processStates pcontext}
            checkedName = case Hash.lookup name $ processStates pcontext of
                Nothing -> Right name
                Just (srcinfo, _) -> Left $ setSourceInfo (DoublyDefinedStateError srcinfo name) content
            checkedTypes = mapM (typecheckTypeExpression context . flip setSourceInfo content . variableObject) params

-- | Add a variable to the process context
addVariableToProcessContext :: Context -> ProcessContext -> WithSourceInfo Text -> TypeExpression -> Checked ProcessContext
addVariableToProcessContext context pcontext nameSrc vartype = fmap updateContext checkedName where
    updateContext n = pcontext {processInputVariables = Hash.insert n vartype $ processInputVariables pcontext}
    checkedName = case Hash.lookup name $ processInputVariables pcontext of
        Nothing -> checkContextVariableNameExists context $ setSource name
        Just{} -> Left . setSource . MultiplyDefinedNameError $ name +++ " was already declared as a process input variable."
    name = removeSourceInfo nameSrc
    setSource = flip setSourceInfo nameSrc

--------------------------------------------------------------------------------
-- Variable declarations
--------------------------------------------------------------------------------

-- | Type check a list of @VariableDeclaration@.
typecheckVariableDeclarations :: Context -> ([VariableDeclaration a] -> WithSourceInfo Error) -> TypeCheck Text -> TypeCheck a
                                    -> [VariableDeclaration a] -> Checked [VariableDeclaration a]
typecheckVariableDeclarations context err checkName checkObject = (mapM checkVariable =<<) . checkDuplicates where
    checkVariable (VariableDeclaration name object) = liftM2 VariableDeclaration (checkName context name) (checkObject context object)
    checkDuplicates vars = case listContainsDuplicates $ map variableName vars of
        True -> Left $ err vars
        False -> Right vars

--------------------------------------------------------------------------------
-- Network statements
--------------------------------------------------------------------------------

-- | Checks if a condition on bus sizes holds
checkBusSizeCondition :: Int -> Maybe Int -> NetworkStatementSrc -> Checked ()
checkBusSizeCondition bussize inputsize networkstatementSrc = case inputsize of
    Nothing -> Right ()
    Just size -> case bussize == size of
        True -> Right ()
        False -> Left $ setSourceInfo (UnequalBusSizeError bussize size) networkstatementSrc

-- | Type check a bus declaration and add it to the context
typecheckBusDeclaration :: WithSourceInfo IntegerExpression -> Text -> Context -> Checked Context
typecheckBusDeclaration intexpr busname context = checkedContext where
    checkedContext = join $ liftM3 addBusDeclarationToContext checkedSize (Right context) (Right $ setSource busname)
    checkedSize = typecheckIntegerPositive context intexpr
    setSource = flip setSourceInfo intexpr

-- | Typecheck an integer parameter declaration and add it to the context
typecheckIntegerParameter :: Text -> WithSourceInfo IntegerExpression -> Context -> Checked Context
typecheckIntegerParameter name intexpr context = checkedContext where
    checkedContext = addIntegerParameterToContext context (setSource name) =<< checkedInt
    checkedInt = if checkMacro $ contextCheckSettings context then Right 1 else typecheckIntegerConstant context intexpr
    setSource = flip setSourceInfo intexpr

-- | Does the first phase of type checking a network statement. Only the declarations of int parameters,
-- channel and bus declarations are handled.
-- N.B. The assumption is that integer parameters must be declared before they are used.
-- Channel and bus parameters may be declared after their usage.
typecheckNetworkStatementPhase1 :: Context -> NetworkStatementSrc -> Checked Context
typecheckNetworkStatementPhase1 context statement = case removeSourceInfo statement of
    (NetworkChannelDeclaration (ChannelDeclaration channelnames)) -> addChannelsToContext context $ map setSource channelnames
    (NetworkChannelDeclaration (ChannelDefinition channelnames _)) -> addChannelsToContext context $ map setSource channelnames
    (NetworkBusDeclaration (BusDeclaration intexpr busnames)) -> checkedContext where
        checkedContext = join $ liftM3 addBusDeclarationsToContext checkedSize (Right context) (Right $ map setSource busnames)
        checkedSize = typecheckIntegerPositive context $ setSource intexpr
    (NetworkBusDeclaration (BusDefinition intexpr busname _)) -> typecheckBusDeclaration (setSource intexpr) busname context
    (NetworkParameterDeclaration (ParameterDeclaration name intexpr)) -> typecheckIntegerParameter name (setSource intexpr) context
    _ -> Right context
    where
        setSource = flip setSourceInfo statement

-- | The second phase of type checking a network statements. Handles all remaining statements.
typecheckNetworkStatementPhase2 :: (Context, [NetworkStatementSrc]) -> NetworkStatementSrc -> Checked (Context, [NetworkStatementSrc])
typecheckNetworkStatementPhase2 (context, checkedstatements) statement = case removeSourceInfo statement of
    NetworkChannelDeclaration (ChannelDefinition channelnames networkprimitive) -> combine checkedContext checkedStatement where
        checkedContext = (flip setChannelInputs (map setSource channelnames) . fst3) =<< checkedPrimitive'
        checkedStatement = fmap (NetworkChannelDeclaration . ChannelDefinition channelnames . snd3) checkedPrimitive'
        checkedPrimitive' = (if checkMacro settings then Right else checkCondition busSizeCondition) =<< checkedPrimitive
        checkedPrimitive = typecheckNetworkPrimitive context networkprimitive
        busSizeCondition p = checkBusSizeCondition (length channelnames) (thrd3 p) statement
    NetworkChannelDeclaration ChannelDeclaration{} -> Right (context, statement:checkedstatements) -- This case is already handled during phase 1
    NetworkBusDeclaration (BusDefinition intexpr busname networkprimitive) -> combine checkedContext checkedStatement where
        checkedContext = (flip (setBusInputs busname) (map setSource [0 .. (contextBusSize context busname) - 1]) . fst3) =<< checkedPrimitive'
        checkedStatement = fmap (NetworkBusDeclaration . BusDefinition intexpr busname . snd3) checkedPrimitive'
        checkedPrimitive' = (if checkMacro settings then Right else checkCondition busSizeCondition) =<< checkedPrimitive
        busSizeCondition p = checkBusSizeCondition busSize (thrd3 p) statement
        busSize = contextBusSize context busname
        checkedPrimitive = typecheckNetworkPrimitive context networkprimitive
    NetworkBusDeclaration BusDeclaration{} -> Right (context, statement:checkedstatements) -- This case is already handled during phase 1
    NetworkLetStatement (LetStatement variables networkprimitive) -> combine (fmap fst3 checkedPrimitive) checkedStatement where
        checkedStatement = fmap NetworkLetStatement $ liftM2 LetStatement (fmap fst checkedVariables) (fmap snd3 checkedPrimitive')
        checkedPrimitive' = (if checkMacro settings then Right else checkCondition busSizeCondition) =<< checkedPrimitive
        checkedPrimitive = (\c -> typecheckNetworkPrimitive c networkprimitive) =<< setChannels
        setChannels = setChannelVariableInputs context =<< fmap (map setSource . fst) checkedVariables
        checkedVariables = typecheckChannelVariables context $ setSource variables
        busSizeCondition p = (\size -> checkBusSizeCondition size (thrd3 p) statement) =<< fmap snd checkedVariables
    NetworkNetworkPrimitive networkprimitive -> combine (fmap fst3 checkedPrimitive) checkedStatement where
        checkedStatement = fmap (NetworkNetworkPrimitive . removeSourceInfo . snd3) checkedPrimitive
        checkedPrimitive = typecheckNetworkPrimitive context $ setSource networkprimitive
    NetworkMacro (Macro header statements) -> combine checkedContext (fmap NetworkMacro checkedStatement) where
        checkedContext = fmap (addMacroToContext context) checkedStatement
        checkedStatement = liftM2 Macro checkedHeader checkedMacroStatements
        checkedMacroStatements = flip (typecheckMacroStatements context) statements =<< checkedHeader
        checkedHeader = typecheckMacroHeader context header
    NetworkTypeDeclaration typedeclaration -> combine checkedContext (fmap NetworkTypeDeclaration checkedTypeDeclaration) where
        checkedContext = (addTypeDeclarationToContext context $ setSource name) =<< checkedTypeDeclaration
        checkedTypeDeclaration = typecheckTypeDeclaration context $ setSource typedeclaration
        name = case typedeclaration of TypeStruct n _ -> n; TypeUnion n _ -> n; TypeEnum n _ -> n; TypeConst n -> n
    NetworkForLoop (ForLoop header statements) -> combine checkedContext $ fmap NetworkForLoop checkedStatement where
        checkedContext = typecheckForLoopInstances context =<< checkedStatement
        checkedStatement = liftM2 ForLoop checkedHeader checkedForLoopStatements
        checkedForLoopStatements = typecheckForLoopStatements context statements =<< fmap removeSourceInfo checkedHeader
        checkedHeader = typecheckForLoopHeader context header
    NetworkParameterDeclaration{} -> Right (context, statement:checkedstatements) -- This case is already handled during phase 1
    NetworkFunctionDeclaration functiondeclaration -> combine checkedContext (fmap NetworkFunctionDeclaration checkedDeclaration) where
        checkedContext = addFunctionDeclarationToContext context =<< checkedDeclaration
        checkedDeclaration = typecheckFunctionDeclaration context functiondeclaration
    NetworkPredicateDeclaration predicatedeclaration -> combine checkedContext (fmap NetworkPredicateDeclaration checkedDeclaration) where
        checkedContext = addPredicateDeclarationToContext context =<< checkedDeclaration
        checkedDeclaration = typecheckPredicateDeclaration context predicatedeclaration
    NetworkProcess (Process header contents) -> combine checkedContext (fmap NetworkProcess checkedStatement) where
        checkedContext = fmap (addProcessToContext context) checkedStatement
        checkedStatement = liftM2 Process checkedHeader checkedContents
        checkedContents = flip (typecheckProcessContents context) contents =<< checkedHeader
        checkedHeader = typecheckMacroHeader context header
    NetworkIfThenElse (IfThenElse bool thenStatements elseStatements) -> combine (checkedContext =<< boolVal) checkedStatement where
        checkedContext b = case checkMacro settings of
            True -> liftM2 joinContexts (fmap fst $ checkedThenStatements b) (fmap fst $ checkedElseStatements b)
            False -> fmap fst $ if b then checkedThenStatements b else checkedElseStatements b
        checkedStatement = fmap NetworkIfThenElse $ liftM3 IfThenElse checkedBool (fmap snd $ checkedThenStatements =<< boolVal) (fmap snd $ checkedElseStatements =<< boolVal)
        checkedThenStatements b = case checkMacro settings || b of
            True -> typecheckNetworkStatements thenStatements context{contextCheckSettings = settings{checkInputOutput = False}}
            False -> Right (context, thenStatements)
        checkedElseStatements b = case checkMacro settings || not b of
            True -> typecheckNetworkStatements elseStatements context{contextCheckSettings = settings{checkInputOutput = False}}
            False -> Right (context, elseStatements)
        boolVal = (if checkMacro settings then const $ Right True else typecheckBooleanConstant context) =<< fmap setSource checkedBool
        checkedBool = typecheckBooleanExpression context emptyFunctionContext $ setSource bool
    NetworkIncludeStatement{} -> fatal 1417 "Include statement should not be present!"
    where
        combine :: Checked Context -> Checked NetworkStatement -> Checked (Context, [NetworkStatementSrc])
        combine = liftM2 (\cntxt stat -> (cntxt, setSource stat : checkedstatements))
        settings = contextCheckSettings context
        setSource = flip setSourceInfo statement

-- | Check a condition on an object, and return the checked object
checkCondition :: (a -> Checked ()) -> a -> Checked a
checkCondition condition object = fmap (\_ -> object) $ condition object

-- | Perform the second phase of typechecking on a list of network statements
typecheckNetworkStatementsPhase2 :: [NetworkStatementSrc] -> Context -> Checked (Context, [NetworkStatementSrc])
typecheckNetworkStatementsPhase2 statements context = checkedStatements >>= checkInputOutputCompleteness' where
    checkedStatements = foldM typecheckNetworkStatementPhase2 (context, []) statements
    checkInputOutputCompleteness' :: (Context, [NetworkStatementSrc]) -> Checked (Context, [NetworkStatementSrc])
    checkInputOutputCompleteness' (cntxt, stats) = case checkInputOutput $ contextCheckSettings context of
        True -> fmap (\_ -> (cntxt, reverse stats)) $ checkCondition checkInputOutputCompleteness cntxt
        False -> Right (cntxt, reverse stats)

-- | Typecheck a list of network statements
typecheckNetworkStatements :: [NetworkStatementSrc] -> Context -> Checked (Context, [NetworkStatementSrc])
typecheckNetworkStatements statements context = result where
    result = context1 >>= typecheckNetworkStatementsPhase2 statements
    context1 = foldM typecheckNetworkStatementPhase1 context statements

--------------------------------------------------------------------------------
-- Network
--------------------------------------------------------------------------------

-- | Typecheck a network
typecheckNetwork :: Network -> Checked Network
typecheckNetwork (NetworkStatements statements) = fmap (NetworkStatements . snd) result where
    result = typecheckNetworkStatements statements emptyContext
