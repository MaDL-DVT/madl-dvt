{-|
Module      : Parser.MadlParser
Description : Parser for Madl files
Copyright   : (c) Wieger Wesselink 2015-2016, Sebastiaan J C Joosten 2015, Tessa Belder 2016

This module contains a parser for Madl files.
-}
module Parser.MadlParser where

import Data.Functor.Identity (Identity)

import Text.Parsec hiding (State)
import Text.Parsec.Expr
import Text.Parsec.String (Parser)

import Madl.SourceInformation

import Parser.MadlLexer
import Parser.MadlAST

import Data.List (isInfixOf)

-- | Parse a Madl file
madlParser :: SourceName -> String -> Either ParseError Network
madlParser = parse parseNetwork

-- | Add source info to an object
parseSourceInfo :: Parser a -> Parser (WithSourceInfo a)
parseSourceInfo objectParser = do
    source <- getInput
    pos <- getPosition
    object <- objectParser
    source' <- getInput
    return $ WSI object (take (length source - length source') source) pos

-- | Parse a 'Network'
parseNetwork :: Parser Network
parseNetwork = (NetworkStatements <$> (whiteSpace *> parseNetworkStatementList <* eof)) <?> "Network"

---------------------------------------------------------
-- * Network Statements
---------------------------------------------------------

-- | Parse a list of 'NetworkStatement's with source information
parseNetworkStatementList :: Parser [NetworkStatementSrc]
parseNetworkStatementList = (semiEnd $ parseSourceInfo parseNetworkStatement) <?> "NetworkStatementList"

-- | Parse a 'NetworkStatement'
parseNetworkStatement :: Parser NetworkStatement
parseNetworkStatement =
        NetworkChannelDeclaration   <$> parseChannelDeclaration
    <|> NetworkBusDeclaration       <$> parseBusDeclaration
    <|> NetworkFunctionDeclaration  <$> parseFunctionDeclaration
    <|> NetworkForLoop              <$> parseForLoop
    <|> NetworkIfThenElse           <$> (parseIfThenElseBrackets parseNetworkStatementList)
    <|> NetworkIncludeStatement     <$> parseIncludeStatement
    <|> NetworkLetStatement         <$> parseLetStatement
    <|> NetworkMacro                <$> parseMacro
    <|> NetworkNetworkPrimitive     <$> parseNetworkPrimitive
    <|> NetworkParameterDeclaration <$> parseParameterDeclaration
    <|> NetworkPredicateDeclaration <$> parsePredicateDeclaration
    <|> NetworkProcess              <$> parseProcess
    <|> NetworkTypeDeclaration      <$> parseTypeDeclaration
    <?> "Network statement"

---------------------------------------------------------
-- ** Bus Declaration

-- | Parse a 'BusDeclaration'
parseBusDeclaration :: Parser BusDeclaration
parseBusDeclaration = (do
    reserved "bus"
    i <- angles parseIntegerExpression
    name <- identifier
    primitive <- optionMaybe $ reservedOp ":=" *> parseNetworkPrimitiveSrc
    case primitive of
        Nothing -> do
            ids <- option [] $ comma *> (commaSep identifier)
            return $ BusDeclaration i (name:ids)
        Just p -> return $ BusDefinition i name p
    ) <?> "Bus declaration"


---------------------------------------------------------
-- ** Channel Declaration

-- | Parse a 'ChannelDeclaration'
parseChannelDeclaration :: Parser ChannelDeclaration
parseChannelDeclaration = (do
    reserved "chan"
    ids <- commaSep1 identifier
    primitive <- optionMaybe $ reservedOp ":=" *> parseNetworkPrimitiveSrc
    case primitive of
        Nothing -> return $ ChannelDeclaration ids
        Just p -> return $ ChannelDefinition ids p
    ) <?> "Channel declaration"

---------------------------------------------------------
-- ** For Loop

-- | Parse a 'ForLoop'
parseForLoop :: Parser ForLoop
parseForLoop = (do
    reserved "for"
    header <- parens $ parseSourceInfo parseForLoopHeader
    statements <- braces parseNetworkStatementList
    return $ ForLoop header statements
    ) <?> "For loop"

-- | Parse a 'ForLoopHeader'
parseForLoopHeader :: Parser ForLoopHeader
parseForLoopHeader = (do
    reserved "int"
    name <- identifier
    reservedOp "="
    low <- parseIntegerExpression
    semi
    _ <- identifier
    reservedOp "<"
    high <- parseIntegerExpression
    semi
    _ <- identifier
    reservedOp "++"
    return $ ForLoopHeader name low high
    ) <?> "For loop header"

---------------------------------------------------------
-- ** Function Declaration

-- | Parse a 'FunctionDeclaration'
parseFunctionDeclaration :: Parser FunctionDeclaration
parseFunctionDeclaration = (do
    header <- parseSourceInfo parseFunctionHeader
    body <- braces $ (parseSourceInfo parseFunctionBody) <* (optional semi)
    return $ FunctionDeclaration header body
    ) <?> "Function declaration"

-- | Parse a 'FunctionHeader'
parseFunctionHeader :: Parser FunctionHeader
parseFunctionHeader = (do
    reserved "function"
    name <- identifier
    arguments <- parens . commaSep $ parseVariableDeclaration parseTypeExpression
    colon
    returntype <- parseTypeExpression
    return $ FunctionHeader name arguments returntype
    ) <?> "Function Header"

-- | Parse a 'FunctionBody'
parseFunctionBody :: Parser FunctionBody
parseFunctionBody =
        FunctionBodySwitch          <$> (parseSwitchStatement $ parseSourceInfo parseFunctionBody)
    <|> FunctionBodyIfThenElse      <$> (parseIfThenElse $ parseSourceInfo parseFunctionBody)
    <|> try (FunctionBodyAssignment <$> (semiSepEnd1 parseFunctionAssignment))
    <|> try parseFunctionTypeSelection
    <|> FunctionBodyContent         <$> parseDataExpression
    <?> "Function Body"

-- | Parse a 'FunctionAssignment'
parseFunctionAssignment :: Parser FunctionAssignment
parseFunctionAssignment = (do
    lhs <- parseAttribute
    reservedOp "="
    rhs <- parseSourceInfo parseFunctionBody
    return $ FunctionAssignment lhs rhs
    ) <?> "Function Assignment"

-- | Parse a 'FunctionBodyTypeSelection'
parseFunctionTypeSelection :: Parser FunctionBody
parseFunctionTypeSelection = (do
    name <- identifier
    content <- braces . optionMaybe $ (parseSourceInfo parseFunctionBody) <* (optional semi)
    return $ FunctionBodyTypeSelection name content
    ) <?> "Function Type Selection"

---------------------------------------------------------
-- ** Include Statement

-- | Parse a 'IncludeStatement'
parseIncludeStatement :: Parser IncludeStatement
parseIncludeStatement = (do
    reserved "uses"
    name <- parseAttribute
    return $ IncludeStatement name
    ) <?> "Include statement"

---------------------------------------------------------
-- ** Let Statement

-- | Parse a 'LetStatement'
parseLetStatement :: Parser LetStatement
parseLetStatement = (do
    reserved "let"
    channels <- commaSep1 parseChannelVariable
    reservedOp ":="
    expr <- parseNetworkPrimitiveSrc
    return $ LetStatement channels expr
    ) <?> "Let statement"

---------------------------------------------------------
-- ** Macro

-- | Parse a 'Macro'
parseMacro :: Parser Macro
parseMacro = (do
    reserved "macro"
    header <- parseSourceInfo parseMacroHeader
    statements <- braces parseNetworkStatementList
    return $ Macro header statements
    ) <?> "Macro"

-- | Parse a 'MacroHeader'
parseMacroHeader :: Parser MacroHeader
parseMacroHeader = (do
    name <- identifier
    inputparameters <- parens $ commaSep parseInputParameter
    outputparameters <- option [] $ reservedOp "=>" *> commaSep parseOutputParameter
    return $ MacroHeader name inputparameters outputparameters
    ) <?> "Macro Header"

---------------------------------------------------------
-- ** Network Primitive

-- | Parse a 'NetworkPrimitive'
parseNetworkPrimitive :: Parser NetworkPrimitive
parseNetworkPrimitive =
        parseControlJoin
    <|> parseDeadSink
    <|> parseFControlJoin
    <|> parseFork
    <|> parseFunction
    <|> parseGuardQueue
    <|> parseJoitch
    <|> parseLoadBalancer
    <|> parseMatch
    <|> parseMerge
    <|> parseMultiMatch
    <|> parsePatientSource
    <|> parseQueue
    <|> parseSink
    <|> parseSource
    <|> parseSwitch
    <|> parseVars
    <|> parseCut
    <|> parseUserDefinedPrimitive
    <?> "Network Primitive"

-- | Parse a 'NetworkPrimitive' with source information
parseNetworkPrimitiveSrc :: Parser (NetworkPrimitiveSrc)
parseNetworkPrimitiveSrc = parseSourceInfo parseNetworkPrimitive

---------------------------------------------------------
-- ** Parameter Declaration

-- | Parse a 'ParameterDeclaration'
parseParameterDeclaration :: Parser ParameterDeclaration
parseParameterDeclaration = (do
    reserved "param"
    reserved "int"
    name <- identifier
    reservedOp "="
    expr <- parseIntegerExpression
    return $ ParameterDeclaration name expr
    ) <?> "Parameter declaration"

---------------------------------------------------------
-- ** Predicate Declaration

-- | Parse a 'PredicateDeclaration'
parsePredicateDeclaration :: Parser PredicateDeclaration
parsePredicateDeclaration = (do
    header <- parseSourceInfo parsePredicateHeader
    body <- braces $ (parseSourceInfo parsePredicateBody) <* optional semi
    return $ PredicateDeclaration header body
    ) <?> "Predicate declaration"

-- | Parse a 'PredicateHeader'
parsePredicateHeader :: Parser PredicateHeader
parsePredicateHeader = (do
    reserved "pred"
    name <- identifier
    arguments <- parens . commaSep $ parseVariableDeclaration parseTypeExpression
    return $ PredicateHeader name arguments
    ) <?> "Preciate Header"

-- | Parse a 'PredicateBody'
parsePredicateBody :: Parser PredicateBody
parsePredicateBody =
        PredicateBodySwitch <$> (parseSwitchStatement $ parseSourceInfo parsePredicateBody)
    <|> PredicateBodyIfThenElse <$> (parseIfThenElse $ parseSourceInfo parsePredicateBody)
    <|> PredicateBodyBool <$> parseBooleanExpression
    <?> "Predicate Body"

---------------------------------------------------------
-- ** Process

-- | Parse a 'Process'
parseProcess :: Parser Process
parseProcess = (do
    reserved "process"
    header <- parseSourceInfo parseProcessHeader
    statements <- braces . semiEnd $ parseSourceInfo parseProcessContent
    return $ Process header statements
    ) <?> "Process"

-- | Parse a 'ProcessHeader'
parseProcessHeader :: Parser ProcessHeader
parseProcessHeader =
        parseMacroHeader
    <?> "Process Header"

-- | Parse a 'ProcessContent'
parseProcessContent :: Parser ProcessContent
parseProcessContent =
        ContentState <$> parseProcessState --todo(tssb): add parsing of initial state when there's separate syntax for this.
    <?> "Process content"

-- | Parse a 'ProcessState'
parseProcessState :: Parser ProcessState
parseProcessState = (do
    reserved "state"
    name <- identifier
    parameters <- parens $ commaSep parseStateParameter
    contents <- braces . semiEnd $ parseSourceInfo parseStateContent
    return $ State name parameters contents
    ) <?> "Process state"

-- | Parse a 'StateContent'
parseStateContent :: Parser StateContent
parseStateContent =
        StateTransition <$> parseProcessTransition
    <?> "State transition"

-- | Parse a 'StateParameter'
parseStateParameter :: Parser (VariableDeclaration TypeExpression)
parseStateParameter = (do
    paramType <- parseTypeExpression
    paramName <- identifier
    return $ VariableDeclaration paramName paramType
    ) <?> "State type parameter"

-- | Parse a 'ProcessTransition'
parseProcessTransition :: Parser ProcessTransition
parseProcessTransition = (do
    reserved "trans"
    contents <- braces . semiEnd $ parseSourceInfo parseTransitionContent
    return $ Transition contents
    ) <?> "Process transition"

-- | Parse a 'TransitionContent'
parseTransitionContent :: Parser TransitionContent
parseTransitionContent =
        parseTransitionNext
    <|> parseTransitionGuard
    <|> try parseTransitionWrite
    <|> parseTransitionRead
    <?> "Transition content"

-- | Parse a 'TransitionRead'
parseTransitionRead :: Parser TransitionContent
parseTransitionRead = (do
    packetType <- parseTypeExpression
    varName <- identifier
    reservedOp "<-"
    inChannel <- parseChannelVariable
    return $ TransitionRead inChannel packetType varName
    ) <?> "Transition Read"

-- | Parse a 'TransitionWrite'
parseTransitionWrite ::Parser TransitionContent
parseTransitionWrite = (do
    packet <- parseDataExpression
    reservedOp "->"
    outChannel <- parseChannelVariable
    return $ TransitionWrite outChannel packet
    ) <?> "Transition Write"

-- | Parse a 'TransitionNext'
parseTransitionNext :: Parser TransitionContent
parseTransitionNext = (do
    reserved "next"
    nextstate <- identifier
    parameters <- parens $ commaSep parseDataExpression
    return $ TransitionNext nextstate parameters
    ) <?> "Transition Next"

-- | Parse a 'TransitionGuard'
parseTransitionGuard :: Parser TransitionContent
parseTransitionGuard = (do
    reserved "guard"
    guard <- parseBooleanExpression
    return $ TransitionGuard guard
    ) <?> "Transition Guard"

---------------------------------------------------------
-- ** Type Declaration

-- | Parse a 'TypeDeclaration'
parseTypeDeclaration :: Parser TypeDeclaration
parseTypeDeclaration =
        parseStruct
    <|> parseUnion
    <|> parseEnum
    <|> parseConst
    <?> "Type declaration"

-- | Parse a 'TypeConst'
parseConst :: Parser TypeDeclaration
parseConst = (do
    reserved "const"
    name <- identifier
    return $ TypeConst name
    ) <?> "Const"

-- | Parse a 'TypeEnum'
parseEnum :: Parser TypeDeclaration
parseEnum = (do
    reserved "enum"
    name <- identifier
    fields <- braces $ semiSepEnd identifier
    return $ TypeEnum name fields
    ) <?> "Enumeration"

-- | Parse a 'TypeStruct'
parseStruct :: Parser TypeDeclaration
parseStruct = (do
    reserved "struct"
    name <- identifier
    fields <- braces . semiSepEnd $ parseVariableDeclaration parseSUTypeExpression
    return $ TypeStruct name fields
    ) <?> "Struct"

-- | Parse a 'TypeUnion'
parseUnion :: Parser TypeDeclaration
parseUnion = (do
    reserved "union"
    name <- identifier
    fields <- braces . semiSepEnd $ parseVariableDeclaration parseSUTypeExpression
    return $ TypeUnion name fields
    ) <?> "Union"

-- | Parse a 'SUTypeExpression'
parseSUTypeExpression :: Parser SUTypeExpression
parseSUTypeExpression =
        parseUnnamedStruct
    <|> parseUnnamedUnion
    <|> parseUnnamedEnumeration
    <|> SUTypeRange <$> parseRangeExpression
    <|> SUTypeVariable <$> parseTypeExpression
    <?> "SU Type expression"

-- | Parse a 'SUTypeEnumeration'
parseUnnamedEnumeration :: Parser SUTypeExpression
parseUnnamedEnumeration = (do
    reserved "enum"
    fields <- braces $ semiSepEnd identifier
    return $ SUTypeEnumeration fields
    ) <?> "Unnamed enumeration"

-- | Parse a 'SUTypeStruct'
parseUnnamedStruct :: Parser SUTypeExpression
parseUnnamedStruct = (do
    reserved "struct"
    fields <- braces . semiSepEnd $ parseVariableDeclaration parseSUTypeExpression
    return $ SUTypeStruct fields
    ) <?> "Unnamed struct"

-- | Parse a 'SUTypeUnion'
parseUnnamedUnion :: Parser SUTypeExpression
parseUnnamedUnion = (do
    reserved "union"
    fields <- braces . semiSepEnd $ parseVariableDeclaration parseSUTypeExpression
    return $ SUTypeUnion fields
    ) <?> "Unnamed union"

---------------------------------------------------------
-- * Expressions
---------------------------------------------------------

---------------------------------------------------------
-- ** Boolean Expression

-- | Parse a 'BooleanExpression'
parseBooleanExpression :: Parser BooleanExpression
parseBooleanExpression = buildExpressionParser booleanOperators parseBooleanAtom <?> "Boolean expression"

-- | Table of boolean operators
booleanOperators :: OperatorTable String () Identity BooleanExpression
booleanOperators = [
      [Prefix (reservedOp "!"  >> return (BooleanUnary  NOT ))          ]
    , [Infix  (reservedOp "&&" >> return (BooleanBinary AND )) AssocLeft
      ,Infix  (reservedOp "||" >> return (BooleanBinary OR  )) AssocLeft]
    ]

-- | Parse a 'BooleanExpression' atom
parseBooleanAtom :: Parser BooleanExpression
parseBooleanAtom =
        try (parens parseBooleanExpression)
    <|> try parseBooleanComparison
    <|> (reserved "true"  >> return BooleanTrue)
    <|> (reserved "false" >> return BooleanFalse)
    <|> parseBooleanPredicate
    <?> "Boolean Atom"

-- | Parse a 'BooleanPredicateApplication'
parseBooleanPredicate :: Parser BooleanExpression
parseBooleanPredicate = (do
    predicate <- parsePredicateExpression
    operands <- parens $ commaSep parseDataExpression
    return $ BooleanPredicateApplication predicate operands
    ) <?> "Boolean Predicate"

-- | Parse a 'BooleanComparison'
parseBooleanComparison :: Parser BooleanExpression
parseBooleanComparison = (do
    left <- parseDataExpression
    op <- parseComparisonOperator
    right <- parseDataExpression
    return $ BooleanComparison op left right
    ) <?> "Boolean Comparison"

-- | Parse a 'ComparisonOperator'
parseComparisonOperator :: Parser ComparisonOperator
parseComparisonOperator =
        (reservedOp "<=" >> return AtMost)
    <|> (reservedOp ">=" >> return AtLeast)
    <|> (reservedOp "==" >> return EqualTo)
    <|> (reservedOp "!=" >> return NotEqualTo)
    <|> (reservedOp ">"  >> return GreaterThan)
    <|> (reservedOp "<"  >> return LessThan)
    <?> "Comparison Operator"

---------------------------------------------------------
-- ** Channel expression

-- | Parse a 'ChannelExpression'
parseChannelExpression :: Parser ChannelExpression
parseChannelExpression =
        try (ChannelPrimitive <$> parseNetworkPrimitiveSrc)
    <|> ChannelId <$> parseChannelVariable
    <?> "Channel expression"

-- | Parse a 'ChannelExpression' that is not a single string
parseChannelExpressionNoString :: Parser ChannelExpression
parseChannelExpressionNoString =
        try (ChannelId <$> parseChannelVariableNoString)
    <|> ChannelPrimitive <$> parseNetworkPrimitiveSrc
    <?> "Channel expression no string"

---------------------------------------------------------
-- ** Data expression

-- | Parse a 'DataExpression'
parseDataExpression :: Parser DataExpression
parseDataExpression =
        try parseDataFunctionApplication
    <|> fmap toDataExpression parseDataIntegerExpression
    <?> "Data expression" where
      toDataExpression :: DataIntegerExpression -> DataExpression
      toDataExpression (DataIntegerUnknown name) = DataUnknown name
      toDataExpression (DataIntegerAttribute names) = DataAttribute names
      toDataExpression dataIntegerExpression = DataInteger dataIntegerExpression

-- | Parse a 'DataFunctionApplication'
parseDataFunctionApplication :: Parser DataExpression
parseDataFunctionApplication = (do
    function <- parseFunctionExpression
    operands <- parens $ commaSep parseDataExpression
    return $ DataFunctionApplication function operands
    ) <?> "Data function application"

-- | Parse a 'DataIntegerExpression'
parseDataIntegerExpression :: Parser DataIntegerExpression
parseDataIntegerExpression = buildExpressionParser dataIntegerOperators parseDataIntegerAtom <?> "Data integer expression"

-- | Table of integer operators
dataIntegerOperators :: OperatorTable String () Identity DataIntegerExpression
dataIntegerOperators = [
      [Infix  (reservedOp "*"   >> return (DataIntegerBinary Mult )) AssocLeft]
    , [Infix  (reservedOp "+"   >> return (DataIntegerBinary Plus )) AssocLeft
      ,Infix  (reservedOp "-"   >> return (DataIntegerBinary Minus)) AssocLeft]
    , [Infix  (reservedOp "%"   >> return (DataIntegerBinary Mod  )) AssocLeft]
    ]

-- | Parse a 'DataIntegerExpression' atom
parseDataIntegerAtom :: Parser DataIntegerExpression
parseDataIntegerAtom =
        parens parseDataIntegerExpression
    <|> DataIntegerNumber <$> decimal
    <|> try (DataIntegerAttribute <$> parseAttributeNoString)
    <|> DataIntegerUnknown <$> identifier
    <?> "Data integer atom"

---------------------------------------------------------
-- ** Function expression

-- | Parse a 'FunctionExpression'
parseFunctionExpression :: Parser FunctionExpression
parseFunctionExpression =
        FunctionVariable <$> identifier
    <?> "Function expression"

---------------------------------------------------------
-- ** Integer expression

-- | Parse a 'IntegerExpression'
parseIntegerExpression :: Parser IntegerExpression
parseIntegerExpression = buildExpressionParser integerOperators parseIntegerAtom <?> "Integer expression"

-- | Table of integer operators
integerOperators :: OperatorTable String () Identity IntegerExpression
integerOperators = [
      [Infix  (reservedOp "*"   >> return (IntegerBinary Mult )) AssocLeft]
    , [Infix  (reservedOp "+"   >> return (IntegerBinary Plus )) AssocLeft
      ,Infix  (reservedOp "-"   >> return (IntegerBinary Minus)) AssocLeft]
    , [Infix  (reservedOp "%"   >> return (IntegerBinary Mod  )) AssocLeft]
    ]

-- | Parse an 'IntegerExpression' atom
parseIntegerAtom :: Parser IntegerExpression
parseIntegerAtom =
        parens parseIntegerExpression
    <|> IntegerNumber <$> decimal
    <|> IntegerVariable <$> identifier
    <?> "Integer atom"

---------------------------------------------------------
-- ** Predicate expression

-- | Parse a 'PredicateExpression'
parsePredicateExpression :: Parser PredicateExpression
parsePredicateExpression =
        PredicateVariable <$> identifier
    <?> "Predicate expression"

---------------------------------------------------------
-- ** Primitive expression

-- | Parse a 'PrimitiveExpression'
parsePrimitiveExpression :: Parser PrimitiveExpression
parsePrimitiveExpression = (fmap toUnknown $ -- Transform IntegerVariables to PrimitiveUnknowns
        try (PrimitiveChannel <$> parseChannelExpressionNoString)
    <|> PrimitiveInteger <$> parseIntegerExpression) -- All strings are parsed as IntegerVariables
    <?> "Primtive expression"
    where
        toUnknown :: PrimitiveExpression -> PrimitiveExpression
        toUnknown (PrimitiveInteger (IntegerVariable name)) = PrimitiveUnknown name
        toUnknown expression = expression

-- | Parse a 'JoitchExpression'
parseJoitchExpression :: Parser JoitchExpression
parseJoitchExpression =
        (reserved "otherwise" >> return JoitchOtherwise)
    <|> JoitchPredicate <$> parsePredicateExpression
    <?> "Joitch expression"

-- | Parse a 'SwitchExpression'
parseSwitchExpression :: Parser SwitchExpression
parseSwitchExpression =
        (reserved "otherwise" >> return SwitchOtherwise)
    <|> try (SwitchBooleanExpression <$> parseBooleanExpression)
    <|> SwitchUnknown <$> identifier
    <?> "Switch expression"

---------------------------------------------------------
-- ** Range expression

-- | Parse a 'RangeExpression'
parseRangeExpression :: Parser RangeExpression
parseRangeExpression = (do
    (first, second) <- brackets $ do
        first <- parseIntegerExpression
        reservedOp ":"
        second <- parseIntegerExpression
        return (first, second)
    return $ RangeExpression first second
    ) <?> "Range expression"

---------------------------------------------------------
-- ** Type expression

-- | Parse a 'TypeExpression'
parseTypeExpression :: Parser TypeExpression
parseTypeExpression =
        TypeVariable <$> identifier
    <?> "Type expression"

---------------------------------------------------------
-- * Other
---------------------------------------------------------

---------------------------------------------------------
-- ** Attribute

-- | Parse a 'Attribute'
parseAttribute :: Parser Attribute
parseAttribute = sepBy1 identifier dot <?> "Attribute"

-- | Parse an 'Attribute' that is not a single string
parseAttributeNoString :: Parser Attribute
parseAttributeNoString = (do
    first <- identifier <* dot
    rest <- sepBy1 identifier dot
    return (first:rest)
    ) <?> "Attribute no string"

---------------------------------------------------------
-- ** Channel variable

-- | Parse a 'ChannelVariable'
parseChannelVariable :: Parser ChannelVariable
parseChannelVariable = (do
    name <- identifier
    value <- optionMaybe (brackets parseIntegerExpression)
    case value of
        Nothing -> return $ UnknownVariable name
        Just i -> return $ BusIndex name i
    ) <?> "Channel variable"

-- | Parse a 'ChannelVariable' that is not a single string
parseChannelVariableNoString :: Parser ChannelVariable
parseChannelVariableNoString = (do
    name <- identifier
    value <- brackets parseIntegerExpression
    return $ BusIndex name value
    ) <?> "Channel variable no string"

---------------------------------------------------------
-- ** If then else

-- | Parser an 'IfThenElse' statement, generalized over its return type (i.e. the type of the expressions in the 'then' and 'else' clauses).
-- Curly brackets around the 'then' and 'else' clauses are optional.
-- The content of the 'then' clause may be ended with a semi-colon.
-- The content of the 'else' clause may be ended with a semi-colon if it is enclosed in curly brackets.
parseIfThenElse :: Parser a -> Parser (IfThenElse a)
parseIfThenElse parseContent = (do
    reserved "if"
    condition <- parens parseBooleanExpression
    thencase <- (braces $ parseContent <* (optional semi)) <|> (parseContent <* (optional semi))
    reserved "else"
    elsecase <- (braces $ parseContent <* (optional semi)) <|> parseContent
    return $ IfThenElse condition thencase elsecase
    ) <?> "If-then-else"

-- | Parser an 'IfThenElse' statement, generalized over its return type (i.e. the type of the expressions in the 'then' and 'else' clauses).
-- Curly brackets around the 'then' and 'else' clauses are mandatory.
parseIfThenElseBrackets :: Parser a -> Parser (IfThenElse a)
parseIfThenElseBrackets parseContent = (do
    reserved "if"
    condition <- parens parseBooleanExpression
    thencase <- braces parseContent
    reserved "else"
    elsecase <- braces parseContent
    return $ IfThenElse condition thencase elsecase
    ) <?> "If-then-else mandatory brackets"

---------------------------------------------------------
-- ** Parameter

-- | Parse an input 'Parameter'
parseInputParameter :: Parser Parameter
parseInputParameter =
        ChannelParameter <$> (reserved "chan" >> identifier)
    <|> parseBusParameter
    <|> IntParameter <$> (reserved "int" >> identifier)
    <|> FunctionParameter <$> parseFunctionSignature
    <?> "Input parameter"

-- | Parse an output 'Parameter'
parseOutputParameter :: Parser Parameter
parseOutputParameter =
        ChannelParameter <$> (reserved "chan" >> identifier)
    <|> parseBusParameter
    <?> "Output parameter"

-- | Parse a 'BusParameter'
parseBusParameter :: Parser Parameter
parseBusParameter = (do
    reserved "bus"
    i <- angles parseIntegerExpression
    name <- identifier
    return $ BusParameter i name
    ) <?> "Bus parameter"

---------------------------------------------------------
-- ** Function signature

-- | Parse a 'FunctionSignature'
parseFunctionSignature :: Parser FunctionSignature
parseFunctionSignature = (do
    rtype <- parseTypeExpression
    name <- identifier
    ids <- parens $ commaSep parseTypeExpression
    return $ FunctionSignature rtype name ids
    ) <?> "Function signature"

---------------------------------------------------------
-- ** Switch statement

-- | Parse a 'SwitchStatement'
parseSwitchStatement :: Parser a -> Parser (SwitchStatement a)
parseSwitchStatement parseSwitchBody = (do
    reserved "switch"
    name <- parseAttribute
    cases <- braces . semiSepEnd $ parseSwitchCase parseSwitchBody
    return $ SwitchStatement name cases
    ) <?> "Switch statement"

-- | Parse a 'SwitchCase'
parseSwitchCase :: Parser a -> Parser (SwitchCase a)
parseSwitchCase parseSwitchBody = (do
    reserved "case"
    lhs <- identifier
    reservedOp ":"
    rhs <- parseSwitchBody
    return $ SwitchCase lhs rhs
    ) <?> "Switch case"

---------------------------------------------------------
-- ** Variable declaration

-- | Parse a 'VariableDeclaration'
parseVariableDeclaration :: Parser a -> Parser (VariableDeclaration a)
parseVariableDeclaration parseVariableType = (do
    lhs <- identifier
    reservedOp ":"
    rhs <- parseVariableType
    return $ VariableDeclaration lhs rhs
    ) <?> "Variable Declaration"

---------------------------------------------------------
-- * Network Primitives
---------------------------------------------------------

-- | Parse a 'ControlJoin' primitive
parseControlJoin :: Parser NetworkPrimitive
parseControlJoin = (do
    reserved "CtrlJoin"
    (a, b) <- parens $ do
        a <- parseChannelExpression; comma
        b <- parseChannelExpression
        return (a, b)
    l <- parseLabelDeclaration
    return $ ControlJoin a b l
    ) <?> "ControlJoin"

-- | Parse a 'DeadSink' primitive
parseDeadSink :: Parser NetworkPrimitive
parseDeadSink = (do
    reserved "DeadSink"
    i <- parens parseChannelExpression
    l <- parseLabelDeclaration
    return $ DeadSink i l
    ) <?> "DeadSink"

-- | Parse a 'FControlJoin' primitive
parseFControlJoin :: Parser NetworkPrimitive
parseFControlJoin = (do
    reserved "FCtrlJoin"
    (p, a, b) <- parens $ do
        p <- parsePredicateExpression; comma
        a <- parseChannelExpression; comma
        b <- parseChannelExpression
        return (p, a, b)
    l <- parseLabelDeclaration
    return $ FControlJoin p a b l
    ) <?> "FControlJoin"

-- | Parse a 'Fork' primitive
parseFork :: Parser NetworkPrimitive
parseFork = (do
    reserved "Fork"
    i <- parens parseChannelExpression
    l <- parseLabelDeclaration
    return $ Fork i l
    ) <?> "Fork"

-- | Parse a 'Function' primitive
parseFunction :: Parser NetworkPrimitive
parseFunction = (do
    reserved "Function"
    (f, i) <- parens $ do
        f <- parseFunctionExpression; comma
        i <- parseChannelExpression
        return (f, i)
    l <- parseLabelDeclaration
    return $ Function f i l
    ) <?> "Function"

-- | Parse a 'GuardQueue' primitive
parseGuardQueue :: Parser NetworkPrimitive
parseGuardQueue = (do
    reserved "GuardQueue"
    (s, ib, ig) <- parens $ do
        s <- parseIntegerExpression; comma
        ib <- parseChannelExpression; comma
        ig <- parseChannelExpression
        return (s, ib, ig)
    l <- parseLabelDeclaration
    return $ GuardQueue s ib ig l
    ) <?> "GuardQueue"

-- | Parse a 'Joitch' primitive
parseJoitch :: Parser NetworkPrimitive
parseJoitch = (do
    reserved "Joitch"
    (a, b, preds) <- parens $ do
        a <- parseChannelExpression; comma
        b <- parseChannelExpression; comma
        preds <- commaSep1 parseJoitchExpression
        return (a, b, preds)
    l <- parseLabelDeclaration
    return $ Joitch a b preds l
    ) <?> "Joitch"

-- | Parse a 'LoadBalancer' primitive
parseLoadBalancer :: Parser NetworkPrimitive
parseLoadBalancer = (do
    reserved "LoadBalancer"
    i <- parens parseChannelExpression
    l <- parseLabelDeclaration
    return $ LoadBalancer i l
    ) <?> "LoadBalancer"

-- | Parse a 'Match' primitive
parseMatch :: Parser NetworkPrimitive
parseMatch = (do
    reserved "Match"
    (p, mIn, dIn) <- parens $ do
        p <- parsePredicateExpression; comma
        mIn <- parseChannelExpression; comma
        dIn <- parseChannelExpression
        return (p, mIn, dIn)
    l <- parseLabelDeclaration
    return $ Match p mIn dIn l
    ) <?> "Match"

-- | Parse a 'Merge' primitive
parseMerge :: Parser NetworkPrimitive
parseMerge = (do
    reserved "Merge"
    (a, b) <- parens $ do
        a <- parseChannelExpression; comma
        b <- parseChannelExpression
        return (a, b)
    l <- parseLabelDeclaration
    return $ Merge a b l
    ) <?> "Merge"

-- | Parse a 'MultiMatch' primitive
parseMultiMatch :: Parser NetworkPrimitive
parseMultiMatch = (do
    reserved "MultiMatch"
    (p, ins) <- parens $ do
        p <- parsePredicateExpression; comma
        ins <- commaSep1 parseChannelExpression
        return (p, ins)
    l <- parseLabelDeclaration
    return $ MultiMatch p ins l
    ) <?> "MultiMatch"

-- | Parse a 'PatientSource' primitive
parsePatientSource :: Parser NetworkPrimitive
parsePatientSource = (do
    reserved "PatientSource"
    e <- parens parseTypeExpression
    l <- parseLabelDeclaration
    return $ PatientSource e l
    ) <?> "PatientSource"

-- | Parse a 'Queue' primitive
parseQueue :: Parser NetworkPrimitive
parseQueue = (do
    reserved "Queue"
    (k, i) <- parens $ do
        k <- parseIntegerExpression; comma
        i <- parseChannelExpression
        return (k, i)
    l <- parseLabelDeclaration
    return $ Queue k i l
    ) <?> "Queue"


-- | Parse a label
-- | Labels may contain underscores, but not two consecutive ones
parseLabel :: Parser String
parseLabel = do
    x <- many1 $ alphaNum <|> char '_'
    if isInfixOf "__" x then unexpected $ "Label contains \"__\": " ++ x else return x

-- | Parse a label declaration
-- | A label could be empty 
parseLabelDeclaration :: Parser (Maybe String)
parseLabelDeclaration = do
    l <- optionMaybe $ try (do 
                                spaces
                                _ <- char '['
                                spaces
                                x <- parseLabel
                                spaces
                                _ <- char ']'
                                return x)
    return l        

-- | Parse a 'Sink' primitive
parseSink :: Parser NetworkPrimitive
parseSink = (do
    reserved "Sink"
    i <- parens parseChannelExpression
    l <- parseLabelDeclaration
    return $ Sink i l
    ) <?> "Sink"

-- | Parse a 'Source' primitive
parseSource :: Parser NetworkPrimitive
parseSource = (do
    reserved "Source"
    e <- parens parseTypeExpression
    l <- parseLabelDeclaration
    return $ Source e l
    ) <?> "Source"

-- | Parse a 'Switch' primitive
parseSwitch :: Parser NetworkPrimitive
parseSwitch = (do
    reserved "Switch"
    (i, sws) <- parens $ do
        i <- parseChannelExpression; comma
        sws <- commaSep1 parseSwitchExpression
        return (i, sws)
    l <- parseLabelDeclaration
    return $ Switch i sws l
    ) <?> "Switch"

-- | Parse a 'Vars' primitive
parseVars :: Parser NetworkPrimitive
parseVars = (do
    reserved "Vars"
    i <- parens parseChannelExpression
    l <- parseLabelDeclaration
    return $ Vars i l
    ) <?> "Vars"

-- | Parse a 'Cut' primitive
parseCut :: Parser NetworkPrimitive
parseCut = (do
    reserved "Cut"
    i <- parens parseChannelExpression
    l <- parseLabelDeclaration
    return $ Cut i l
    ) <?> "Cut"

-- | Parse a 'UserDefinedPrimitive'
parseUserDefinedPrimitive :: Parser NetworkPrimitive
parseUserDefinedPrimitive = (do
    name <- identifier
    exprn <- parens $ commaSep parsePrimitiveExpression
    l <- parseLabelDeclaration
    return $ UserDefinedPrimitive name exprn l
    ) <?> "User defined primitive"
