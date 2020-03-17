{-|
Module      : Parser.MadlAST
Description : Madl Abstract Syntax Tree
Copyright   : (c) Wieger Wesselink 2015-2016, Sebastiaan J C Joosten 2015, Tessa Belder 2016

This module contains an abstract syntax tree of the Madl language.
-}
module Parser.MadlAST where

import Utils.Text

import Madl.SourceInformation

-- | A network consists of a list of statements
data Network = NetworkStatements [NetworkStatementSrc] deriving (Show)

-- | A single network statement
data NetworkStatement = NetworkBusDeclaration       BusDeclaration
                      | NetworkChannelDeclaration   ChannelDeclaration
                      | NetworkForLoop              ForLoop
                      | NetworkFunctionDeclaration  FunctionDeclaration
                      | NetworkIfThenElse           (IfThenElse [NetworkStatementSrc])
                      | NetworkIncludeStatement     IncludeStatement
                      | NetworkLetStatement         LetStatement
                      | NetworkMacro                Macro
                      | NetworkNetworkPrimitive     NetworkPrimitive
                      | NetworkParameterDeclaration ParameterDeclaration
                      | NetworkPredicateDeclaration PredicateDeclaration
                      | NetworkProcess              Process
                      | NetworkTypeDeclaration      TypeDeclaration
                      deriving (Show)

-- | A network statement with source information
type NetworkStatementSrc = WithSourceInfo NetworkStatement

---------------------------------------------------------
-- * Network statements
---------------------------------------------------------

---------------------------------------------------------
-- ** Bus Declaration

-- | A declararation of a bus
data BusDeclaration = BusDeclaration IntegerExpression [Text] -- ^ Declaration of one or more busses
                    | BusDefinition IntegerExpression Text NetworkPrimitiveSrc -- ^ Declaration of single bus that is assigned an initiator
                    deriving (Show)

---------------------------------------------------------
-- ** Channel Declaration

-- | A declararation of a channel
data ChannelDeclaration = ChannelDeclaration [Text] -- ^ Declaration of one or more channels
                        | ChannelDefinition [Text] NetworkPrimitiveSrc-- ^ Declaration of one or more channels that are assigned an initiator
                        deriving (Show)

---------------------------------------------------------
-- ** For Loop

-- | @ForLoop header statements@
-- This represents: @for header { statements }@
data ForLoop = ForLoop (WithSourceInfo ForLoopHeader) [NetworkStatementSrc] deriving (Show)

-- | @ForLoopHeader name first last@
-- This represents: @(name = first; name < last; name++)@
data ForLoopHeader = ForLoopHeader Text IntegerExpression IntegerExpression deriving (Show)

---------------------------------------------------------
-- ** Function

-- | A function declaration consists of a header and a body
data FunctionDeclaration = FunctionDeclaration (WithSourceInfo FunctionHeader) FunctionBodySrc deriving (Show)

-- | @FunctionHeader name vars returntype@
-- This represents: @function name (vars) : returntype@
data FunctionHeader = FunctionHeader Text [VariableDeclaration TypeExpression] TypeExpression deriving (Show)

-- | The body of a function
data FunctionBody = FunctionBodySwitch (SwitchStatement FunctionBodySrc) -- ^ A switch statement returning a function body
                  | FunctionBodyAssignment [FunctionAssignment] -- ^ A list of assignments
                  | FunctionBodyTypeSelection Text (Maybe FunctionBodySrc) -- ^ @FunctionBodyTypeSelection name Nothing@ represents:
                  -- @name{}@. @FunctionBodyTypeSelection name (Just body)@ represents: @name{ body }@.
                  | FunctionBodyContent DataExpression -- ^ A value, such as an integer or a data packet
                  | FunctionBodyIfThenElse (IfThenElse FunctionBodySrc) -- ^ An if-then-else construction returning a function body
                  deriving (Show)
-- | A function body with source information
type FunctionBodySrc = WithSourceInfo FunctionBody

-- | A @FunctionAssignment attribute body@ represents: @attribute = body@
data FunctionAssignment = FunctionAssignment Attribute FunctionBodySrc deriving (Show)

---------------------------------------------------------
-- ** Include Statement

-- | @IncludeStatement [a, b]@ represents: @uses a.b@
data IncludeStatement = IncludeStatement Attribute deriving (Show)

---------------------------------------------------------
-- ** Let Statement

-- | @LetStatement channels primitive@ assigns an initiator to one or more channels
-- This represents: @let channels := primitive@
data LetStatement = LetStatement [ChannelVariable] NetworkPrimitiveSrc deriving (Show)

---------------------------------------------------------
-- ** Macro

-- | @Macro header statements@
-- This represents: @header { statements }@
data Macro = Macro (WithSourceInfo MacroHeader) [NetworkStatementSrc] deriving (Show)

-- | @MacroHeader name inputvars outputvars@
-- This represents: @macro name (inputvars) => outputvars@
data MacroHeader = MacroHeader Text [Parameter] [Parameter] deriving (Show)

---------------------------------------------------------
-- ** Network Primitive

-- | A MaDL primitive
data NetworkPrimitive = ControlJoin ChannelExpression ChannelExpression (Maybe String)
                      | DeadSink ChannelExpression (Maybe String)
                      | FControlJoin PredicateExpression ChannelExpression ChannelExpression (Maybe String)
                      | Fork ChannelExpression (Maybe String)
                      | Function FunctionExpression ChannelExpression (Maybe String)
                      | GuardQueue IntegerExpression ChannelExpression ChannelExpression (Maybe String)
                      | Joitch ChannelExpression ChannelExpression [JoitchExpression] (Maybe String)
                      | LoadBalancer ChannelExpression (Maybe String)
                      | Match PredicateExpression ChannelExpression ChannelExpression (Maybe String)
                      | Merge ChannelExpression ChannelExpression (Maybe String)
                      | MultiMatch PredicateExpression [ChannelExpression] (Maybe String)
                      | PatientSource TypeExpression (Maybe String)
                      | Queue IntegerExpression ChannelExpression (Maybe String)
                      | Buffer IntegerExpression ChannelExpression (Maybe String)
                      | Sink ChannelExpression (Maybe String)
                      | Source TypeExpression (Maybe String)
                      | Switch ChannelExpression [SwitchExpression] (Maybe String)
                      | Vars ChannelExpression (Maybe String)
                      | Cut ChannelExpression (Maybe String)
                      | UserDefinedPrimitive Text [PrimitiveExpression] (Maybe String) -- ^ For macros and processes
                      deriving (Show)

-- | A network primitive with source information
type NetworkPrimitiveSrc = WithSourceInfo NetworkPrimitive

---------------------------------------------------------
-- ** Parameter Declaration

-- | A global parameter of the network @ParameterDeclaration name val@ represents @param int name = val@
data ParameterDeclaration = ParameterDeclaration Text IntegerExpression deriving (Show)

---------------------------------------------------------
-- ** Predicate

-- | A predicate declaration consists of a header and a body
data PredicateDeclaration = PredicateDeclaration (WithSourceInfo PredicateHeader) PredicateBodySrc deriving (Show)

-- | @PredicateHeader name vars@
-- This represents: @pred name (vars)@
data PredicateHeader = PredicateHeader Text [VariableDeclaration TypeExpression] deriving (Show)

-- | The body of a predicate
data PredicateBody = PredicateBodyBool BooleanExpression -- ^ A boolean expression
                   | PredicateBodySwitch (SwitchStatement PredicateBodySrc) -- ^ A switch statement returning a predicate body
                   | PredicateBodyIfThenElse (IfThenElse PredicateBodySrc) -- ^ An if-then-else construction returning a predicate body
                   deriving (Show)

-- | A predicate body with source information
type PredicateBodySrc = WithSourceInfo PredicateBody

---------------------------------------------------------
-- ** Process

-- | @Process header content@
-- This represents: @header { content }@
data Process = Process (WithSourceInfo ProcessHeader) [WithSourceInfo ProcessContent] deriving (Show)

-- | @ProcessHeader name inputvars outputvars@
-- This represents: @process name (inputvars) => outputvars@
type ProcessHeader = MacroHeader

-- | Process content
data ProcessContent = InitialState ProcessState -- ^ The initial state of a process
                    | ContentState ProcessState -- ^ A state of a process
                     deriving (Show)

-- | @ProcessState name vars content@
-- This represents: @state name (vars) { content }@
data ProcessState = State Text [VariableDeclaration TypeExpression] [WithSourceInfo StateContent] deriving (Show)
-- | State content
data StateContent = StateTransition ProcessTransition -- ^ A transition
                  deriving (Show)

-- | @ProcessTransition content@
-- This represents: @trans { content }@
data ProcessTransition = Transition [WithSourceInfo TransitionContent] deriving (Show)
-- | Transition content
data TransitionContent = TransitionRead ChannelVariable TypeExpression Text -- ^ @TransitionRead chan type var@ represents @type var <- chan@
                       | TransitionWrite ChannelVariable DataExpression -- ^ @TransitionWrite chan pkt@ represents @pkt -> chan@
                       | TransitionGuard BooleanExpression -- ^ @TransitionGuard bool@ represents @guard bool@
                       | TransitionNext Text [DataExpression] -- ^ @TransitionNext state pkts@ represents @next state(pkts)@
                        deriving (Show)

---------------------------------------------------------
-- ** Type Declaration

-- | A type is a @struct@, a @union@, an @enumeration@, or a @constant@.
data TypeDeclaration = TypeStruct Text [VariableDeclaration SUTypeExpression] -- ^ A @TypeStruct name flds@ represents @struct name { flds }@
                     | TypeUnion Text [VariableDeclaration SUTypeExpression] -- ^ A @TypeUnion name flds@ represents @union name { flds }@
                     | TypeEnum Text [Text] -- ^ An @TypeEnum name values@ represents @enum name { values }@
                     | TypeConst Text -- ^ A @TypeConst name@ represents @const name@
                     deriving (Show)

-- | Variable types of struct/union attributes
data SUTypeExpression = SUTypeVariable TypeExpression -- ^ A reference to another type
                      | SUTypeEnumeration [Text] -- ^ An @SUTypeEnumeration values@ represents @enum { values }@
                      | SUTypeUnion [VariableDeclaration SUTypeExpression] -- ^ An @SUTypeUnion flds@ represents @union { flds }@
                      | SUTypeStruct [VariableDeclaration SUTypeExpression] -- ^ An @SUTypeStruct flds@ represents @struct { flds }@
                      | SUTypeRange RangeExpression -- ^ A @SUTypeRange range@ represents @[n:m]@, which represents a bitvector of size @abs(n - m) + 1@
                      deriving (Show, Eq)

---------------------------------------------------------
-- * Expressions
---------------------------------------------------------

---------------------------------------------------------
-- ** Boolean Expression

-- | A boolean expression
data BooleanExpression = BooleanTrue -- ^ The value 'True'
                       | BooleanFalse -- ^ The value 'False'
                       | BooleanUnary BooleanUnaryOperator BooleanExpression -- ^ A unary operator applied to a single boolean expression
                       | BooleanBinary BooleanBinaryOperator BooleanExpression BooleanExpression -- ^ A binary operator applied to two boolean expressions
                       | BooleanComparison ComparisonOperator DataExpression DataExpression -- ^ A relational operator applied to two data expressions
                       | BooleanPredicateApplication PredicateExpression [DataExpression] -- ^ A predicate applied to a list of data expressions
                       deriving (Show)

-- | Unary boolean operators
data BooleanUnaryOperator = NOT -- ^ Negation, @!@
                         deriving (Show)
-- | Binary boolean operators
data BooleanBinaryOperator = AND -- ^ Conjunction, @&&@
                           | OR  -- ^ Disjunction, @||@
                           deriving (Show)
-- | Relational boolean operators
data ComparisonOperator = EqualTo -- ^ Equal, @==@
                        | NotEqualTo -- ^ Unequal, @!=@
                        | LessThan -- ^ Less than, @<@
                        | AtMost -- ^ At most, @<=@
                        | GreaterThan -- ^ Greater than, @>@
                        | AtLeast -- ^ At least, @>=@
                        deriving (Show)

---------------------------------------------------------
-- ** Channel Expression
-- | A channel expression
data ChannelExpression = ChannelPrimitive NetworkPrimitiveSrc -- ^ The set of outcoming channels of a primitive
                       | ChannelId ChannelVariable -- ^ The set of channels represented by a channel variable
                       deriving (Show)

---------------------------------------------------------
-- ** Data Expression

-- | A data expression
data DataExpression = DataInteger DataIntegerExpression -- ^ Integer data
                    | DataType TypeExpression -- ^ A type that represents a single packet
                    | DataAttribute Attribute -- ^ An attribute
                    | DataFunctionApplication FunctionExpression [DataExpression] -- ^ A function applied to a list of data expressions
                    | DataUnknown Text -- ^ During parsing, strings will be mapped to DataUnknown.
                    -- During type checking, all DataUnknown instances will be converted to one of the the other options.
                    deriving (Show)

-- | A data expression representing an integer value
data DataIntegerExpression = DataIntegerNumber Integer -- ^ An integer number
                           | DataIntegerVariable Text -- ^ An identifier of an integer parameter (either global or local)
                           | DataIntegerAttribute Attribute -- ^ An attribute identifying a @Range@
                           | DataIntegerBinary IntegerBinaryOperator DataIntegerExpression DataIntegerExpression -- ^ A binary operator applied to two data integer expressions
                           | DataIntegerUnknown Text -- ^ During parsing, strings will be mapped to DataIntegerUnknown.
                           -- During type checking, all DataIntegerUnknown instances will be converted to DataIntegerVariable or DataIntegerAttribute.
                           deriving (Show)

---------------------------------------------------------
-- ** Function Expression

-- | A function epxression
data FunctionExpression = FunctionVariable Text -- ^ An identifier of a function
                        deriving (Show)

---------------------------------------------------------
-- ** Integer Expression

-- | An integer expression
data IntegerExpression = IntegerNumber Integer -- ^ An integer number
                       | IntegerVariable Text -- ^ An identifier of an integer parameter (either global or local)
                       | IntegerBinary IntegerBinaryOperator IntegerExpression IntegerExpression -- ^ A binary operator applied to two integer expressions
                       deriving (Show, Eq)

-- | Binary integer operators
data IntegerBinaryOperator = Plus -- ^ Addition, @+@
                           | Minus -- ^ Subtraction, @-@
                           | Mult -- ^ Multiplication, @*@
                           | Mod -- ^ Modulo, @%@
                           deriving(Show, Eq)

---------------------------------------------------------
-- ** Predication Expression

-- | A predicate expression
data PredicateExpression = PredicateVariable Text -- ^ An identifier of a predicate
                         deriving (Show)

---------------------------------------------------------
-- ** Primitive Expressions

-- | Expressions that can be used as arguments to user-defined primitives.
data PrimitiveExpression = PrimitiveChannel ChannelExpression
                         | PrimitiveInteger IntegerExpression
                         | PrimitiveType TypeExpression
                         | PrimitiveFunction FunctionExpression
                         | PrimitivePredicate PredicateExpression
                         | PrimitiveJoitch JoitchExpression
                         | PrimitiveSwitch SwitchExpression
                         -- | During parsing, strings will be mapped to PrimitiveUnknown.
                         -- During type checking, all PrimitiveUnknown instances will be converted to one of the the other options.
                         | PrimitiveUnknown Text
                         deriving (Show)

-- | Expressions that can be used as arguments to the Joitch primitive.
data JoitchExpression = JoitchPredicate PredicateExpression -- ^ A predicate taking two arguments
                      | JoitchOtherwise -- ^ The keyword @otherwise@
                      deriving (Show)

-- | Expressions that can be used as arguments to the Switch primitive.
-- Not to be confused with the switch statement in functions.
data SwitchExpression = SwitchTypeExpression TypeExpression -- ^ A type
                      | SwitchPredicate PredicateExpression -- ^ A predicate taking one argument
                      | SwitchBooleanExpression BooleanExpression -- ^ A boolean expression
                      | SwitchOtherwise -- ^ The keyword @otherwise@
                      | SwitchUnknown Text -- ^ During parsing, strings will be mapped to SwitchUnknown.
                      -- During type checking, all SwitchUnknown instances will be converted to SwitchTypeExpression or SwitchPredicate.
                      deriving (Show)

---------------------------------------------------------
-- ** Range Expression

-- | @RangeExpression n m@ represents @[n:m]@, which represents a bitvector of size @abs(n - m) + 1@
data RangeExpression = RangeExpression IntegerExpression IntegerExpression deriving (Show, Eq)

---------------------------------------------------------
-- ** Type Expression

-- | A type expression
data TypeExpression = TypeVariable Text -- ^ An identifier of a type
                    deriving (Show, Eq)

---------------------------------------------------------
-- * Other
---------------------------------------------------------

---------------------------------------------------------
-- ** Attribute

-- | An @Attribute [a, b, c]@ represents @a.b.c@
type Attribute = [Text]

---------------------------------------------------------
-- ** Channel Variable

-- | A channel variable
data ChannelVariable = ChannelVariable Text -- ^ The name of a channel
                     | BusVariable Text -- ^ The name of a bus
                     | BusIndex Text IntegerExpression -- ^ The name of a bus and an index of this bus
                     | UnknownVariable Text -- ^ During parsing, string will be mapped to UnknownVariable.
                     -- During type checking, all UnknownVariable instance will be converted to ChannelVariable or BusVariable.
                     deriving (Show)

---------------------------------------------------------
-- ** If-Then-Else Construction

-- | @IfThenElse bool thenval elseval@
-- This represents: @if(bool) thenval else elseval@
data IfThenElse a = IfThenElse BooleanExpression a a deriving (Show)

---------------------------------------------------------
-- ** Parameter

-- | Parameters that can be used in macro and process definitions
data Parameter = ChannelParameter Text -- ^ @ChannelParameter name@ represents @chan name@
               | BusParameter IntegerExpression Text -- ^ @BusParameter val name@ represents @bus<val> name@
               | IntParameter Text -- ^ @IntParameter name@ represents @int name@
               | FunctionParameter FunctionSignature -- ^ A function parameterf
               deriving (Show)

-- | @FunctionSignature returntype name inputtypes@
-- This represents: @returntype name (inputtypes)@
data FunctionSignature = FunctionSignature TypeExpression Text [TypeExpression] deriving (Show)

---------------------------------------------------------
-- ** Switch Statement

-- | A @SwitchStatement attribute cases@ represents: switch attribute { cases }
data SwitchStatement a = SwitchStatement Attribute [SwitchCase a] deriving (Show)
-- | A @SwitchCase name val@ represents: case name: val
data SwitchCase a = SwitchCase Text a deriving (Show)

---------------------------------------------------------
-- ** Variable Declaration

-- | A @VariableDeclaration name type@ represents @name : type@
data VariableDeclaration a = VariableDeclaration { variableName :: Text, variableObject :: a} deriving (Show, Eq)
