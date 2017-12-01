// DParser grammar for xMAS
// Author: Wieger Wesselink 2015

// param int N = 2
ParameterDeclaration : 'param' 'int' ID '=' IntegerExpression ;

// Fork(Source(color in {b, r}))
NetworkPrimitive
  : 'ControlJoin' '(' ChannelExpression ',' ChannelExpression ')'
  | 'Fork' '(' ChannelExpression ')'
  | 'Function' '(' ID ',' ChannelExpression ')'
  | 'Join' '(' ID ',' ChannelExpression ',' ChannelExpression ')'
  | 'Merge' '(' ChannelExpression ',' ChannelExpression ')'
  | 'Queue' '(' IntegerExpression ',' ChannelExpression ')'
  | 'Sink' '(' ChannelExpression ')'
  | 'Source' '(' ID ')'
  | 'Switch' '(' ID ',' ChannelExpression ')'
  | 'LoadBalancer' '(' ChannelExpression ')'
  | UserDefinedPrimitive
  ;

IDList : ID (',' ID)* ;

//
UserDefinedPrimitive : ID '(' PrimitiveExpressionList ')' ;

IntegerExpression
  : NUMBER
  | ID
  | IntegerExpression '+' IntegerExpression
  ;

// Fork(buffer_req_out)
PrimitiveExpression
  : ChannelExpression
  | IntegerExpression
  | ID // refers to a type expression or a function expression
  ;

PrimitiveExpressionList : PrimitiveExpression (',' PrimitiveExpression)* ;

ChannelVariable : ID ('[' IntegerExpression ']')? ;

ChannelVariableList : ChannelVariable (',' ChannelVariable)* ;

//
ChannelExpression
  : NetworkPrimitive
  | ChannelVariable
  ;

// chan q0, q1 := Fork(Source(color in {b, r}))
// chan req_out, rsp_out
ChannelDeclaration : 'chan' IDList (':=' NetworkPrimitive)? ;

// bus<2> i
BusDeclaration
  : 'bus' '<' IntegerExpression '>' IDList
  | 'bus' '<' IntegerExpression '>' ID (':=' NetworkPrimitive)?
  ;

// color in {b, r}
// type := type with {_: rsp}
TypeExpression : 'type' ;

// let o[0], req_out := Fork(buffer_req_out)
LetStatement : 'let' ChannelVariableList ':=' ChannelExpression ;

Parameter
  : 'chan' ID
  | 'bus' '<' IntegerExpression '>' ID
  | 'int' ID
  | FunctionSignature
  ;

// chan i
ParameterList : Parameter (',' Parameter)* ;

CBParameter
  : 'chan' ID
  | 'bus' '<' IntegerExpression '>' ID
  ;

CBParameterList : CBParameter (',' CBParameter)* ;

ReturnType : 'bool' | 'msg' ;

FunctionSignature : ReturnType ID '(' IDList? ')' ;

//
MessageExpression
  : MessageFieldExpression
  | MessageSelectExpression
  | MessageValueExpression
  ;

MessageFieldExpression : ID ('(' FieldExpressionList ')')? ;

MessageSelectExpression : 'select' ID MessageCaseList ;

MessageValueExpression
  : ID '.' ID
  | NUMBER
  | MessageValueExpression '+' MessageValueExpression
  ;

ComparisonOperator
  : '=='
  | '<'
  | '>'
  ;

// a == Rsp()
// a == Rsp() || a == Req()
// a of type x
// bool f(a, b) = select a,b
//                  case Req, Req: a.data == b.data
//                  default: False
BooleanExpression : MessageExpression ComparisonOperator MessageExpression ;

MessageCase
  : 'case' ID ':' MessageExpression
  | 'default' ':' MessageExpression
  ;

MessageCaseList : MessageCase (',' MessageCase)* ;

FieldExpression : ID ':' MessageExpression ;

FieldExpressionList : FieldExpression (',' FieldExpression)* ;

// msg f(a) = a
// msg f(a) = Rsp()
// msg f(a) = select a
//              case Req: Rsp(data: a.data + 1)
//              case Rsp: a
// msg src() = Rsp(dest: 7, payload: A(data: B()))
// msg src0() = Req()
FunctionDeclaration : FunctionSignature '=' (BooleanExpression | MessageExpression) ;

NetworkStatement
  : try ChannelDeclaration
  | try BusDeclaration
  | try FunctionDeclaration
  | try LetStatement
  | try NetworkPrimitive
  | try ParameterDeclaration
  | try Component
  ;

NetworkStatementList : NetworkStatement (';' NetworkStatement)* ';'? ;

Network : NetworkStatementList ;

// component DualChannel(bus<2> i) => bus<2> o { }
Component : 'component' ID '(' ParameterList? ')' ('=>' CBParameterList)? '{' NetworkStatementList? '}' ;

NUMBER           : "0|([1-9][0-9]*)" $term -1 ;

ID               : "[a-zA-Z_][a-zA-Z0-9_]*" $term -1 ;

whitespace: ( "[ \t\r\n]+" | singleLineComment )* ;

singleLineComment: '//' "[^\n]*" '\n' ;
