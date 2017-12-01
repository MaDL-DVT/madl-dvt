{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Parser.MadlLexer
Description : Madl Language definition
Copyright   : (c) Tessa Belder 2016

This module contains the language definition of the Madl language.
-}
module Parser.MadlLexer(
      identifier
    , reserved, reservedOp
    , decimal
    , whiteSpace
    , parens, braces, angles, brackets
    , semi, comma, colon, dot
    , semiSep, semiSep1, commaSep, commaSep1
    , semiEnd, semiEnd1, commaEnd, commaEnd1
    , semiSepEnd, semiSepEnd1, commaSepEnd, commaSepEnd1
    ) where

import Data.Functor.Identity (Identity)

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Utils.Text

-- | MaDL language definition. Outcommented lines contain default values
madlDef :: GenLanguageDef String () Identity
madlDef = emptyDef {
      commentStart = "/*"
    , commentEnd = "*/"
    , commentLine = "//"
    -- , nestComments = True

    , identStart = letter <|> char '_'
    , identLetter = alphaNum <|> char '_'

    -- , opStart        = opLetter emptyDef
    -- , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"

    , reservedOpNames= [
          "+", "-", "*", "%" -- integer operators
        , "&&", "||", "!" -- boolean operators
        , "<", "<=", "=>", ">", "!=", "==" -- relational operators
        , ":=", "=", "++", ":" -- assignment operators
        , "<-", "->" -- read and write actions
        ]

    , reservedNames  = [
          "bus", "chan", "component", "function", "macro", "pred", "process" -- Madl object keywords
        , "guard", "next", "state", "trans" -- Madl process keywords
        , "const", "enum", "struct", "union", "otherwise" -- Madl data keywords
        , "CtrlJoin", "DeadSink", "FCtrlJoin", "Fork", "Function", "GuardQueue", "Joitch", "LoadBalancer", "Match" -- Madl primitives
        , "Merge", "MultiMatch", "PatientSource", "Queue", "Sink", "Source", "Switch", "Vars", "Cut" -- Madl primitives
        , "let" -- Madl assignment keyword

        , "for", "if", "else", "uses" -- control keywords
        , "param", "int" -- global variable keywords
        ]

    -- , caseSensitive  = True
    }

-- | Lexer for the madl language
madlLexer :: Token.GenTokenParser String () Identity
madlLexer = Token.makeTokenParser madlDef

-- | A madl identifier
identifier :: Parser Text
identifier = fmap txt $ Token.identifier madlLexer

-- | Reserved keywords and operators
reserved, reservedOp :: String -> Parser ()
reserved = Token.reserved madlLexer
reservedOp = Token.reservedOp madlLexer

-- | A decimal value
decimal :: Parser Integer
decimal = Token.decimal madlLexer <* whiteSpace

-- | Whitespace, including newlines and comments
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace madlLexer

-- | Different types of brackets
parens, braces, angles, brackets :: forall a. Parser a -> Parser a
parens = Token.parens madlLexer
braces = Token.braces madlLexer
angles = Token.angles madlLexer
brackets = Token.brackets madlLexer

-- | Different separators
semi, comma, colon, dot :: Parser ()
semi = do _ <- Token.semi madlLexer; return ()
comma = do _ <- Token.comma madlLexer; return ()
colon = do _ <- Token.colon madlLexer; return ()
dot = do _ <- Token.dot madlLexer; return ()

-- | Seperator-separated lists
semiSep, semiSep1, commaSep, commaSep1 :: forall a. Parser a -> Parser [a]
semiSep = Token.semiSep madlLexer
semiSep1 = Token.semiSep1 madlLexer
commaSep = Token.commaSep madlLexer
commaSep1 = Token.commaSep1 madlLexer

-- | Seperator-separated-and-ended lists
semiEnd, semiEnd1, commaEnd, commaEnd1 :: forall a. Parser a -> Parser [a]
semiEnd = flip endBy semi
semiEnd1 = flip endBy1 semi
commaEnd = flip endBy comma
commaEnd1 = flip endBy1 comma

-- | Seperator-separated-and-optionally-ended lists
semiSepEnd, semiSepEnd1, commaSepEnd, commaSepEnd1 :: forall a. Parser a -> Parser [a]
semiSepEnd = flip sepEndBy semi
semiSepEnd1 = flip sepEndBy1 semi
commaSepEnd = flip sepEndBy comma
commaSepEnd1 = flip sepEndBy1 comma