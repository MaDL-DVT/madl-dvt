{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -fwarn-orphans #-} -- without  -fwarn-missing-local-sigs  since we don't have proper forall syntax
{-# LANGUAGE OverloadedStrings, NoImplicitPrelude #-}

{-|
Module      : Verilog.Parser
Copyright   : (c) Sebastiaan J C Joosten
-}
module Verilog.Parser
       ( parseInputAsVerilog ) where
-- I chose Attoparsec this time, have no idea on what the speed difference with Parsec is,
-- and the error messages do not contain the file position anymore.
-- We're mostly parsing Verific output, we should not encounter those parse errors often.
-- In addition, I should be able to go to (more) strict bytestrings and measure performance
-- If we'd go to Parsec, a try is needed around most strings, while this code is try-free
import           Control.Applicative ((<**>),optional,(<|>))
import           System.Exit (exitFailure)
import           Data.List (intercalate)
import qualified Data.Map                         as Map (fromList,empty)
import           Data.ByteString                  as B  (cons,append)
import qualified Data.ByteString                  as BL (hGetContents)
import qualified Data.Attoparsec.ByteString.Char8 as AC (endOfLine,decimal)
-- import Data.Attoparsec.Internal.Types          as T  (Input(..), Added(..), More, addS, Parser(..))
import           Data.Attoparsec.ByteString       as AL (string,takeWhile1,endOfInput,Parser,(<?>),option,takeTill,Result,satisfy,word8,skipWhile,parse,IResult(..),takeWhile,manyTill)
import           System.IO (Handle,hPutStrLn,stderr)
import           CommonDataTypes.Syntax -- data types
import           Data.Either
import BaseLike.CustomPrelude

-- | TODO
parseInputAsVerilog :: Handle -> IO ([VerilogModule],[VerilogPort])
parseInputAsVerilog h = do file <- BL.hGetContents h
                           partitionEithers <$> readerToIO (parse readVerilogList file)

readerToIO :: Result t -> IO t
readerToIO (Fail x b _c)
 = do hPutStrLn stderr ("Error while parsing "++(intercalate " inside " (reverse b))++" at:\n"++(take 200$ (read$show x)))
      exitFailure
readerToIO (Done _ x) = return x
readerToIO (Partial x) = readerToIO (x "")

readVerilogList :: AL.Parser [Either VerilogModule VerilogPort]
readVerilogList = readCommentsAndWhiteLines *> manyTill (((Left <$> readModule) <|> (Right <$> readVerilogPort)) <* readCommentsAndWhiteLines) endOfInput

readVerilogPort :: AL.Parser VerilogPort
readVerilogPort = VerilogPort <$> ((string "properties" <|> string "annotate") *> whitespace *> (PD <$> readIdentifier) <* string ";" <* whitespace)
                              <*> (manyTill (readPortStatement <* whitespace) (string "endport" <|> string "endannotate"))

intOrRefParser :: AL.Parser (Either Int ByteString)
intOrRefParser
 = whitespace *> ((Left <$> readInt) <|> (Right <$> readIdentifier)) <* whitespace
intMapParser :: AL.Parser (ByteString, Int)
intMapParser
 = whitespace *> ((,) <$> (string "." *> readIdentifier <* whitespace)
                      <*> (string "(" *> whitespace *> readInt <* whitespace <* string ")" <* whitespace))
{-
data PortStatement
  = PortModuleReference [(ByteString,Int)] ByteString
  | PortExpression PortProperty [Either Int ByteString] VerilogExpression
-}
readPortStatement :: AL.Parser PortStatement
readPortStatement
 = ((   (PortModuleReference <$> (string "module" *> whitespace *> option Map.empty (Map.fromList <$> argumentList intMapParser))) <*> (whitespace *> readIdentifier)
    <|> (PortExpression <$> (PP <$> (readIdentifier <* whitespace)) <*> option [] (argumentList intOrRefParser) <*> readExpression)
   ) <?> "Port statement")
   <* stmtEnd

readModule :: AL.Parser VerilogModule
readModule
 = VerilogModule <$> (string "module" *> whitespace *> readIdentifier <?> "Module name")
                 <*> (whitespace *> argumentList (readSpacedIdentifier <?> "Spaced identifier"))
                 <*> (whitespace *> string ";" *> whitespace *> optional readComment <* whitespace <?> "End of argument list")
                 <*> (concat <$> manyTill (readStatement <* whitespace) (string "endmodule"))
 where readSpacedIdentifier :: AL.Parser ByteString
       readSpacedIdentifier = whitespace *> readIdentifier <* whitespace
commaSeparated :: AL.Parser a -> AL.Parser [a]
commaSeparated f = option [] cs
 where cs = (:) <$> f <*> ((string "," *> cs) <|> pure []) <?> "Comma separated list"

argumentList :: AL.Parser x -> AL.Parser [x]
argumentList listOf
 = optional "#" *> string "(" *> commaSeparated listOf <* string ")"

-- careful for loops: these cannot fail!
whitespace, readCommentsAndWhiteLines :: AL.Parser ()
whitespace = readCommentsAndWhiteLines
readCommentsAndWhiteLines = purewhitespace <* optional (readComment *> readCommentsAndWhiteLines)
                          where purewhitespace = skipWhile whitespaceChar <?> "Pure whitespace"


readIdentifier, readComment :: AL.Parser ByteString
readIdentifier
 =     (cons <$> word8 92 <*> takeTill whitespaceChar <?> "Escaped identifier character") -- escaped identifier
   <|> (cons <$> satisfy letterOrUnderscore <*> AL.takeWhile identifierChar <?> "Identifier character") -- regular identifier
   <?> "Identifier"
readComment = string "//" *> takeTill endOfLineChar <* optional AC.endOfLine <?> "Comment"

readStatement :: AL.Parser [VerilogModuleStatement]
readStatement
 =(((\x y z -> map (\(y1,y2) -> VerilogDeclare x y1 y2 z) y)
      <$> (readDeclareType <* whitespace)
      <*> commaSeparated
            ((,)<$> option SizeBit (SizeWord <$> (string "[" *> readInt) <*> (string ":" *> readInt <* string "]"))
                <*> (whitespace *> readIdentifier))
      <?> "a declaration") <|>
   ((\x x2 y z -> [VerilogAssign x x2 y z])
      <$> (string "assign" *> whitespace *> readIdentifier <* whitespace)
      <*> (optional (string "[" *> readInt <* string "]") <* whitespace <* string "=")
      <*> (whitespace *> readExpression)
      <?> "assignment") <|>
   ((\x y z -> [VerilogUnhandled (B.append x y) z])
      <$> string "defparam" <*> AL.takeWhile (/= 59)
      <?> "defparam"
      ) <|>
   ((\x y y2 z -> [VerilogInstantiate x y y2 z])
      <$> (readIdentifier <* whitespace <?> "module instantiation module name")
      <*> optional (readIdentifier <* whitespace <?> "module instantiation instance name")
      <*> argumentList (param <?> "Module parameter")
      <?> "module instantiation") )
      <*> (stmtEnd <?> "statement")
  where
   param = whitespace *> (
           (VerilogModuleParameterInstantiation
             <$> (string "." *> (Just <$> readIdentifier) <* whitespace)
             <*> (string "(" *> readExpression <* string ")" <* whitespace))
           <|>
           (VerilogModuleParameterInstantiation Nothing
             <$> (readExpression <* whitespace)))

stmtEnd :: AL.Parser (Maybe ByteString)
stmtEnd = (whitespace *> optional inlineComment *> string ";" <?> ";-character") *> whitespace *> optional readComment
inlineComment :: AL.Parser ByteString
inlineComment
  = string "/*" *> restComment <* whitespace
  where restComment = append <$> takeTill starChar <*> ( string "*/" <|> restComment )
readInt :: AL.Parser Int
readInt = AC.decimal


readExpression :: AL.Parser VerilogExpression
readExpression
 = whitespace *> (
     concatenation <|>
     -- pre <|>
     negation <|> brac <|>
     verilogRangedVariable <|>
     constant
     ) <**>
   (whitespace *> option id andVerilog <* whitespace) <**>
   (whitespace *> option id  orVerilog <* whitespace) <**>
   (whitespace *> option id ifThenElse <* whitespace) <?> "Expression"
  where preselection x (Just y) z = VerilogVariableSelection x y z
        preselection x Nothing  z = VerilogVariableSelection x x z
        verilogRangedVariable
          = (readIdentifier <* whitespace) <**> (range <|> pure VerilogVariable)
        range = preselection <$> (string "[" *> readInt) <*> optional (string ":" *> readInt) <* string "]"
        concatenation = string "{" *> (VerilogConcatenate <$> commaSeparated readExpression) <* string "}"
        negation = string "!" *> (VerilogNOT <$> readExpression)
        -- pre = string "pre(" *> (VerilogPRE <$> readExpression) <* string ")"
        brac = string "(" *> readExpression <* string ")"
        constant = VerilogConcatenate <$> (readInt *> string "'b" *> readBinary)
        ifThenElse = (\x y z -> VerilogITE z x y) <$> (string "?" *> readExpression)
                                                  <*> (string ":" *> readExpression)
        andVerilog = VerilogAND <$> ((string "&&" <|> string "&") *> readExpression)
        orVerilog  = VerilogOR  <$> ((string "||" <|> string "|") *> readExpression)

readDeclareType :: AL.Parser VerilogWireType
readDeclareType = (string "output" *> pure Output) <|>
                  (string "input"  *> pure Input )<|>
                  (string "inout"  *> pure InOut )<|>
                  (string "wire"   *> pure Wire  )
readBinary :: AL.Parser [VerilogExpression]
readBinary = (map step . unpack) `fmap` takeWhile1 isBinDigit
  where
    -- isBinDigit :: Word8 -> Bool
    isBinDigit w = (w == 48 || w == 49 || w == 120 || w == 122)
    -- step :: Word8 -> VerilogExpression
    step 'x' = VerilogBit ( True, False ) -- x: 120
    step 'z' = VerilogBit ( False, True ) -- z: 122
    step w   = VerilogBit ( w=='1', w=='1' ) -- 1: 49

-- character recognisers for Verilog:
whitespaceChar,endOfLineChar,letterOrUnderscore,identifierChar,starChar :: (Num a, Eq a, Ord a) => a -> Bool
starChar w = w == 42
whitespaceChar w = w <= 32 && w>=1 -- should be usable for escaped identifier terminator
endOfLineChar w = w == 13 || w == 10 -- not tested, but seems reasonable
letterOrUnderscore w = w >= 65 && w <= 122 && (w<91 || w>96 || w==95) -- according to standard
identifierChar w = letterOrUnderscore w || (w>= 48 && w <= 57) || w == 36 -- according to standard