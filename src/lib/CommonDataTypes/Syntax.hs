{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -Wmissing-local-signatures #-}
{-# LANGUAGE Safe, DeriveFoldable,DeriveTraversable,DeriveFunctor,NoImplicitPrelude #-}

{-|
Module      : CommonDataTypes.Syntax
Copyright   : (c) Sebastiaan J C Joosten
-}
module CommonDataTypes.Syntax where
import Data.ByteString as B  (ByteString)
import qualified Data.Map as Map (Map)
import BaseLike.CustomPrelude

-- | TODO
data VerilogModule = VerilogModule VerilogIdentifier    -- name of the module
                                   [VerilogIdentifier]  -- list of parameters
                                   (Maybe B.ByteString) -- maybe a comment is added
                                   [VerilogModuleStatement]

-- | TODO
data VerilogModuleStatement
 = VerilogDeclare VerilogWireType VerilogWireSize VerilogIdentifier (Maybe B.ByteString) -- maybe a comment is added
 | VerilogInstantiate VerilogIdentifier (Maybe VerilogIdentifier) [VerilogModuleParameterInstantiation] (Maybe B.ByteString)
 | VerilogAssign VerilogIdentifier (Maybe Int) VerilogExpression (Maybe B.ByteString)
 | VerilogUnhandled B.ByteString (Maybe B.ByteString)

-- | TODO
data VerilogExpression
 = VerilogITE VerilogExpression VerilogExpression VerilogExpression -- ^ in Verilog: .. ? .. : ..
 | VerilogAND VerilogExpression VerilogExpression -- ^ in Verilog: .. && ..
 | VerilogOR  VerilogExpression VerilogExpression -- ^ in Verilog: .. || ..
 | VerilogNOT VerilogExpression -- ^ in Verilog: ! ..
 | VerilogBit (Bool,Bool) -- ^ any value of a certain bit-size; first Int is the bit-size (as in 1'b000 ). The two Integers are the same, but taking into account the x- and z-convention
 | VerilogVariableSelection Int Int VerilogIdentifier
 | VerilogVariable VerilogIdentifier
 | VerilogConcatenate [VerilogExpression]
  deriving Show

-- | TODO
data VerilogWireType = Input | Output | Wire | Register | InOut deriving (Eq,Show)

-- | TODO
data VerilogWireSize = SizeBit | SizeWord Int Int -- ^ as in [max:min] or [min:max}

-- | TODO
type VerilogIdentifier = ByteString -- ^ I think using the strict version instead might speed things up

-- | TODO
data VerilogModuleParameterInstantiation
 = VerilogModuleParameterInstantiation (Maybe VerilogIdentifier) VerilogExpression deriving Show

-- | TODO
data VerilogPort = VerilogPort PortDescription [PortStatement]

-- | TODO
newtype PortDescription = PD ByteString deriving Show

-- | TODO
data PortStatement
  = PortModuleReference (Map.Map ByteString Int) ByteString
  | PortExpression PortProperty [Either Int ByteString] VerilogExpression

-- | TODO
newtype PortProperty = PP ByteString deriving (Ord,Show,Eq)

-- | TODO
data Instantiation e = INST  ByteString -- module name
                             ByteString -- instance name
                             e -- assignment of parameters to values
