{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Utils.NuxmvCode
Description : Utilities for producing nuXmv code
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for producing nuXmv code.
-}
module Utils.NuxmvCode where

import Data.List (intersperse)

import Utils.Concatable as C

-- * Declarations
-- | INVAR declaration
nuxmv_invar :: (IsString a, Monoid a) => a -> a
nuxmv_invar = nuxmv_keyword "INVAR"
-- | INVARSPEC declaration
nuxmv_invarspec :: (IsString a, Monoid a) => a -> a
nuxmv_invarspec = nuxmv_keyword "INVARSPEC"

-- | NuXmv keyword declarations
nuxmv_keyword :: (IsString a, Monoid a) => a -> a -> a
nuxmv_keyword keyword assignment = C.unwords[keyword,assignment]

-- | CONSTANTS declaration
nuxmv_constants :: (IsString a, Monoid a) => [a] -> a
nuxmv_constants consts = "CONSTANTS " <> C.intercalate ", " consts <> ";"

-- | NuXmv variable types
data NuxmvVariableType =
      Input -- ^ Input variable (IVAR)
    | State -- ^ State variable (VAR)
    | Frozen -- ^ Frozen variable (FROZENVAR)

-- | Boolean variable declaration
nuxmv_bool :: (IsString a, Monoid a) => NuxmvVariableType -> a -> a
nuxmv_bool varType = nuxmv_var varType bool_type
-- | Integer variable declaration
nuxmv_int :: (IsString a, Monoid a) => NuxmvVariableType -> Int -> a -> a
nuxmv_int varType n = nuxmv_var varType (int_type n)
-- | Enumeration declaration
nuxmv_enum :: (IsString a, Monoid a) => NuxmvVariableType -> [a] -> a -> a
nuxmv_enum varType vals = nuxmv_var varType (enum_type vals)
-- | Array declaration
nuxmv_array :: (IsString a, Monoid a) => NuxmvVariableType -> a -> a -> a -> a
nuxmv_array varType t t' name = nuxmv_var varType (array_type t t') name

-- | NuXmv keyword for nuXmv variable types
nuxmv_var :: (IsString a, Monoid a) => NuxmvVariableType -> a -> a -> a
nuxmv_var State = nuxmv_declaration "VAR"
nuxmv_var Input = nuxmv_declaration "IVAR"
nuxmv_var Frozen = nuxmv_declaration "FROZENVAR"

-- | General nuXmv declaration
nuxmv_declaration :: (IsString a, Monoid a) => a -> a -> a -> a
nuxmv_declaration keyword t name = nuxmv_keyword keyword $ name <> ": " <> t <> ";"

-- * Types
-- | NuXmv boolean type
bool_type :: IsString a => a
bool_type = "boolean"
-- | nuXmv integer type
int_type :: (IsString a, Monoid a) => Int -> a
int_type n = range_type 0 (n-1)
-- | nuXmv range type
range_type :: (IsString a, Monoid a) => Int -> Int -> a
range_type n m = C.show n <> ".." <> C.show m
-- | nuXmv enumeration type
enum_type :: (IsString a, Monoid a) => [a] -> a
enum_type [] = "{no_values}" -- empty enumerations are not allowed
enum_type vals = "{" <> C.intercalate ", " vals <> "}"
-- | nuXmv array type
array_type :: (IsString a, Monoid a) => a -> a -> a
array_type t t' = "array " <> t <> " of " <> t'

-- | Position in an array
nuxmv_array_pos :: (IsString a, Monoid a) => a -> Int -> a
nuxmv_array_pos arr pos = arr <> "[" <> (C.show pos) <> "]"

-- * Constants
-- | True
nuxmv_true :: IsString a => a
nuxmv_true = "TRUE"
-- | False
nuxmv_false :: IsString a => a
nuxmv_false = "FALSE"

-- * Operators
-- ** Unary operators
-- | Boolean negation
nuxmv_negate :: (IsString a, Monoid a) => a -> a
nuxmv_negate = nuxmv_un_operator "!"

-- | General unary operator
nuxmv_un_operator :: (IsString a, Monoid a) => a -> a -> a
nuxmv_un_operator op arg = "(" <> op <> arg <> ")"

-- ** Binary operators
-- | Equality operator
nuxmv_equals :: (IsString a, Monoid a) => a -> a -> a
nuxmv_equals = nuxmv_bin_operator "="
-- | Inequality operator
nuxmv_unequal :: (IsString a, Monoid a) => a -> a -> a
nuxmv_unequal = nuxmv_bin_operator "!="
-- | At most operator
nuxmv_atmost :: (IsString a, Monoid a) => a -> a -> a
nuxmv_atmost = nuxmv_bin_operator "<="
-- | Greater than operator
nuxmv_gt :: (IsString a, Monoid a) => a -> a -> a
nuxmv_gt = nuxmv_bin_operator ">"
-- | Set inclusion ("in") operator
nuxmv_in :: (IsString a, Monoid a) => a -> a -> a
nuxmv_in = nuxmv_bin_operator "in"

-- | Addition
nuxmv_add_bin :: (IsString a, Monoid a) => a -> a -> a
nuxmv_add_bin x y = nuxmv_add [x, y]
-- | Multiplication
nuxmv_mult_bin :: (IsString a, Monoid a) => a -> a -> a
nuxmv_mult_bin x y = nuxmv_mult [x, y]
-- | Subtraction
nuxmv_minus :: (IsString a, Monoid a) => a -> a -> a
nuxmv_minus = nuxmv_bin_operator "-"
-- | Modulo
nuxmv_mod :: (IsString a, Monoid a) => a -> a -> a
nuxmv_mod = nuxmv_bin_operator "mod"
-- | Disjunction
nuxmv_or_bin :: (IsString a, Monoid a) => a -> a -> a
nuxmv_or_bin x y = nuxmv_or [x, y]
-- | Conjunction
nuxmv_and_bin :: (IsString a, Monoid a) => a -> a -> a
nuxmv_and_bin x y = nuxmv_and [x, y]

-- | General binary operator
nuxmv_bin_operator :: (IsString a, Monoid a) => a -> a -> a -> a
nuxmv_bin_operator op arg1 arg2 = "(" <> C.unwords [arg1, op, arg2] <> ")"

-- ** Tertiary operators
-- | In range operator (at least "low" and at most "high")
nuxmv_inrange :: (IsString a, Monoid a) => a -> (Int, Int) -> a
nuxmv_inrange val (l, h) = nuxmv_and[nuxmv_atmost (C.show l) val, nuxmv_atmost val (C.show h)]

-- ** N-ary operators
-- | Addition
nuxmv_add :: (IsString a, Monoid a) => [a] -> a
nuxmv_add = nuxmv_n_operator "+"
-- | Multiplication
nuxmv_mult :: (IsString a, Monoid a) => [a] -> a
nuxmv_mult = nuxmv_n_operator "*"
-- | Disjunction
nuxmv_or :: (IsString a, Monoid a) => [a] -> a
nuxmv_or = nuxmv_n_operator "|"
-- | Conjunction
nuxmv_and :: (IsString a, Monoid a) => [a] -> a
nuxmv_and = nuxmv_n_operator "&"

-- | General n-ary operator
nuxmv_n_operator :: (IsString a, Monoid a) => a -> [a] -> a
nuxmv_n_operator _ [] = ""
nuxmv_n_operator _ [x] = x
nuxmv_n_operator op xs = "(" <> C.unwords (intersperse op xs) <> ")"

-- * Functions
-- | Cast to integer
nuxmv_toint :: (IsString a, Monoid a) => a -> a
nuxmv_toint = nuxmv_function "toint" . (:[])
-- | Count function
nuxmv_count :: (IsString a, Monoid a) => [a] -> a
nuxmv_count = nuxmv_function "count"

-- | General function application
nuxmv_function :: (IsString a, Monoid a) => a -> [a] -> a
nuxmv_function fun args = fun <> "(" <> C.intercalate ", " args <> ")"

-- * Assignments
-- | Init assignment
nuxmv_init :: (IsString a, Monoid a) => a -> a -> a
nuxmv_init var = head . nuxmv_assignment (nuxmv_function "init" [var]) . (:[])
-- | Next assignment
nuxmv_next :: (IsString a, Monoid a) => a -> [a] -> [a]
nuxmv_next var = nuxmv_assignment $ nuxmv_function "next" [var]

-- | General assignment
nuxmv_assignment :: (IsString a, Monoid a) => a -> [a] -> [a]
nuxmv_assignment _ [] = fatal (513::Int) "Empty assignment not allowed" where
    fatal i s = error ("Fatal " ++ Prelude.show i ++ " in " ++ fileName ++ ":\n  " ++ s)
    fileName = "Utils.NuxmvCode"
nuxmv_assignment name [assignment] = [name <> " := " <> assignment <> ";"]
nuxmv_assignment name (asg:asgs) = [name <> " := " <> asg] ++ init asgs ++ [last asgs <> ";"]

-- * Case distinction
-- | Switch statement
nuxmv_switch :: (IsString a, Monoid a) => [(a, a)] -> [a]
nuxmv_switch cases = ["case"] ++ nuxmv_indent (map (uncurry nuxmv_case) cases) ++ ["esac"] where
-- | A single switch case
nuxmv_case :: (IsString a, Monoid a) => a -> a -> a
nuxmv_case ifval thenval = ifval <> ": " <> thenval <> ";"

-- | If-then-else statement
nuxmv_ite :: (IsString a, Monoid a) => a -> a -> a -> a
nuxmv_ite ifval thenval elseval = "(" <> C.unwords[ifval, "?", thenval, ":", elseval] <> ")"

-- * File generation
-- | "MODULE" block
nuxmv_module :: (IsString a, Monoid a) => a -> [a] -> [a]
nuxmv_module name = nuxmv_file_block (C.unwords["MODULE",name])
-- | "ASSIGN" block
nuxmv_assign :: (IsString a, Monoid a) => [a] -> [a]
nuxmv_assign = nuxmv_file_block "ASSIGN"

-- | General block
nuxmv_file_block :: (IsString a, Monoid a) => a -> [a] -> [a]
nuxmv_file_block header contents = if null contents then [] else header:(nuxmv_indent contents)

-- | Indent 2 spaces
nuxmv_indent :: (IsString a, Monoid a) => [a] -> [a]
nuxmv_indent = map ("  " <>)