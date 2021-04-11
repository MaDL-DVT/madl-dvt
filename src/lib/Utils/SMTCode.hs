{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Utils.NuxmvCode
Description : Utilities for producing smt code
Copyright   : (c) Tessa Belder 2015-2016

This module contains useful functions for producing smt code.
-}
module Utils.SMTCode where

import Utils.Concatable as C

-- * Declarations
-- | SMT declaration
smt_fun :: (IsString a, Monoid a) => a -> a -> a
smt_fun t name = "(" <> C.unwords ["declare-fun", name, "()", t] <> ")"

-- * Unary operators
-- | Assert statement
smt_assert :: (IsString a, Monoid a) => a -> a
smt_assert = smt_un_operator "assert"

smt_assert' :: (IsString a, Monoid a) => a -> a
smt_assert' arg = smt_un_operator "assert" ("(! " <> arg <> " :interpolation-group ga)")

smt_assert'' :: (IsString a, Monoid a) => a -> a
smt_assert'' arg = smt_un_operator "assert" ("(! " <> arg <> " :interpolation-group gb)")

-- | Boolean to integer conversion
smt_bool_to_int :: (IsString a, Monoid a) => a -> a
smt_bool_to_int bool = smt_ite bool "1" "0"

-- | General unary operator
smt_un_operator :: (IsString a, Monoid a) => a -> a -> a
smt_un_operator op arg = "(" <> C.unwords [op, arg] <> ")"

-- * Binary operators
-- | Equality operator
smt_equals :: (IsString a, Monoid a) => a -> a -> a
smt_equals = smt_bin_operator "="
-- | At most operator
smt_atmost :: (IsString a, Monoid a) => a -> a -> a
smt_atmost = smt_bin_operator "<="
-- | At least operator
smt_atleast :: (IsString a, Monoid a) => a -> a -> a
smt_atleast = smt_bin_operator ">="
-- | Multiplication
smt_mult :: (IsString a, Monoid a) => a -> a -> a
smt_mult = smt_bin_operator "*"

-- | General binary operator
smt_bin_operator :: (IsString a, Monoid a) => a -> a -> a -> a
smt_bin_operator op arg1 arg2 = "(" <> C.unwords [op, arg1, arg2] <> ")"

-- * Tertiary operators
-- | In range operator (at least "low" and at most "high")
smt_assert_inrange :: (IsString a, Monoid a) => a -> (Int, Int) -> a
--smt_assert_inrange val (l, h) = C.unwords [smt_assert $ smt_atmost (C.show l) val, smt_assert $ smt_atmost val (C.show h)]
smt_assert_inrange val (l, h) = (smt_assert $ smt_atmost (C.show l) val) <> (smt_assert $ smt_atmost val (C.show h))

smt_assert_inrange' :: (IsString a, Monoid a) => a -> (Int, Int) -> a
smt_assert_inrange' val (l, h) = (smt_assert' $ smt_atmost (C.show l) val) <> (smt_assert' $ smt_atmost val (C.show h))

smt_assert_inrange'' :: (IsString a, Monoid a) => a -> (Int, Int) -> a
smt_assert_inrange'' val (l, h) = (smt_assert'' $ smt_atmost (C.show l) val) <> (smt_assert'' $ smt_atmost val (C.show h))

-- | If-then-else statement
smt_ite :: (IsString a, Monoid a) => a -> a -> a -> a
smt_ite i t e = "(" <> C.unwords ["ite", i, t, e] <> ")"

-- * N-ary operators:
-- | Addition
smt_add :: (IsString a, Monoid a) => [a] -> a
smt_add = smt_n_operator "+"
-- | Disjunction
smt_or :: (IsString a, Monoid a) => [a] -> a
smt_or = smt_n_operator "or"
-- | Conjunction
smt_and :: (IsString a, Monoid a) => [a] -> a
smt_and = smt_n_operator "and"

-- | General n-ary operator
smt_n_operator :: (IsString a, Monoid a) => a -> [a] -> a
smt_n_operator _ [] = ""
smt_n_operator _ [x] = x
smt_n_operator op xs = "(" <> C.unwords (op:xs) <> ")"
