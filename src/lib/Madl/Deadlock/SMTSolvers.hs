{-|
Module      : Madl.Deadlock.SMTSolvers
Description : SMT solvers.
Copyright   : (c) Freek Verbeek, Tessa Belder 2016

This module contains supported SMT solvers.
-}
module Madl.Deadlock.SMTSolvers where

-- | Currently the solvers z3 and cvc4 are supported.
data SmtSolver = Z3 | CVC4

-- | A solver function takes a filename, and produces the name of an executable, and arguments for this executable.
type SolverFunction = String -> (String, [String])

-- | Returns the solver function of the given SMT solver.
solverFunction :: SmtSolver -> SolverFunction
solverFunction Z3 = (\file -> ("z3", [file])) -- /opt/local/bin
solverFunction CVC4 = (\file -> ("cvc4", ["-m",file]))
