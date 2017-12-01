{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Madl.Deadlock.Runner
Description : Main module for deadlock and reachability analysis.
Copyright   : (c) Freek Verbeek, Sanne Wouda 2015-2016, Tessa Belder 2016

This module uses command line input to execute the smt and nuxmv deadlock algorithms.
-}
module Madl.Deadlock.Runner(
    runDeadlockDetection,
    RunMode(..), SmtSolver(..), Sources(..), Verbose(..),
    ReachabilityEngine(..), NuxmvEngine(..), AbcEngine(..),
    ReachabilityOptions(..),
    CommandLineOptions(..), defaultOptions,
    notFullQueues
    ) where

-- import              Debug.Trace

import              Control.Monad (foldM_,filterM,when)
import qualified    Control.Monad.Parallel as Par (MonadParallel,mapM)

import              Data.List.Split (chunksOf)
import qualified    Data.Map            as Map
import qualified    Data.Sequence       as Seq

import              System.Directory (removeFile)
import              System.Exit (exitFailure)
import              System.IO (hPutStrLn,hClose,openFile,IOMode(..))
import              System.IO.Temp (withTempFile)
import              System.Process (readProcessWithExitCode)

import GHC.Conc (numCapabilities)
import Text.Parsec.Error(errorMessages, messageString)

import              Utils.Map
import              Utils.Text

import              Madl.Network
import              Madl.MsgTypes
import              Madl.Invariants

import              Madl.Deadlock.Formulas
import              Madl.Deadlock.DeadlockDetection
import              Madl.Deadlock.Nuxmv
import              Madl.Deadlock.SMT
import              Madl.Deadlock.SMTSolvers

-- | Determines which algorithms are executed.
data RunMode = NuxmvModelOnly | ReachabilityOnly | SmtOnly | ReachabilityAfterSmt 
-- | InPar
-- | Determines whether all sources are checked for deadlocks, or if the algorithm is stopped after finding the first deadlock.
data Sources = ALL | ONE
-- | Verbosity level.
data Verbose = ON | OFF deriving (Eq)

-- | Contains user input from command line
data CommandLineOptions = CommandLineOptions {
    argNetwork :: Either Text FilePath, -- ^ The network to be checked. Either predefined (Left), or input from madl file.
    argTypeCheck :: Bool, -- ^ States whether the provided madl input file should be typechecked. (Deprecated: non-typechecking is no longer supported)
    argCycleCheck :: Bool, -- ^ States whether the provided mald input file should be searched for combinatorial cycles. 
    argRunMode :: RunMode, -- ^ The algorithms to execute.
    argKeepSMTModel :: Bool, -- ^ Determines whether the produced SMT files are removed after usage.
    argSMTSolver :: SmtSolver, -- ^ Determines which SMT solver is used.
    argSources :: Sources, -- ^ Determines when to stop checking for deadlocks.
    argVerbose :: Verbose, -- ^ Determines which information is provided to the user.
    argNuxmvOptions :: ReachabilityOptions, -- ^ The options to use for reachability analysis.
    argUseInvariants :: Bool, -- ^ Determines whether invariants are calculated.
    showChannelTypes  :: Bool, -- ^ Determines whether channel types are displayed
    showChannelSource :: Bool, -- ^ Determines whether channel source info is displayed
    showChannelConnections :: Bool, -- ^ Determines whether channel connections are displayed
    showRings :: Bool -- ^ Determines whether ring information is displayed
}

-- | Default commandline options.
defaultOptions :: CommandLineOptions
defaultOptions = CommandLineOptions {
    argNetwork = Left "twoagents10",
    argTypeCheck = True,
    argCycleCheck = True,
    argRunMode = ReachabilityAfterSmt,
    argKeepSMTModel = False,
    argSMTSolver = Z3,
    argSources = ONE,
    argVerbose = OFF,
    argNuxmvOptions = ReachabilityOptions {
        keepAigerModel = False,
        keepNuxmvModel = False,
        reachabilityEngine = NUXMV IC3M
    },
    argUseInvariants = True,
    showChannelTypes = False,
    showChannelSource = False,
    showChannelConnections = False,
    showRings = False
}

-- | Function to convert a color to a string.
show_p :: Color -> String
show_p = showColorNoSpaces

-- | Check whether the given formula is satisfiable for the given network, using the provided SMT solver
check_feasibility :: (Show a') => a' -> ColoredNetwork -> Set ComponentID -> (Map ComponentID [Color], Set ComponentID) -> (Color -> String) -> [Char] -> SmtSolver -> Formula -> IO Bool
check_feasibility i x' qs vars show_p_t invs solver f =
    case f of
        T -> return True
        F -> return False
        _ -> withTempFile "." ("t"++show i++".smt2") $ \file h ->
                do
                    -- let ret  = simplify_subsumptions $ simplify_remove_selects $ f
                    hPutStrLn h $ "(set-logic QF_LIA)\n" ++ invs
                    let (smt',_qs',_vars') = export_formula_to_SMT x' qs vars show_p_t Nothing f
                    hPutStrLn h $ smt'
                    hPutStrLn h $ "(check-sat)\n(get-model)"
                    () <- hClose h
                    (_exit,solver_output,_err) <- (uncurry readProcessWithExitCode) (solverFunction solver file) []
                    -- putStrLn solver_output
                    case parseSMTOutput solver_output of
                        Left err -> do
                                        print err
                                        h' <- openFile "temp.smt2" WriteMode
                                        -- hPutStrLn h' $ "(set-logic QF_LIA)\n" ++ invs
                                        hPutStrLn h' $ "(set-logic QF_LIA)\n" ++ invs ++ smt' ++ "(check-sat)\n(get-model)\n"
                                        hPutStrLn h' $ "Solver Output:\n" ++ solver_output
                                        hClose h'
                                        exitFailure
                        Right Nothing -> return False
                        Right (Just _model) -> return True

-- | Given a network, find all queues in this network that can never be full (using an SMT solver)
notFullQueues :: ColoredNetwork -> SmtSolver -> [Invariant Int] -> IO [ComponentID]
notFullQueues net solver invs = fmap (map fst) $ par_filterM isInfeasible (getComponentsWithID net) where
    (smtinvs, qs, vars) = export_invariants_to_smt net show_p invs
    -- TODO(snnw) better: IO [(ComponentID, Component)]
    isInfeasible :: (ComponentID, Component) -> IO Bool
    isInfeasible (i,c) = case c of
        Queue _ _ -> do
            feasible <- check_feasibility i net qs vars show_p smtinvs solver (Lit $ Is_Full i)
            return $ not feasible
        _ -> return False where

-- | Main function to perform deadlock and reachability analysis.
runDeadlockDetection :: ColoredNetwork -> CommandLineOptions -> [Invariant Int] -> [ComponentID] -> IO (Either String (Bool, Maybe SMTModel))
runDeadlockDetection net options invs nfqs =
    -- Calculate network properties
    let (smtinvs, qs, vars) = export_invariants_to_smt net show_p invs    
        --when (argVerbose options == ON) $ putStrLn ("Computing never full queues ... ")
        --nfqs :: IO [ComponentID]
        --nfqs = {-# SCC "NeverFullQueues" #-} notFullQueues net (argSMTSolver options) invs
        -- when (argVerbose options == ON) $ putStrLn ("Never full queues: " ++ show nfqs')

        -- nuxmv model
        nuxmv_model = writeModel (ReachabilityInput net Map.empty Nothing invs)

        -- reachability analysis
        nuxmv :: IO (Either String (Bool, Maybe SMTModel))
        nuxmv = do
--            nfqs' <- nfqs
            let allFormulas = unfold_formula net (BlockVars Seq.empty nfqs) spec
                mkLiteral :: ComponentID -> Component -> Formula
                mkLiteral i Source{} = Lit (BlockSource i)
                mkLiteral _ _ = F
                spec :: Formula
                spec = disjunctive literals
                literals :: Seq Formula
                literals = Seq.fromList $ map (uncurry mkLiteral) (getComponentsWithID net)
            ret <- hasDeadlock (argNuxmvOptions options) (ReachabilityInput net allFormulas (Just spec) invs)
            case ret of
                Left err -> return $ Left err
                Right b -> return $ Right (b,Nothing)

        smt :: IO (Either String (Bool, Maybe SMTModel))
        smt = case (argSources options) of
                    ALL -> smtPar
                    _   -> smtSeq

        -- deadlock analysis in parallel
        smtPar :: IO (Either String (Bool, Maybe SMTModel))
        smtPar = do 
                eq_lst' <- eq_lst
                foldr f (return $ Right (False,Nothing)) eq_lst' where
                eq_lst :: IO [Either String (Bool, Maybe SMTModel)]
                eq_lst = Par.mapM detectDeadlock (map fst src_lst)
                f :: (Either String (Bool, Maybe SMTModel)) -> IO (Either String (Bool, Maybe SMTModel)) -> IO (Either String (Bool, Maybe SMTModel))
                f res b' = do
                    res2 <- b'
                    case (res, res2) of
                        (Left err, Left err2) -> return $ Left (err ++ "\n" ++ err2)
                        (Left err, _) -> return $ Left err
                        (_, Left err) -> return $ Left err
                        (Right (False,Nothing), Right (False,Nothing)) -> return $ Right (False,Nothing)
                        (Right (False,Nothing), Right (True,Just model)) -> return $ Right (True,Just model)
                        (Right (True,Just model), Right (_,_)) -> return $ Right (True,Just model)
                        (_,_) -> return $ Left "Unexpected error"


                src_lst :: [(ComponentID, XComponent Text)]
                src_lst = filter (filter_out_dead_source . snd) (getComponentsWithID net)
                filter_out_dead_source i = case i of 
                                            (Source _ t) | not (emptyColorSet t) -> True
                                            _ -> False

        -- deadlock analysis
        smtSeq :: IO (Either String (Bool, Maybe SMTModel))
        smtSeq = foldr (uncurry doDeadlock) s (getComponentsWithID net) where
                doDeadlock :: ComponentID -> Component -> IO (Either String (Bool, Maybe SMTModel)) -> IO (Either String (Bool, Maybe SMTModel))
                doDeadlock i e dl' = do
                    dl <- dl'
                    case (dl, e) of
                        (Right (False,Nothing), Source _ t ) | not (emptyColorSet t) -> detectDeadlock i
                        _ -> return dl
                s = return $ Right (False,Nothing)

        -- components that are never blocked (currently not used)
        live = Seq.empty

        -- Determine the block formula of the source. Export it to an SMT solver.
        -- Based on the result, update the set of live components or not.
        detectDeadlock :: ComponentID -> IO (Either String (Bool, Maybe SMTModel))
        detectDeadlock i = let
            name = utxt . getName . getComponent net
            blockLit = BlockSource i in
                do
                    when (argVerbose options == ON) $ putStrLn ("Starting deadlock detection for source " ++ name i)                    
--                    nfqs' <- nfqs -- (js) this takes quite a lot of time ! I would turn in off for now.                     
                    when (argVerbose options == ON) $ putStrLn ("Unfolding formulas and writing SMT model ... ")
                    let ret  = {-# SCC "UnfoldFormula" #-} unfold_formula net (BlockVars live nfqs) (Lit blockLit) -- nfqs') (Lit blockLit)
                    let file = "deadlock_" ++ name i ++ ".smt2"
                    h <- openFile file WriteMode
                    hPutStrLn h $ "(set-logic QF_LIA)\n" ++ smtinvs
                    hPutStrLn h $ export_bi_var_to_smt net show_p (Map.keys ret)
                    foldM_ (\(qs',vars') (bi, f) -> do
                                                        let (smt',qs2,vars2) = export_formula_to_SMT net qs' vars' show_p (Just bi) f
                                                        hPutStrLn h $ smt'
                                                        return (qs2, vars2))
                           (qs, vars) (Map.toList ret)         
                    hPutStrLn h $ "(assert " ++ export_literal_to_SMT net show_p blockLit ++ ")"
                    hPutStrLn h $ "(check-sat)\n(get-model)"
                    when (argVerbose options == ON) $ putStrLn ("Unfolding formulas and writing SMT model completed. ")
                    when (argVerbose options == ON) $ putStrLn ("Calling SMT solver ... ")
                    hClose h
                    (_exit,solver_output,_err) <- (uncurry readProcessWithExitCode) (solverFunction (argSMTSolver options) file) []
                    when (not $ argKeepSMTModel options) $ removeFile file
                    -- putStrLn solver_output
                    case parseSMTOutput solver_output of
                        Left err -> do return $ Left (unlines $ map messageString $ errorMessages err)
                        Right Nothing -> do when (argVerbose options == ON) $ putStrLn $ "== Source " ++ name i ++ " is live."
                                            return $ Right (False,Nothing)
                        Right (Just model) -> do
                                            when (argVerbose options == ON) $ putStrLn $ "Source " ++ name i ++ " has a possible deadlock:\n" ++ showModel model
                                            return $ Right (True, Just model)
    in
        case argRunMode options of
            NuxmvModelOnly -> do
                _ <- nuxmv_model
                return (Left "Model only.")
            ReachabilityOnly -> nuxmv
            SmtOnly -> smt
            --InPar -> smt_par
            ReachabilityAfterSmt -> do
                result <- smt
                case result of
                    Left err -> return $ Left err
                    Right (False, Nothing) -> return $ Right (False, Nothing)
                    Right (True, _) -> nuxmv
                    Right (_,_) -> return $ Left "Unexpected error"

-- | Like 'Control.Monad.filterM', but applying the function to the individual list items in parallel (in chunks).
par_filterM :: (Functor m, Par.MonadParallel m) => (a -> m Bool) -> [a] -> m [a]
par_filterM f list = concat <$> Par.mapM (filterM f) (chunksOf (length list `quot` numCapabilities) list)


