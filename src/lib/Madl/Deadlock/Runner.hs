{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Madl.Deadlock.Runner
Description : Main module for deadlock and reachability analysis.
Copyright   : (c) Freek Verbeek, Sanne Wouda 2015-2016, Tessa Belder 2016, Alexander Fedotov 2016-2020

This module uses command line input to execute the smt and nuxmv deadlock algorithms.
-}
module Madl.Deadlock.Runner(
    runDeadlockDetection,
    RunMode(..), SmtSolver(..), Sources(..), Verbose(..),
    ReachabilityEngine(..), NuxmvEngine(..), AbcEngine(..),
    ReachabilityOptions(..),
    CommandLineOptions(..), defaultOptions,
    notFullQueues,
    ChannelsToCheck(..)
    ) where

-- import              Debug.Trace

import              Control.Monad (foldM_,filterM,when)
import qualified    Control.Monad.Parallel as Par (MonadParallel,mapM)

import              Data.List.Split (chunksOf)
import qualified    Data.Map            as Map
import qualified    Data.Sequence       as Seq
import qualified    Data.Set            as Set

import              System.Directory (removeFile)
import              System.Exit (exitFailure)
import              System.IO (hPutStrLn,hClose,openFile,IOMode(..))
import              System.IO.Temp (withTempFile)
import              System.Process (readProcessWithExitCode)

import GHC.Conc (numCapabilities)
import Text.Parsec.Error(errorMessages, messageString)

import              Madl.Base.Identifiers
import              Utils.Map
import              Utils.Text

import              Madl.Network
import              Madl.MsgTypes
import              Madl.Invariants
import              Madl.ReachInvariants

import              Madl.Deadlock.Formulas
import              Madl.Deadlock.DeadlockDetection
import              Madl.Deadlock.Nuxmv
import              Madl.Deadlock.SMT
import              Madl.Deadlock.SMTSolvers

-- Error function
fileName :: Text
fileName = "Madl.Deadlock.Runner"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> Source
src i = (fileName, i)

-- | Determines which algorithms are executed.
data RunMode = NuxmvModelOnly | ReachabilityOnly | SmtOnly | ReachabilityAfterSmt
-- | InPar
-- | Determines whether all sources are checked for deadlocks, or if the algorithm is stopped after finding the first deadlock.
data Sources = ALL | ONE
-- | Verbosity level.
data Verbose = ON | OFF deriving (Eq)
-- | Determines what channels are checked for liveness: SRCS is for output of the sources, ND is for outputs of the sources and outputs of all components with non-deterministic outputs, ALL - all channels are checked for liveness
data ChannelsToCheck = SRCS | ND | WHOLE

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
    argFullQueues :: Bool, -- ^ Allows user to turn on optimisation searching for never full queues.
    argNuxmvOptions :: ReachabilityOptions, -- ^ The options to use for reachability analysis.
    argUseInvariants :: Bool, -- ^ Determines whether invariants are calculated.
    showChannelTypes  :: Bool, -- ^ Determines whether channel types are displayed
    showChannelSource :: Bool, -- ^ Determines whether channel source info is displayed
    showChannelConnections :: Bool, -- ^ Determines whether channel connections are displayed
    showRings :: Bool, -- ^ Determines whether ring information is displayed
    detectRings :: Bool, -- ^ Determines whether ring detection is done
    detectLivelock :: Bool, -- ^ Determines whether livelock detection is done
    replaceAutomata :: Bool, -- ^ Replaces all automata in the network, such that behavior of the automata is mimicked using standard primitives
    whatToCheck :: ChannelsToCheck, -- ^ Determines what channels are checked for liveness: SRCS is for output of the sources, ND is for outputs of the sources and outputs of all components with non-deterministic outputs, ALL - all channels are checked for liveness
    smtAllChans :: Bool, -- ^ Determines if SMT checks all channels simultaneously or not
    backwardReachInvar :: Int
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
    argFullQueues = False,
    argNuxmvOptions = ReachabilityOptions {
        keepAigerModel = False,
        keepNuxmvModel = 0,
        reachabilityEngine = NUXMV IC3M
    },
    argUseInvariants = True,
    showChannelTypes = False,
    showChannelSource = False,
    showChannelConnections = False,
    showRings = False,
    detectRings = True,
    detectLivelock = True,
    replaceAutomata = False,
    whatToCheck = WHOLE,
    smtAllChans = False,
    backwardReachInvar = 0
}


getChannelsToCheck :: ColoredNetwork -> ChannelsToCheck -> [ChannelID]
getChannelsToCheck net SRCS = filter (\x -> case getComponent net (getInitiator net x) of Source{} -> True; _ -> False) (getChannelIDs net)
getChannelsToCheck net ND = filter (\x -> case getComponent net (getInitiator net x) of Source{} -> True; Automaton{} -> True; LoadBalancer{} -> True; Match{} -> True; MultiMatch{} -> True; _ -> False) (getChannelIDs net)
getChannelsToCheck net _ = getChannelIDs net

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

-- some helpers used to calculate formulas for the nuxmv model
literals :: ColoredNetwork -> [ChannelID] -> Seq Formula
literals net chans = Seq.fromList $ map (\x -> NOT $ AND (Set.fromList [NOT (Lit $ IdleAll (src 174) x Nothing),Lit (BlockAny (src 174) x Nothing)])) chans
--literals net _ = Seq.fromList $ map (\x -> mkLiteral net x) (getAllSourceIDs net)

mkLiteral :: ColoredNetwork -> ComponentID -> Formula
mkLiteral net i = NOT $ Lit $ BlockSource i
--mkLiteral _ _ _ = F

spec :: ColoredNetwork -> [ChannelID] -> Formula
spec net chans = conjunctive $ literals net chans

{-debug stuff-}
testChanID :: ChannelID
testChanID = (ChannelIDImpl 62)

testFormula :: Formula
testFormula = Lit $ BlockAny ("",0) testChanID (Just (ColorSet Set.empty))
{-***********-}

runDeadlockDetection :: ColoredNetwork -> CommandLineOptions -> [Invariant Int] -> [ComponentID] -> IO (Either String (Bool, Maybe SMTModel))
runDeadlockDetection net options invs nfqs =
    -- Export invariants to their SMT expression
    let (smtinvs, qs, vars) = export_invariants_to_smt net show_p invs

        -- formula for the nuXmv model
        spec' = spec net (getChannelsToCheck net (whatToCheck options))
        allFormulas = unfold_formula net (BlockVars Seq.empty nfqs) spec'
        reachability_model = (ReachabilityInput net allFormulas (Just spec') invs)
        reachability_model_invs_only = (ReachabilityInput net Map.empty Nothing invs)
        -- write nuXmv model
        written_model = case (keepNuxmvModel (argNuxmvOptions options)) of
            1 -> reachability_model
            2 -> reachability_model_invs_only
            _ -> reachability_model
        nuxmv_model = writeModel written_model

        -- reachability analysis
        nuxmv :: IO (Either String (Bool, Maybe SMTModel))
        nuxmv = do
            ret <- hasDeadlock (argNuxmvOptions options) reachability_model
            case ret of
                Left err -> return $ Left err
                Right b -> return $ Right (b,Nothing)

        smt :: IO (Either String (Bool, Maybe SMTModel))
        smt = if (smtAllChans options)
              then detectAllDeadlocks
              else case (argSources options) of
                     ALL -> smtPar
                     _   -> smtSeq

        -- deadlock analysis in parallel
        smtPar :: IO (Either String (Bool, Maybe SMTModel))
        smtPar = do
                eq_lst' <- eq_lst
                foldr f (return $ Right (False,Nothing)) eq_lst' where
                eq_lst :: IO [Either String (Bool, Maybe SMTModel)]
                eq_lst = Par.mapM detectDeadlock (getChannelsToCheck net (whatToCheck options))
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
        smtSeq = foldr (\x y -> doDeadlock x y) s (getChannelsToCheck net (whatToCheck options)) where
                doDeadlock :: ChannelID -> IO (Either String (Bool, Maybe SMTModel)) -> IO (Either String (Bool, Maybe SMTModel))
                doDeadlock i dl' = do
                    dl <- dl'
                    case (dl,i) of
                        (Right (False,Nothing),i') | not (emptyColorSet (getColorSet net i')) -> detectDeadlock i
                        _ -> return dl
                s = return $ Right (False,Nothing)

        -- components that are never blocked (currently not used)
        live = Seq.empty

        -- Determine the block formula of the source. Export it to an SMT solver.
        -- Based on the result, update the set of live components or not.
        detectDeadlock :: ChannelID -> IO (Either String (Bool, Maybe SMTModel))
        detectDeadlock i = let
            name = utxt . getName . getChannel net
            lit1 = IdleAll (src 174) i Nothing --IdleAll (src 174) i (Just (getColorSet net i))
            lit2 = BlockAny (src 174) i Nothing {-BlockAny (src 174) i (Just (getColorSet net i))-} in
            --blockLit = (AND (Set.fromList [NOT (Lit $ IdleAll (src 174) i (Just (getColorSet net i))),Lit (BlockAny (src 174) i (Just (getColorSet net i)))])) in
                do
                    --when (argVerbose options == ON) $ putStrLn ("Starting deadlock detection for source " ++ name i)
--                    nfqs' <- nfqs -- (js) this takes quite a lot of time ! I would turn in off for now.
                    --when (argVerbose options == ON) $ putStrLn ("Unfolding formulas and writing SMT model ... ")
                    let ret  = unfold_formula net (BlockVars live nfqs) (AND (Set.fromList [NOT (Lit $ IdleAll (src 174) i Nothing),Lit (BlockAny (src 174) i Nothing)]))
                      --unfold_formula net (BlockVars live nfqs) (AND (Set.fromList [NOT (Lit $ IdleAll (src 174) i (Just (getColorSet net i))),Lit (BlockAny (src 174) i (Just (getColorSet net i)))])) --{-# SCC "UnfoldFormula" #-} unfold_formula net (BlockVars live nfqs) (Lit blockLit) -- nfqs') (Lit blockLit)
                    let file = "deadlock_" ++ name i ++ ".smt2"
                    --error $ "DEBUG-OUT: " ++ invarToSMT net (backwardReachInvar options)
                    h <- openFile file WriteMode
                    hPutStrLn h $ "(set-logic QF_LIA)\n" ++ smtinvs
                    --hPutStrLn h $ ivars
                    hPutStrLn h $ export_bi_var_to_smt net show_p (Map.keys ret)
--export_formula_to_SMT :: ColoredNetwork -> (Set ComponentID) -> (Map ComponentID [Color], Set ComponentID) -> (Color -> String) -> Maybe Literal -> Formula -> (String, Set ComponentID, (Map ComponentID [Color], Set ComponentID))
                    foldM_ (\(qs',vars') (bi, f) -> do
                                                        let (smt',qs2,vars2) = export_formula_to_SMT net qs' vars' show_p (Just bi) f
                                                        hPutStrLn h $ smt'
                                                        return (qs2, vars2))
                           (qs, vars) (Map.toList ret)
                    --hPutStrLn h $ breach
                    hPutStrLn h $ "(assert " ++ "(and (not " ++ export_literal_to_SMT net show_p lit1 ++ ") " ++ export_literal_to_SMT net show_p lit2 ++ "))"
                    hPutStrLn h $ "(check-sat)\n(get-model)"
                    when (argVerbose options == ON) $ putStrLn ("Unfolding formulas and writing SMT model completed. ")
                    when (argVerbose options == ON) $ putStrLn ("Calling SMT solver ... ")
                    hClose h
                    (_exit,solver_output,_err) <- (uncurry readProcessWithExitCode) (solverFunction (argSMTSolver options) file) []
                    when (not $ argKeepSMTModel options) $ removeFile file
                    -- putStrLn solver_output
                    case parseSMTOutput solver_output of
                        Left err -> do return $ Left (unlines $ map messageString $ errorMessages err)
                        Right Nothing -> do when (argVerbose options == ON) $ putStrLn $ "== Channel " ++ name i ++ " is live."
                                            return $ Right (False,Nothing)
                        Right (Just model) -> do
                                            when (argVerbose options == ON) $ putStrLn $ "Channel " ++ name i ++ " has a possible deadlock:\n" ++ showModel model
                                            return $ Right (True, Just model)

        mkAssertions :: [ChannelID] -> String -> String
        mkAssertions [] s = "(assert " ++ s ++ ")"
        mkAssertions (x:xs) s = let lit1 i = IdleAll (src 174) i Nothing--IdleAll (src 174) i (Just (getColorSet net i))
                                    lit2 i = BlockAny (src 174) i Nothing--BlockAny (src 174) i (Just (getColorSet net i))
                                    res = "(and (not " ++ export_literal_to_SMT net show_p (lit1 x) ++ ") " ++ export_literal_to_SMT net show_p (lit2 x) ++ ")"
                                    res' = if s == ""
                                           then res
                                           else "(or " ++ res ++ " " ++ s ++ ")"
                                in mkAssertions xs res'


        detectAllDeadlocks :: IO (Either String (Bool, Maybe SMTModel))
        detectAllDeadlocks = let name = "all_dls"
                             in
            --blockLit = (AND (Set.fromList [NOT (Lit $ IdleAll (src 174) i (Just (getColorSet net i))),Lit (BlockAny (src 174) i (Just (getColorSet net i)))])) in
                do
                    --when (argVerbose options == ON) $ putStrLn ("Starting deadlock detection for source " ++ name i)
--                    nfqs' <- nfqs -- (js) this takes quite a lot of time ! I would turn in off for now.
                    --when (argVerbose options == ON) $ putStrLn ("Unfolding formulas and writing SMT model ... ")
                    let ret  = unfold_formula net (BlockVars live nfqs) (spec net (getChannelsToCheck net (whatToCheck options))) --{-# SCC "UnfoldFormula" #-} unfold_formula net (BlockVars live nfqs) (Lit blockLit) -- nfqs') (Lit blockLit)
                    let file = "deadlock_" ++ name ++ ".smt2"
                    let ivars = if (backwardReachInvar options) > 0
                                then makeVars net (backwardReachInvar options)
                                else ""
                    let breach = if (backwardReachInvar options) > 0
                                 then invarToSMT net (backwardReachInvar options)
                                 else ""
                    h <- openFile file WriteMode
                    hPutStrLn h $ "(set-logic QF_LIA)\n" ++ smtinvs
                    hPutStrLn h $ ivars
                    hPutStrLn h $ export_bi_var_to_smt net show_p (Map.keys ret)
--export_formula_to_SMT :: ColoredNetwork -> (Set ComponentID) -> (Map ComponentID [Color], Set ComponentID) -> (Color -> String) -> Maybe Literal -> Formula -> (String, Set ComponentID, (Map ComponentID [Color], Set ComponentID))
                    foldM_ (\(qs',vars') (bi, f) -> do
                                                        let (smt',qs2,vars2) = export_formula_to_SMT net qs' vars' show_p (Just bi) f
                                                        hPutStrLn h $ smt'
                                                        return (qs2, vars2))
                           (qs, vars) (Map.toList ret)
                    hPutStrLn h $ breach
                    hPutStrLn h $ mkAssertions (getChannelsToCheck net (whatToCheck options)) ""
                    hPutStrLn h $ "(check-sat)\n(get-model)"
                    when (argVerbose options == ON) $ putStrLn ("Unfolding formulas and writing SMT model completed. ")
                    when (argVerbose options == ON) $ putStrLn ("Calling SMT solver ... ")
                    hClose h
                    (_exit,solver_output,_err) <- (uncurry readProcessWithExitCode) (solverFunction (argSMTSolver options) file) []
                    when (not $ argKeepSMTModel options) $ removeFile file
                    -- putStrLn solver_output
                    case parseSMTOutput solver_output of
                        Left err -> do return $ Left (unlines $ map messageString $ errorMessages err)
                        Right Nothing -> do when (argVerbose options == ON) $ putStrLn $ "All channels are live"
                                            return $ Right (False,Nothing)
                        Right (Just model) -> do
                                            when (argVerbose options == ON) $ putStrLn $ "There is a possible deadlock:\n" ++ showModel model
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
