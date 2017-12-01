{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, PartialTypeSignatures #-}

{-|
Module      : Madl2Verilog.Automaton
Description : Conversion of MaDL automata to System Verilog.
Copyright   : (c) 2016-2017 Eindhoven University of Technology
Authors     : Tessa Belder 2016, Julien Schmaltz 2017

Contains functions to transform madl automata to verilog code.

The structure of the generated FSM is inspire from 
  https://inst.eecs.berkeley.edu/~cs150/sp12/resources/FSM.pdf

si -- cond -> sj

data_i = state_val && cond ? val1 : val2 ;



-}
module Madl2Verilog.Automaton (
    declareAutomatonComponent
) where

-- import Debug.Trace

import qualified Data.Text as T
import qualified Data.IntMap as IM

import Utils.Text

import Madl.MsgTypes

import Madl.Network

import Madl2Verilog.VerilogConstants
import Madl2Verilog.VerilogGen
import Madl2Verilog.Component
import Madl2Verilog.Functions

import Math.NumberTheory.Logarithms

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Automaton"

fatal :: Int -> Text -> a
fatal i s = error ("Fatal "++show i++" in " ++utxt fileName ++":\n  "++utxt s)

src :: Int -> (Text, Int)
src i = (fileName, i)

_okWhenNotUsed :: a
_okWhenNotUsed = undefined fatal src
-- End of error function

-----------------------------------
-- Functions to generate Verilog --
-----------------------------------

-- | Declare automaton component
declareAutomatonComponent :: Bool -> Maybe Int -> ComponentInfo -> VerilogCode
declareAutomatonComponent useInterface mtype comp = declareModule useInterface automatonModule where
    automatonModule = VModule {
        vmoduleName = funModuleName,
        vmoduleParams = [],
        vmoduleHasTime = hasTimeFromInfo comp,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface',
        vmoduleBody = automatonBody useInterface comp
    }

    funModuleName = vType mtype $ vAutomaton (T.intercalate "_" $ compIdentifier comp)

    vmoduleInterface' = map (uncurry inputPort) inputs ++ map (uncurry outputPort) outputs
    inputPort pname ptype = VInterfacePort (Just MInput) (Right . Just . Data . Left $ encodingSize ptype) pname
    outputPort pname ptype = VInterfacePort (Just MOutput) (Right . Just . Data . Left $ encodingSize ptype) pname
    inputs = zip (inputPorts (length inputtypes, compComponent comp)) inputtypes
    outputs = zip (outputPorts (compComponent comp, length outputtypes)) outputtypes
    inputtypes = compInputTypes comp
    outputtypes = compOutputTypes comp

-- | Body of an automaton module
automatonBody :: Bool -> ComponentInfo -> VerilogCode
automatonBody _useInterface _comp =  
    declareFunctions _useInterface Nothing _comp ++ -- JS this generates nothing for now
    createBFunction "fun_x" (epsilon (tr!!0)) (IM.fromList [(0,(constColorSet "blue", ("foo",Just (fromInteger 0,fromInteger 1)))),(1,(constColorSet "blue", ("foo",Just (fromInteger 0,fromInteger 1))))])++
    generateStateEncoding _comp++ 
    generateStateRegDeclaration st_width++
    generateStateUpdate ++
    generateStateTransitions tr (2^st_width -1) ++
    [(showT tr)]
    where
        c        = compComponent _comp
        n_st     = nrOfStates c
        st_width = genStateBitWidth n_st
        tr       = transitions c

-- | Generate state encoding
-- 
{-- 
For the state encoding, we use local parameters:
localparam STATE_Initial = n'd0,
           STATE_1 = n'd1,
           STATE_end = n'dN-1;

where 
- n = number of bits required encode all states
- N = number of states

Note that not all states are used. We will generate non-conditional
transitions from the unused states to the initial one. 
--}
generateStateEncoding :: ComponentInfo-> VerilogCode
generateStateEncoding _comp = 
    commentHeader 
                "State Encoding"
                (["localparam "]++
                 indents (declareParams2 (genLocalStateValueList (2^s_width - 1) s_width)))
    where 
        n_st    = nrOfStates $ compComponent _comp
        s_width = genStateBitWidth n_st


-- | Generate a list [(p,v)] where p is a state variable 
-- name and v is its value. We generate the following variables:
-- STATE_Initial = n'd0
-- STATE_1 = n'd1
-- STATE_(N-1) = n'd(n-1)
-- where n is the bit width computed by genStateBitWidth
-- the first parameter is the number of states
-- the second parameter is the bit width
genLocalStateValueList :: Int -> Int -> [VParameter] 
genLocalStateValueList 0 st_width = 
    [(mkStateLabel 0,(txt (prefix++"0")))]
    where 
        prefix = (show st_width)++"'d"
genLocalStateValueList n st_width = 
    [(mkStateLabel n,(txt (prefix ++numero)))]++(genLocalStateValueList (n - 1) st_width)
    where 
        prefix = (show st_width)++"'d"
        numero = show n

-- | Generate bit width required to store the states of a process.
-- The first parameter is the number of states needed to be encoded.
genStateBitWidth :: Int -> Int
genStateBitWidth n = ((integerLog2 $ toInteger (n-1)) + 1)

-- | Generate the declaration of the state registers.
-- We declare two registers:
-- 1. CurrentState
-- 2. NextState
-- The first argument gives the range of the registers
generateStateRegDeclaration :: Int -> VerilogCode
generateStateRegDeclaration n = 
    commentHeader 
                "State Registers" 
                (declareRegister (txt "x",0)  (0,n) "CurrentState"++
                 declareRegister (txt "x",0) (0, n) "NextState")
  
-- | Generate synchronous state update.
generateStateUpdate :: VerilogCode
generateStateUpdate = 
    commentHeader 
                "Synchronous State Update"
                (declareAlwaysBlock 
                   (declarePosEdgeClk (txt "clk"))
                   (indents (assignNonBlock "CurrentState" (vlog_ite (esc "rst") "STATE_0" (esc "NextState")))))
  

-- | Generate the state transitions.
-- A transition has the following parameters:
-- startState :: Int
-- endState :: Int
-- inPort :: Int 
-- epsilon :: MFunctionBool, guard ? 
-- evenFunction :: Int -> Color -> Bool
-- The event function reads a channel (i) and a packet.
-- It is true when the automaton is ready to accept color on the channel. 
-- outPort : Maybe Int
-- phi :: Maybe (MFunctionDisj)
-- packetTransformationFunction :: Int -> Color -> Maybe (Int, Color)

{-- 

The definition of the transitions has the following structure:
NextState = CurrentState;
case (CurrentState)
    STATE_i: begin
        // all transitions from STATE_i ? 
        // we create here an order between the transition
        // at the MaDL level there is no such order. 
        if (read/write/rw(irdy,trdy,port) && guard_condition) then 
            NextState = target_state;
        if (...) transition 2
        if (...) transition 3 
    end
    ...
endcase

--}
generateStateTransitions :: [AutomatonTransition] -> Int -> VerilogCode
generateStateTransitions _tr _numStates = 
    commentHeader 
                "State Transitions"
                (declareAlwaysBlock 
                    (txt "*") 
                    (indents 
                        [(esc "NextState")+++(txt " = ")+++(esc "CurrentState")+++(txt ";")]
                        ++
                        (indents (declareCaseStatement (esc "CurrentState") (indents _body)))))
    where 
        _body = generateStateTransitionsBody _tr _numStates

generateStateTransitionsBody :: [AutomatonTransition] -> Int -> [Text]
generateStateTransitionsBody _tr 0 = (declareCaseItem (mkStateLabel 0) _it_body)
    where _it_body = (generateTransitionCodeForState _tr 0)
generateStateTransitionsBody _tr n = (declareCaseItem (mkStateLabel n) _it_body) ++ generateStateTransitionsBody _tr (n-1)
    where _it_body = (generateTransitionCodeForState _tr n)

-- | Filter transitions on the starting state
filterTransStartState :: [AutomatonTransition] -> Int -> [AutomatonTransition]
filterTransStartState _tr _st_ID = filter (\x -> startState x == _st_ID) _tr

-- | Generate code for transitions from a given state, if no transitions
-- generate a transition to the initial state.
generateTransitionCodeForState :: [AutomatonTransition] -> Int -> VerilogCode
generateTransitionCodeForState _tr _st_ID = 
    if (_tr' == []) 
        then [assignBlock "NextState" (mkStateLabel 0)]
    else
        map (generateTransitionCode) _tr'
    where
        _tr' = filterTransStartState _tr _st_ID

-- | Generate a state update for one transition
generateTransitionCode :: AutomatonTransition -> Text
generateTransitionCode _tr =
    assignBlock "NextState" _assignment
    where
        _endState   = "STATE_"+++(showT $ endState _tr)
        _inputPort  = inPort _tr
        _cond_ins   = generateTxCondInputPorts  _inputPort
        _cond_outs  = case outPort _tr of 
            Nothing -> []; 
            Just op -> generateTxCondOutputPorts op
        _cond       = generateTxCond (_cond_ins++_cond_outs)
        _assignment = vlog_ite _cond _endState (esc "CurrentState")

-- | Generate condition for a transfer on port with number port_nb.
generateTxCond :: [Text] -> Text
generateTxCond lst = mkParentheses $ T.intercalate " & " lst 

generateTxCondInputPorts :: Int -> [Text]
generateTxCondInputPorts port_nb = 
    [ (esc ("i"+++(showT port_nb)+++"$irdy")), 
      (esc ("i"+++(showT port_nb)+++"$trdy"))] 

generateTxCondOutputPorts :: Int -> [Text]
generateTxCondOutputPorts port_nb = 
    [ (esc ("o"+++(showT port_nb)+++"$irdy")), 
      (esc ("o"+++(showT port_nb)+++"$trdy"))] 

mkStateLabel :: Int -> Text
mkStateLabel n = "STATE_"+++(showT n)

-- | Generate computation of the outputs.
-- always@ (*) begin
-- \oi$data = default value;
-- case (\CurrentState ) begin
-- endcase
-- end








