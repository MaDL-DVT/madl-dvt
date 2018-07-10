{-# LANGUAGE OverloadedStrings, CPP #-}

{-|
Module      : Examples
Description : Provides predefined networks.
Copyright   : (c) Tessa Belder 2015.

Provides predefined networks.
-}
module Examples(
    networkMap, networkMapFlattened, networkMapTyped,
    module Examples.InvariantTestNetwork,
    module Examples.Macros,
    module Examples.MergeSwitchNetwork,
    module Examples.MergeBlock,
    module Examples.ReorderTestNetwork,
    module Examples.SmallAutomatonNetwork,
    module Examples.SmallFunctionNetwork,
    module Examples.SmallMacroTest,
    module Examples.SmallMatchNetwork,
    module Examples.SmallSwitchNetwork,
    module Examples.SmallTestNetwork,
    module Examples.TwoAgents,
    module Examples.AllPrimitives,
    module Examples.RedBlue,
    module Examples.TypesAndFunctions
#ifdef EIGHT_ROUTER
    ,module Examples.EightRouterModel
#endif
) where

import Examples.InvariantTestNetwork
import Examples.Macros
import Examples.MergeBlock
import Examples.MergeSwitchNetwork
import Examples.ReorderTestNetwork
import Examples.SmallAutomatonNetwork
import Examples.SmallFunctionNetwork
import Examples.SmallMacroTest
import Examples.SmallMatchNetwork
import Examples.SmallSwitchNetwork
import Examples.SmallTestNetwork
import Examples.TwoAgents
import Examples.AllPrimitives
import Examples.RedBlue
import Examples.TypesAndFunctions
#ifdef EIGHT_ROUTER
import Examples.EightRouterModel
#endif

import Data.HashMap as Hash
import Madl.Network

import Utils.Text

-- | Map containing the predefined networks
networkMap :: Hash.Map Text MadlNetwork
networkMap = Hash.fromList [
    ("itn", itn),
    ("itn2", itn2),
    ("msn", msn),
    ("rtn-22F", rtn 1 2 2 False),
    ("rtn-32F", rtn 1 3 2 False),
    ("rtn-23F", rtn 1 2 3 False),
    ("rtn-34F", rtn 1 3 4 False),
    ("rtn-45F", rtn 1 4 5 False),
    ("rtn-22T", rtn 1 2 2 True),
    ("rtn-32T", rtn 1 3 2 True),
    ("rtn-23T", rtn 1 2 3 True),
    ("rtn-34T", rtn 1 3 4 True),
    ("rtn-45T", rtn 1 4 5 True),
    ("rtn2-2F", rtn 2 2 0 False),
    ("rtn2-3F", rtn 2 3 0 False),
    ("rtn2-2T", rtn 2 2 0 True),
    ("rtn2-3T", rtn 2 3 0 True),
    ("rtn3-22F", rtn 3 2 2 False),
    ("rtn3-32F", rtn 3 3 2 False),
    ("rtn3-23F", rtn 3 2 3 False),
    ("rtn3-22T", rtn 3 2 2 True),
    ("rtn3-32T", rtn 3 3 2 True),
    ("rtn3-23T", rtn 3 2 3 True),
    ("san", san),
    ("sfn", sfn),
    ("smn", smn),
    ("smt", smt),
    ("smt2", smt2),
    ("smt3", smt3),
    ("sct", sct),
    ("ssn", ssn),
    ("stn", stn),
    ("allprim", allPrimitives False),
    ("allprimDL", allPrimitives True),
    ("twoagents10", two_agents 10 10 2),
    ("twoagents9", two_agents 9 10 2),
    ("twoagents8", two_agents 8 10 2),
    ("twoagents2", two_agents 2 2 2),
    ("mergeblock", mergeBlock),
    ("redblue"   , redblue False),
    ("redblueDL" , redblue True)
#ifdef EIGHT_ROUTER
    ,("8router", eightRouter True True 2)
    ,("8routerDL", eightRouter True False 2)
#endif
    ]

-- | Map containing flattened versions of the predefined networks.
networkMapFlattened :: Hash.Map Text FlattenedNetwork
networkMapFlattened = fmap unflatten networkMap_flat where
    networkMap_flat :: Hash.Map Text FlatFlattenedNetwork
    networkMap_flat = fmap unfoldMacros networkMap

-- | Map containing colored versions of the predefined networks.
networkMapTyped :: Hash.Map Text ColoredNetwork
networkMapTyped = fmap channelTypes networkMapFlattened
