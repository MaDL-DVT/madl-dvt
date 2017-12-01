{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleContexts, OverloadedStrings, ScopedTypeVariables, NoImplicitPrelude #-}
-- I don't know what the -fwarn-auto-orphans switch does, but it creates an awful lot of warnings when -O or -O2 is used

{-|
Module      : Verilog.Processor
Copyright   : (c) Sebastiaan J C Joosten

This module should take a set of modules, and sets their interdependencies right.
It does the same for ports, using the set of interdependent modules.
-}
module Verilog.Processor ( processModule
                         , WireValue(..), VerilogWireType(..)
                         , modName
                         , VerilogModule
                         , Instantiation(INST)
                         , GetBitsType
                         , variablesInExpr
                         , getBit2
                         , getBitsChangeBPart
                         ) where
import CommonDataTypes.Syntax -- data types
import qualified Data.Map as Map -- (Map,unionsWith,alter,empty,insert, lookup,fromListWith,elems,map,keys,(!),union,mapWithKey,fromList,toList)
import Data.ByteString as B  (ByteString)
import qualified Data.Vector as Vector (Vector,fromList,toList,map,(!))
import BooleanSymbolic.Class (BooleanXZ(..),Boolean(..),BooleanResult,trueC,falseC,getUniqueVariants,AtomToBoolean(..))
import BaseLike.CustomPrelude
import Debug.Trace (trace)

_unused :: a
_unused = undefined fatal trace

fatal :: Int -> [Char] -> t
fatal n s = error ("Fatal "++show n++" in Verilog.Processor.hs:\n  "++s)
fatalDuplicates :: String -> a -> a -> a
fatalDuplicates s = fatal 35 $ "Duplicate map keys!\n  "++s

-- | TODO
modName :: VerilogModule -> VerilogIdentifier
modName (VerilogModule nm _ _ _) = nm

-- | TODO
type GetBitsType atomType boolType
 = Map.Map VerilogIdentifier ( Vector.Vector ( atomType, boolType ) -- its values
                             , Maybe Bool -- whether this is big or little endian, or a single bit
                             )

-- | TODO
getBitsChangeBPart :: (Ord a)
         => (a -> b -> c)
         -> GetBitsType a b -> GetBitsType a c
getBitsChangeBPart f gb = Map.map (\(vec,bl) -> (fmap (\(a,b) -> (a,f a b)) vec,bl)) gb

-- There are three ways we reference a wire:
-- 1. (name, Maybe Int): the "Maybe" is Nothing when the wire is declared as a single bit
-- 2. (name, Int): when instantiating a parameter of another module, we cannot determine whether that wire is declared as a single bit or not
-- 3. atomtype: this is the internal representation used for booleans. For instance, it may be a C-Int inside a monad indicating some (FR)AIG node number
-- Since we cannot sort by atomtype (as it could be in a monad), we build a map from 1. to 3.
-- When instantiating parameters, we are forced to use type 2.
-- Since every wire is declared only once, you may assume that (name, Nothing) and (name, Just i) do not co-exist.
-- (Checking this has caught a bug in the past)

-- | TODO
data WireValue e = WV e -- wire value
                      [INSTREF] -- modules involved

instance Show e => Show (WireValue e) where
 show (WV a []) = "WV "++show a
 show (WV a _) = "WV "++show a++" [..]"

type INSTREF = ( Int -- number of the instance
               , (ByteString, Int) -- parameter in that instance from which to get a value
               )

-- Only used in processModule
-- I made it into a separate data structure for code clarity (We were carrying around tuples and quadruples inside Either, which was a pain)
-- Basically a version of the VerilogStatement with these differences:
--   Gates become assignments
--   Assignments a = b are split into two assignments: a = b and b = a
--   Operations are translated into the BooleanClass variants
data SimpleStatement e
  = InstanceSTMT ByteString -- module instantiation
                 ByteString -- instantiation name
                 [ ( (ByteString, Int) -- variable being instantiated
                   , e) -- its value
                 ]
                 -- and the reverse ‘map’ in which duplicates may occur on both sides
                 [((ByteString, Maybe Int), (ByteString, Int))]
                 -- the following should hold: (this specifies the second map)
                 -- map2 ; map1 ≥ id[dom(map2)] ≤ id[(VX.APair AtomType)]
                 -- map1 ; map2 ≤ id[(ByteString,Int)]
  | AssignSTMT  (ByteString, Maybe Int) -- original name of the wire
                e -- value of a wire

mustBeOne :: [a] -> String -> a
mustBeOne [a] _ = a
mustBeOne lst s = fatal 107 (s++" (got "++show (length lst)++" instead of 1)")

-- | TODO
variablesInExpr :: forall atomType boolType.
                ( AtomToBoolean ByteString (BooleanResult boolType)
                , BooleanXZ boolType )
                => GetBitsType atomType (BooleanResult boolType) -> VerilogExpression -> [(Maybe (VerilogIdentifier, Maybe Int), BooleanResult boolType)]
variablesInExpr localWireDeclarations = variablesInExpr'
 where
  variablesInExpr' :: VerilogExpression -> [(Maybe (VerilogIdentifier, Maybe Int), BooleanResult boolType)]
  variablesInExpr' (VerilogConcatenate exprs) = concat (map variablesInExpr' exprs)
  variablesInExpr' (VerilogVariableSelection start end idt)
   = case b of
      Just True -> reverse (drop end (take (start+1) res)) -- high to low
      Just False -> drop start (take (end+1) res) -- low to high
      _ -> fatal 472 "Bit selection on a single bit!"
   where (lst,b) = getBools' toBoolean localWireDeclarations idt
         res = [ (Just (idt, Just bit), v) | (bit,v)<-zip [0..] (Vector.toList lst)]
  variablesInExpr' (VerilogVariable idt)
   = case getBools' toBoolean localWireDeclarations idt of
      (lst,Just _ ) -> [ (Just (idt, Just bit), v) | (bit,v) <- zip [0..] (Vector.toList lst)]
      (lst,Nothing) -> [ (Just (idt, Nothing ), v) | v <- (Vector.toList lst)]
  variablesInExpr' (VerilogBit (a,b))
   = [(Nothing, toVal (a, b))]
   where toVal (True ,True ) = trueC
         toVal (True ,False) = xC
         toVal (False,True ) = zC
         toVal (False,False) = falseC
  variablesInExpr' (VerilogITE x y z) = [ (Nothing, join$ iteC <$> expression x <*> (expression y) <*> (expression z)) ]
  variablesInExpr' (VerilogAND a b  ) = [ (Nothing, join$ andC <$> expression a <*> (expression b)                   ) ]
  variablesInExpr' (VerilogOR  a b  ) = [ (Nothing, join$ orC  <$> expression a <*> (expression b)                   ) ]
  variablesInExpr' (VerilogNOT a    ) = [ (Nothing, join$ notC <$> expression a                                      ) ]
  {- variablesInExpr' (VerilogPRE expr ) = map f (variablesInExpr' expr)
    where f (_,b) = (Nothing, scopePreB b) -}
  expression e = snd (mustBeOne (variablesInExpr' e) "Parsing unexpected expression; expecting a one-bit expression, got a different number of bits instead. Did you translate this Verilog to netlist first?")

unravel :: forall m boolType atomType.
           ( AtomToBoolean ByteString (m boolType)
           , AtomToBoolean ByteString atomType
           , BooleanXZ boolType
           , m ~ (BooleanMonad boolType)
           -- , Monad m -- because Boolean m boolType
           -- , Boolean m boolType -- because BooleanXZ m boolType
           )
        => GetBitsType atomType (m boolType) -> VerilogModuleStatement -> [SimpleStatement (m boolType)]
unravel v3 stmt = unravel' stmt
  where
    bitParam (VerilogModuleParameterInstantiation _ expr) = expression expr
    getBit :: ByteString -> Maybe Int -> m boolType
    getBit a b = (\lw -> snd (getBit2 lw a b)) v3
    variablesInExpr' :: VerilogExpression -> [(Maybe (VerilogIdentifier, Maybe Int), m boolType)]
    variablesInExpr' v = variablesInExpr v3 v
    expression :: VerilogExpression -> m boolType
    expression e = snd (flip mustBeOne "Parsing unexpected expression; expecting a one-bit expression, got a different number of bits instead. Did you translate this Verilog to netlist first?"
                             (variablesInExpr' e))
    -- unravel' will translate a statement into something that is pre-translated, see the documentation of
    -- "SimpleStatement" above
    unravel' :: VerilogModuleStatement -> [SimpleStatement (m boolType)]
    unravel' (VerilogUnhandled _ _) = [] -- something that can safely be ignored
    unravel' (VerilogDeclare _ _ _ _) = [] -- handled elsewhere
    unravel' (VerilogInstantiate m _ [] _) = fatal 111 ("Module "++unpack m++" instantiated without any connections")
    unravel' (VerilogInstantiate modname instanceName instparams@(firstParam:restParams) _)
     = case modname of -- instantiate all the modules we understand immediately
         "and"     -> assignTo $          (foldrM' andC trueC  (map bitParam restParams))
         "or"      -> assignTo $          (foldrM' orC  falseC (map bitParam restParams))
         "xor"     -> assignTo $          (foldrM' xorC falseC (map bitParam restParams))
         "nand"    -> assignTo $ notC =<< (foldrM' andC trueC  (map bitParam restParams))
         "nor"     -> assignTo $ notC =<< (foldrM' orC  falseC (map bitParam restParams))
         "buf"     -> assignTo $ bufC =<< (foldrM' orC  falseC (map bitParam restParams))
         "not"     -> assignTo $ notC =<< (bitParam$ mustBeOne restParams "not-gate(output,input) should have exactly one output")
         "bufif1"  -> case restParams of
                        [val,enable] -> assignTo ( join$ gbufC <$> (bitParam enable) <*> (bitParam val) )
                        _ -> fatal 121 ("bufif1 takes three arguments (got "++show (length instparams)++")")
         "nmos"    -> case restParams of -- future work: add a uni-directionality check
                        [val,enable] -> assignTo ( join$ gbufC <$> (bitParam enable) <*> (bitParam val) )
                        _ -> fatal 121 ("nmos takes three arguments (got "++show (length instparams)++")")
         "tranif1"  -> case restParams of
                        [val,enable] -> [AssignSTMT (paramSubexprs firstParam) ( join$ gbufC <$> bitParam enable <*> (bitParam val) )
                                        ,AssignSTMT (paramSubexprs val)        ( join$ gbufC <$> bitParam enable <*> (bitParam firstParam) )
                                        ]
                        _ -> fatal 121 ("tranif1 takes three arguments (got "++show (length instparams)++")")
         "bufif0"  -> case restParams of
                        [val,enable] -> assignTo ( join$ gbufC <$> (notC =<< bitParam enable) <*> (bitParam val) )
                        _ -> fatal 121 ("bufif1 takes three arguments (got "++show (length instparams)++")")
         "pmos"    -> case restParams of -- future work: add a uni-directionality check
                        [val,enable] -> assignTo ( join$ gbufC <$> (notC =<< bitParam enable) <*> (bitParam val) )
                        _ -> fatal 121 ("pmos takes three arguments (got "++show (length instparams)++")")
         "tranif0"  -> case restParams of
                        [val,enable] -> [AssignSTMT (paramSubexprs firstParam) ( join$ gbufC <$> (notC =<< bitParam enable) <*> (bitParam val) )
                                        ,AssignSTMT (paramSubexprs val)        ( join$ gbufC <$> (notC =<< bitParam enable) <*> (bitParam firstParam) )
                                        ]
                        _ -> fatal 121 ("tranif0 takes three arguments (got "++show (length instparams)++")")
         "cmos"  -> case restParams of
                        [val,enable1,enable0]
                         -> assignTo ( join$ combineC <$> (join$ gbufC <$> (notC =<< bitParam enable0) <*> (bitParam val))
                                                      <*> (join$ gbufC <$> (         bitParam enable1) <*> (bitParam val)))
                        _ -> fatal 121 ("tranif0 takes four arguments (got "++show (length instparams)++")")
         _         -> case instanceName of -- name is required for scoping
                        Just nm -> let zips = [ ((,) nm' . zip [0..] . variablesInExpr') param
                                              | VerilogModuleParameterInstantiation (Just nm') param <- instparams
                                              ]
                                       parameterInstantiation =
                                                [ ((nm',i),(subexpr,val))
                                                | (nm', l2) <- zips
                                                , (i,(subexpr,val)) <- l2 ]
                                       paramValues = [ ((nm',i),val)
                                                     | ((nm',i),(_,val)) <- parameterInstantiation ]
                                       varValues   = [ ((v,w),param)
                                                     | (param,(Just (v,w),_)) <- parameterInstantiation ]
                                   in  [InstanceSTMT modname nm paramValues varValues]
                        _ -> fatal 203 $"No definition for the gate "++unpack modname++" found. (If this is a module instance, please provide an instance name)"
      where assignTo :: m boolType -> [SimpleStatement (m boolType)]
            assignTo v = [AssignSTMT (paramSubexprs firstParam) v]
            paramSubexprs (VerilogModuleParameterInstantiation _ expr)
              = ( mustBeJust . fst . flip mustBeOne "Output port in a gate must be a single variable" . variablesInExpr' )
                expr
            mustBeJust (Just a) = a
            mustBeJust _ = fatal 157 "Could not find a valid parameter name"
    unravel' (VerilogAssign id1 bit expr _) -- these assign just one bit thanks to preprocessing
      = case expr of
         VerilogVariable                 id2 -> [ AssignSTMT (id1,bit      ) $ getBit id2  Nothing
                                                , AssignSTMT (id2,Nothing  ) $ getBit id1  bit      ]
         VerilogVariableSelection _ bit2 id2 -> [ AssignSTMT (id1,bit      ) $ getBit id2 (Just bit2)
                                                , AssignSTMT (id2,Just bit2) $ getBit id1  bit      ]
         _ -> [ AssignSTMT (id1,bit) $ expression expr ]

-- | process a module into unsimplified wire values
-- this function has three main parts:
-- 1. translate every expression into a list of variables (for assigning to it)
--    together with their values (for assigning from it)
-- 2. translate every statement into something simple. This function is called "unravel".
--    it uses 1. where expressions are encountered
-- 3. putting everything together into a map of assignments to variables, namely wireAssignments
--    and getting the remaining instantiations, namely instances.
--    This step uses step 2
processModule :: forall m1 boolType1 m2 boolType2 atomType.
                 ( AtomToBoolean ByteString (m1 boolType1)
                 , AtomToBoolean ByteString (m2 boolType2)
                 , AtomToBoolean ByteString atomType
                 , BooleanXZ boolType1
                 , Applicative m1
                 , BooleanXZ boolType2
                 , Applicative m2
                 , m1 ~ BooleanMonad boolType1
                 , m2 ~ BooleanMonad boolType2
                 -- , Monad m -- because Boolean m boolType
                 -- , Boolean m boolType -- because BooleanXZ m boolType
                 )
              => Bool -- whether or not to treat as a black box
              -> VerilogModule
              -> ( B.ByteString
                 , ( m1 ( Map.Map (ByteString, Maybe Int) (atomType, WireValue boolType1, VerilogWireType)
                        , GetBitsType atomType (m1 boolType1) -- already sequenced, this m1 does not "do" anything here!
                        )
                   , (Vector.Vector (Instantiation (m2 [((ByteString,Int),boolType2)])))
                   )
                 )
processModule
 isBlackBox
 ( VerilogModule name _ _ statements )
 = ( name -- name of the module
   , ( do v3 <- traverse seqMapItm localWireDeclarations :: m1 (GetBitsType atomType (m1 boolType1))
          let assigningStatements :: [SimpleStatement (m1 boolType1)]
              assigningStatements = concat$ map (unravel v3) statements
          let (wireAssignments', _, _)
                = foldl' accumulate (return [], [], 0::Int) assigningStatements
          wireAssignments <- wireAssignments'
          v1 <- Map.mapWithKey isPort <$>
                 let zOnly = Map.fromList $
                              concat [ let (lst, bl) = (localWireDeclarations::(GetBitsType atomType (m1 boolType1))) Map.! n
                                       in [ ( (n,fmap (const i) bl)
                                            , (w, ([ toBoolean (n <> "_" <> pack (show i))
                                                   | isBlackBox && hasOutput dType ]
                                                  ,[]
                                                  )
                                              ))
                                          | ((w,_boolTypeVersionOfWire),i)<-zip (Vector.toList lst) [0..]]
                                     | (dType,_,n,_) <- declareStatements
                                     , portKindTester dType] -- make sure these have values at least
                 in  traverse combineVals
                     (if    isBlackBox
                      then  zOnly
                      else  foldl' buildMap zOnly wireAssignments -- map from wires to their symbolic values
                     )
          return (v1,v3)
     , let assigningStatements :: [SimpleStatement (m2 boolType2)]
           assigningStatements = concat$ map (unravel localWireDeclarations) statements
           (_, instances, _) = foldl' accumulate (return [], [], 0::Int) (assigningStatements :: [SimpleStatement (m2 boolType2)])
       in  Vector.fromList (if isBlackBox then [] else instances) -- list with instances
     )
   )
 where
  -- get the internal representation and the expression for a bit
  portKindTester dType = elem dType [Input,Output,InOut]
  portKinds = Map.fromListWithKey (\ n -> fatal 259 ("Multiple declarations for wire " ++ show n))
               [ (n,kind) | (kind,_,n,_) <- declareStatements, portKindTester kind]
  -- hasInput dType = elem dType [Input,InOut]
  hasOutput dType = elem dType [Output,InOut]
  isPort (s,_) (x,y)
       = (x,y, ( Map.findWithDefault Wire s portKinds ))
  accumulate :: forall m boolType. (BooleanXZ boolType , Applicative m, AtomToBoolean ByteString (m boolType), m~(BooleanMonad boolType))
             => ( m [((ByteString, Maybe Int), (atomType, ([boolType],[INSTREF])))]
                , [Instantiation (m [((ByteString, Int), boolType)])]
                , Int
                ) ->
                SimpleStatement (m boolType) ->
                ( m [((ByteString, Maybe Int), (atomType, ([boolType],[INSTREF])))]
                , [Instantiation (m [((ByteString, Int), boolType)])]
                , Int
                )
  accumulate (assignmentMap, instanceList, num) stmt
                  = case stmt of
                      AssignSTMT var@(varId,varNr) val
                        -> -- if onlyInput varId then o else -- turns out we CAN assign values to inputs
                           -- if this is bugging you, consider changing how to parse "assign .. = .." instead:
                           -- we could make this right to left only iff the rhs is an input wire
                           -- that would be a change in unravel, not a change here!
                           ( (:) <$> ((\val' -> (var, (getBitAsAtom varId varNr, ([val'], [])))) <$> val) <*> assignmentMap
                           , instanceList
                           , num )
                      InstanceSTMT modName' modname params occs
                        -> ( (++) [ ( (varId,varNr)
                                    , ( getBitAsAtom varId varNr
                                      , ([], [(num, param)])
                                      )
                                    )
                                  | ((varId,varNr),param) <- occs
                                  , not (onlyInput varId)
                                  ] <$> assignmentMap
                           , instanceList ++ [INST modName' modname (traverse sequenceA params)]
                           , num + 1 )
                  where getBitAsAtom :: ByteString -> Maybe Int -> atomType
                        getBitAsAtom v (Just i) = getBits v Vector.! i
                        getBitAsAtom v Nothing  = mustBeOneV (getBits v) $"expecting a single bit, but got the word "++unpack v
                        getBits :: ByteString -> Vector.Vector atomType
                        getBits bs = fmap fst (fst (getBits' toBoolean (fatal 287 "Undefined open wire in getBits for atomType")
                                                             (localWireDeclarations :: GetBitsType atomType (m boolType))
                                                             bs))
  declareStatements :: [(VerilogWireType, VerilogWireSize, ByteString, Maybe ByteString)]
  declareStatements = [(a,b,c,d) | (VerilogDeclare a b c d) <- statements]
  perName = Map.fromListWith (++) [(c,[a]) | (VerilogDeclare a _ c _) <- statements, a/=Input]
  onlyInput v = null (Map.findWithDefault [] v perName)
  localWireDeclarations :: (BooleanXZ boolType, AtomToBoolean ByteString (m boolType), m~(BooleanMonad boolType))
   => GetBitsType atomType (m boolType)
  localWireDeclarations
      = Map.fromListWith (fatalDuplicates "fromListWith (wire declarations) 378")
          [ case sz of
              SizeBit -> (idt, (Vector.fromList [ (toBoolean idt, toBoolean idt) ], Nothing))
              (SizeWord a b) -> (idt, (Vector.fromList$ drop (min a b) (zip (getUniqueVariants idt (abs (a - b) + 1))
                                                                            (getUniqueVariants idt (abs (a - b) + 1))
                                                                       ), Just$ a>=b))
          | (_, sz, idt, _) <- declareStatements ]
  buildMap :: Monad m
           => Map.Map (ByteString, Maybe Int) (atomType, ([m boolType],[INSTREF]))
           ->        ((ByteString, Maybe Int),(atomType, ([  boolType],[INSTREF])))
           ->(Map.Map (ByteString, Maybe Int) (atomType, ([m boolType],[INSTREF])))
  buildMap mp (k,(a,(bs,ir))) = Map.insertWith appendBool k (a,(fmap return bs,ir)) mp
   where appendBool (at,(bl1,i1)) (_,(bl2,i2)) = (at,(bl1++bl2,i1++i2))
  combineVals :: (BooleanXZ boolType, m ~ (BooleanMonad boolType))
            => (atomType, ([m boolType],[( Int, (ByteString, Int))])) -> m (atomType, WireValue boolType)
  combineVals (a,(lst,l)) = (,) a <$> (WV <$> (combineListC =<< sequenceA lst) <*> pure l)
  seqMapItm :: (BooleanXZ boolType)
            =>                          ( Vector.Vector ( atomType, (BooleanMonad boolType) boolType ), Maybe Bool)
            -> (BooleanMonad boolType) ( Vector.Vector ( atomType, (BooleanMonad boolType) boolType ), Maybe Bool)
  seqMapItm = traverseMapItm (fmap return)
  traverseMapItm :: forall f a b. (Applicative f)
                 => (a -> f b)
                 ->   (Vector.Vector (atomType, a), Maybe Bool)
                 -> f (Vector.Vector (atomType, b), Maybe Bool)
  traverseMapItm f ~(v,b) = flip (,) b <$> traverse fPair v
                          where fPair :: (atomType, a) -> f (atomType, b) -- in the case of f :: a->a
                                fPair ~(a,b') = (,) a <$> f b'

mustBeOneV :: Vector.Vector a -> String -> a
mustBeOneV = mustBeOne . Vector.toList

-- | functions for getting the right bit from GetBitsType
-- getBit2 yields the atomtype and the booltype of a single bit
getBit2 :: forall a boolType. (GetBitsType a boolType) -> ByteString -> Maybe Int -> (a, boolType)
getBit2 getBits v (Just i) = (fst (getBits' (fatal 360 "getting open wire atom") (fatal 358 "getting open wire bool") getBits v) Vector.! i)
getBit2 getBits v Nothing  = mustBeOneV (fst$ getBits' (fatal 361 "getting open wire atom") (fatal 359 "getting open wire bool") getBits v) $"expecting a single bit, but got the word "++unpack v

-- getBools' is a version of getBits' without the atomtype
getBools' :: forall a b. (ByteString -> b) -> GetBitsType a (b) -> ByteString -> (Vector.Vector (b), Maybe Bool)
getBools' openHack bits idt
 = (Vector.map snd lst,b)
 where (lst,b)=getBits' (const undefined) openHack bits idt
-- getBits' is the most primitive lookup function.
-- Since "Open123" is a wire name in some designs, we allow this value even when it is not in the GetBitsType lookup list.
getBits' :: forall a boolType. (ByteString -> a) -> (ByteString -> boolType) -> (GetBitsType a (boolType)) -> ByteString -> (Vector.Vector (a,boolType), Maybe Bool)
getBits' openHackA openHackB getBits idt
 = case Map.lookup idt getBits of
     Just ~(x,v) -> (x,v)
     Nothing -> case unpack idt of -- note: unfortunately, open wires are translated as undeclared wires sometimes!
                  ('O':'p':'e':'n':'_':_) -> (Vector.fromList [ (openHackA idt, openHackB idt) ], Nothing)
                  _ -> fatal 175 ("Referenced a wire which is not declared: "++unpack idt++"\n"++concat ["  "++unpack k++"\n" | k<-Map.keys getBits])
