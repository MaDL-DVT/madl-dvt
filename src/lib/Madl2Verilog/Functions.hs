{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

{-|
Module      : Madl2Verilog.Function
Description : Conversion of madl functions to verilog.
Copyright   : (c) Tessa Belder 2015-2016

Contains functions to transform madl functions to verilog code.
-}
module Madl2Verilog.Functions (
    declareFunctionComponent,
    declareFunctions, createBFunction
) where

-- import Debug.Trace

import qualified Data.HashMap as Hash
import qualified Data.IntMap as IM
import Data.List (intersect)
import Data.Maybe (mapMaybe)
import qualified Data.Text as T

import Utils.Map
import Utils.Text
import Utils.Tuple

import Madl.MsgTypes hiding (VArguments)

import Madl2Verilog.VerilogConstants
import Madl2Verilog.VerilogGen
import Madl2Verilog.Component

-- Error function
fileName :: Text
fileName = "Madl2Verilog.Functions"

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

-- | Declare function component
declareFunctionComponent :: Bool -> Maybe Int -> ComponentInfo -> VerilogCode
declareFunctionComponent useInterface mtype comp = declareModule useInterface functionModule where
    functionModule = VModule {
        vmoduleName = funModuleName,
        vmoduleParams = [],
        vmoduleHasTime = hasTimeFromInfo comp,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface',
        vmoduleBody =
               assignWire (esc . vTrdy useInterface $ vFunInputPort 0) (esc $ vTrdy useInterface vFunOutputPort)
            ++ assignWire (esc $ vIrdy useInterface vFunOutputPort) (esc . vIrdy useInterface $ vFunInputPort 0)
            ++ commentHeader "Function logic" (
                functionvariables
                ++ [""]
                ++ function
            )
    }

    funModuleName = vType mtype $ vFunction (T.intercalate "_" $ compIdentifier comp)

    vmoduleInterface' = [inputPort, outputPort]
    inputPort = VInterfacePort (Just MInput) (Right . Just . Data . Left $ encodingSize inputType) (vFunInputPort 0)
    outputPort = VInterfacePort (Just MOutput) (Right . Just . Data . Left $ encodingSize outputType) vFunOutputPort
    [inputType] = compInputTypes comp
    [outputType] = compOutputTypes comp

    functionvariables = case madlFunction of
        Left f -> createFunction vTopFunctionName (f component) inargs outEncoding
        Right f -> createBFunction vTopFunctionName (f component) inargs
    madlFunction = case outputFunctions (1, component, 1) of
        [] -> fatal 71 "Component must have an outputfunction"
        [f] -> f
        _ -> fatal 72 "Component must have at most one outputfunction"
    inargs = IM.singleton 0 (inputType, (esc . vData useInterface $ vFunInputPort 0, Nothing))
    (TE outEncoding) = typeEncoding outputType
    component = compComponent comp

    function = assignWire (esc $ vData useInterface vFunOutputPort) (esc vTopFunctionName)

-- | Declare all functions for a component
declareFunctions :: Bool -> Maybe Int -> ComponentInfo -> VerilogCode
declareFunctions useInterface mtype comp = concatMap declareFunction $ functionInputPorts (nrInChannels, compComponent comp, nrOutChannels) where
    nrInChannels = length $ compInputTypes comp
    nrOutChannels = length $ compOutputTypes comp
    declareFunction = declareOutputFunction useInterface mtype comp

-------------------------------------
-- Function generation --
-------------------------------------

-- | Declare function
declareOutputFunction :: Bool -> Maybe Int -> ComponentInfo -> VFPort -> VerilogCode
declareOutputFunction useInterface mtype comp vfport@(_, findex, oport) = declareModule useInterface outputFunModule where
    outputFunModule = VModule {
        vmoduleName = traceShowId' "Output Function" 99 funModuleName,
        vmoduleParams = [],
        vmoduleHasTime = hasTimeFunction,
        vmoduleHasRst = True,
        vmoduleInterface = vmoduleInterface',
        vmoduleBody = commentHeader "Function logic" (
               functionvariables
            ++ [""]
            ++ function
            )
    }
    funModuleName = vType mtype $ vFunModule vfport (T.intercalate "_" $ compIdentifier comp)

    vmoduleInterface' = inputports ++ [outputport]
    inputports =
        map (\(i, t) -> VInterfacePort (Just MInput) (Right . Just . Function . Left $ encodingSize t) (vFunInputPort i) ) (zip [0..] (compInputTypes comp)) ++
        mapMaybe (\(i, (n, t)) -> if i == findex then Just $ VInterfacePort (Just MInput) (Left . fmap Left $ wireSize t) n else Nothing) (functionOutputPorts (nrInputs, component, nrOutputs))
    outputport = VInterfacePort (Just MOutput) (Right . Just . Function . Left $ encodingSize outputType) vFunOutputPort
    outputType = case oport of
        Output i -> lookupM (src 198) i $ compOutputTypes comp
        Selection cs -> cs
    nrInputs = length $ compInputTypes comp
    nrOutputs = length $ compOutputTypes comp
    component = compComponent comp

    functionvariables = case madlFunction of
        Left f -> createFunction vTopFunctionName (f component) inargs outEncoding
        Right f -> createBFunction vTopFunctionName (f component) inargs
    madlFunction = lookupMnoShow (src 50) findex $ outputFunctions (nrInputs, component, nrOutputs)
    inargs = IM.fromList (
        [(i, (itype, (esc . vData useInterface $ vFunInputPort i, Nothing))) | (i, itype) <- zip [0..] (compInputTypes comp)] ++
        zip [nrInputs..] [(itype, (esc name, Nothing)) | (j, (name, itype)) <- functionOutputPorts (nrInputs, component, nrOutputs), j == findex]
        )
    (TE outEncoding) = typeEncoding outputType

    function = assignWire (esc outputname) (esc vTopFunctionName)
    outputname = if useInterface then vData True vFunOutputPort else vFunOutputPort

type VArguments = IntMap (ColorSet, (Text, Maybe Range))
tokenParam :: (Text, Int) -> Text
-- tokenParam loc = trace ("token: " ++ show loc) $ T.cons '`' (fst3 vToken +++ showT loc) -- Uncomment for debugging
tokenParam _ = T.cons '`' $ fst3 vToken

traceShowId' :: Show a => String -> Int -> a -> a
-- traceShowId' name loc obj= trace (name ++" " ++show loc ++": " ++show obj) obj -- Uncomment for debugging
traceShowId' _ _ obj = obj

traceShowEnc :: Show a => Int -> a -> a
traceShowEnc = traceShowId' "Enc"

traceShowFun :: Show a => Int -> a -> a
traceShowFun = traceShowId' "Fun"

createBFunction :: Text -> MFunctionBool -> VArguments -> VerilogCode
createBFunction name f args = case traceShowFun 151 f of
    XCompare op x y -> snd argumentX ++ snd argumentY
        ++ declareWire name assignment where
        (argumentX, argumentY) = get2Arguments $ getArguments name [x, y] args
        assignment = T.unwords [fst argumentX, operator, fst argumentY]
        operator = case op of
            Eq -> "=="
            Gt -> ">"
    XMatch x y -> argumentX ++ argumentY
        ++ declareWire name assignment where
        (TE xEnc) = typeEncoding $ resultingTypeStrict (IM.map fst args) x
        (TE yEnc) = typeEncoding $ resultingTypeStrict (IM.map fst args) y
        argumentX = createFunction xName x args xEnc
        argumentY = createFunction yName y args yEnc
        assignment = case (Hash.keys xEnc, Hash.keys yEnc) of
            ([], _) -> vlog_number 1 0
            (_, []) -> vlog_number 1 0
            ([xKey], [yKey]) -> vlog_number 1 (if xKey == yKey then 1 else 0)
            ([xKey], _) -> case Hash.lookup xKey yEnc of
                Nothing -> vlog_number 1 0
                Just ((v, r, _, _)::DisjType) -> vlog_equals (esc yName +++ declareRange (src 275) r) (vlog_number (rSize r) v)
            (_, [yKey]) -> case Hash.lookup yKey xEnc of
                Nothing -> vlog_number 1 0
                Just ((v, r, _, _)::DisjType) -> vlog_equals (esc xName +++ declareRange (src 276) r) (vlog_number (rSize r) v)
            _ -> if null crossKeys then vlog_number 1 0 else vlog_or $ map compareValues crossKeys where
                    compareValues (xV, xR, yV, yR) = vlog_and[
                        vlog_equals (esc xName +++ declareRange (src 277) xR) (vlog_number (rSize xR) xV),
                        vlog_equals (esc yName +++ declareRange (src 278) yR) (vlog_number (rSize yR) yV)]
        crossKeys = Hash.elems $ Hash.intersectionWith (\(xV, xR, _, _) (yV, yR, _, _) -> (xV, xR, yV, yR)) xEnc yEnc
        xName = name >. "arg0"
        yName = name >. "arg1"
    XTrue -> declareWire name (vlog_number 1 1)
    XFalse -> declareWire name (vlog_number 1 0)
    XUnOpBool op x -> snd argument ++ declareWire name assignment where
        argument = head $ getArgumentsB name [x] args
        assignment = operator +++ fst argument
        operator = case op of Not -> "!";
    XBinOpBool op x y -> snd argumentX ++ snd argumentY ++ declareWire name assignment where
        (argumentX, argumentY) = get2Arguments $ getArgumentsB name [x, y] args
        assignment = T.unwords [fst argumentX, operator, fst argumentY]
        operator = case op of Or -> "||"; And -> "&&";
    XAppliedToB f' gs -> if any emptyColorSet $ map (resultingTypeStrict $ IM.map fst args) gs
        then declareWire name (vlog_number 1 0)
        else arguments ++ createBFunction fname f' args' ++ declareWire name (esc fname) where
        fname = name >. "f"
        (arguments, args') = foldr calcArg ([], IM.empty) (zip [0..] gs)
        calcArg :: (Int, MFunctionDisj) -> (VerilogCode, VArguments) -> (VerilogCode, VArguments)
        calcArg (i, g) (vcode, arg) = (vcode', arg') where
            vcode' = vcode ++ createFunction gname g args gEnc
            arg' = IM.insert i (gType, (esc gname, Nothing)) arg
            gname = name >. "g" +++ showT i
            gType = resultingTypeStrict (IM.map fst args) g
            (TE gEnc) = typeEncoding gType
    XSelectB d smap
        | Hash.size smap < 2 -> fatal 143 "Select should have at least 2 choices"
        | otherwise -> disjvalue ++ choices ++
        declareWire name (contentFunction +++ vlog_number 1 0) where

        disj = resultingTypeStrict (IM.map fst args) d
        (TE dmap) = typeEncoding disj
        disjvalue = createFunction disjname d args dmap
        disjname = name >. "sel"

        choices = concatMap (uncurry declareChoice) (Hash.assocs smap)
        declareChoice :: Text -> MFunctionBool -> VerilogCode
        declareChoice key f' = if Hash.member key dmap then createBFunction dataname f' args' else [] where
                dataname = name >. key
                args'= case d of XVar i -> IM.adjust (uncurry editArgument) i args; _ -> args;

                editArgument :: ColorSet -> (Text, Maybe Range) -> (ColorSet, (Text, Maybe Range))
                editArgument cs (n, r) = (cs', (n, r')) where
                    cs' = makeColorSet [(key, lookupM (src 299) key cs)]
                    (TE csmap) = typeEncoding cs
                    r' = case choiceRangeSize csmap of 0 -> r; _ -> Just $ intersectRange (contentRange csmap) r

        contentFunction = concatMapT calcFunction (Hash.keys smap)

        calcFunction :: Text -> Text
        calcFunction key = if not $ Hash.member key dmap then "" else
            ifThen matchesKey dataname where
            matchesKey = T.unwords [esc disjname, declareRange (src 307) r, "==", vlog_number (rSize r) i]
            dataname = esc (name >. key)
            (i, r, _, _)::DisjType = lookupM (src 309) key dmap
    XIfThenElseB bool true false -> createBFunction (name >. "bool") bool args
         ++ createBFunction (name >. "true") true args ++ createBFunction (name >. "false") false args
         ++ declareWire name (vlog_ite (esc $ name >. "bool") (esc $ name >. "true") (esc $ name >. "false"))

createVFunction :: Text -> MFunctionVal -> VArguments -> Range -> VerilogCode
createVFunction name f args outEnc = case traceShowFun 239 f of
    XConst c -> if rSize (traceShowEnc 234 outEnc) == 0
        then fatal 71 "Bitvector size cannot be 0"
        else declareRangedWire (src 225) outEnc name $ vlog_number (rSize outEnc) c
    XUnOp op x -> if rSize (traceShowEnc 237 outEnc) == 0
        then fatal 74 "Bitvector size cannot be 0"
        else snd argument ++ declareRangedWire (src 228) outEnc name assignment where
        argument = head $ getArguments name [x] args
        assignment = operator +++ fst argument
        operator = case op of Neg -> "~";
    XBinOp op x y -> if rSize (traceShowEnc 243 outEnc) == 0
        then fatal 82 "Bitvector size cannot be 0"
        else snd argumentX ++ snd argumentY
            ++ declareRangedWire (src 237) outEnc name assignment where
        (argumentX, argumentY) = get2Arguments $ getArguments name [x, y] args
        assignment = T.unwords [fst argumentX, operator, fst argumentY]
        operator = case op of Plus -> "+"; Minus -> "-"; Mult -> "*"; Mod -> "%";
    XChooseVal val d -> if rSize (traceShowEnc 250 outEnc) == 0
            then fatal 287 "Bitvector size cannot be 0"
            else if rSize r /= rSize outEnc then fatal 336 "outEncoding does not correspond to disjEncoding"
            else disjvalue ++ declareRangedWire (src 288) outEnc name fieldvalue where
            disj = resultingTypeStrict (IM.map fst args) d
            (TE dmap) = typeEncoding disj
            (_, _, _, r)::DisjType = lookupM (src 291) val dmap
            disjvalue = createFunction disjname d args dmap
            fieldvalue = esc disjname +++ declareRange (src 294) r
            disjname = name >. "disj"
    XGetFieldVal val c -> if rSize (traceShowEnc 260 outEnc) == 0
            then fatal 296 "Bitvector size cannot be 0"
            else if rSize r /= rSize outEnc then fatal 345 "outEncoding does not correspond to conjEncoding"
            else conjvalue ++ declareRangedWire (src 297) outEnc name fieldvalue where
            conj = resultingTypeStrict (IM.map fst args) c
            cmap = fst $ conjEncoding 0 conj
            (r, _)::ConjType = lookupM (src 300) val cmap

            conjvalue = createCFunction conjname c args cmap
            fieldvalue = esc conjname +++ declareRange (src 303) r
            conjname = name >. "conj"
    XIfThenElseV bool true false -> if rSize (traceShowEnc 271 outEnc) == 0
            then fatal 296 "Bitvector size cannot be 0"
            else createBFunction (name >. "bool") bool args
                ++ createVFunction (name >. "true") true args outEnc
                ++ createVFunction (name >. "false") false args outEnc
                ++ declareRangedWire (src 356) outEnc name (
                        vlog_ite (esc $ name >. "bool") (esc $ name >. "true") (esc $ name >. "false"))

createCFunction :: Text -> MFunctionStruct -> VArguments -> ConjMap -> VerilogCode
createCFunction name f args outEnc = case traceShowFun 286 f of
    XConcat valmap -> if conjRangeSize (traceShowEnc 281 outEnc) == 0
            then declareWire name (tokenParam $ src 279)
            else declareEmptyRangedWire (src 245) (conjRange outEnc) name ++ disjvalues where
            disjvalues = Hash.foldWithKey calcValue [] valmap

            calcValue :: Text -> OrMFVal MFunctionDisj -> VerilogCode -> VerilogCode
            calcValue val (Left f') = (++) $ if rSize r == 0 then []
                else createFunction disj f' args dmap
                ++ assignRangedWire (src 251) r name (esc disj) where
                disj = name >. val
                (r, TE dmap) = lookupM (src 100) val outEnc
            calcValue val (Right f') = (++) $ if rSize r == 0 then []
                else createVFunction disj f' args r
                ++ assignRangedWire (src 321) r name (esc disj) where
                disj = name >. val
                (r, _)::ConjType = lookupM (src 323) val outEnc
    XChooseStruct val d -> if conjRangeSize (traceShowEnc 297 outEnc) == 0
            then declareWire name (tokenParam $ src 295)
            else if rSize r /= conjRangeSize outEnc then fatal 376 "outEncoding does not correspond to disjEncoding"
            else disjvalue ++ declareRangedWire (src 257) (conjRange outEnc) name fieldvalue where
            disj = resultingTypeStrict (IM.map fst args) d
            (TE dmap) = typeEncoding disj
            (_, _, _, r)::DisjType = lookupM (src 107) val dmap

            disjvalue = createFunction disjname d args dmap
            fieldvalue = esc disjname +++ declareRange (src 263) r
            disjname = name >. "disj"
    XIfThenElseC{} -> fatal 305 "unimplemented"

createFunction :: Text -> MFunctionDisj -> VArguments -> DisjMap -> VerilogCode
createFunction name f args outEnc = case traceShowFun 317 f of
    XChoice val c
        | choiceRangeSize (traceShowEnc 313 outEnc) > 0 && contentRangeSize outEnc > 0 ->
               conjvalue
            ++ declareEmptyRangedWire (src 285) (disjRange outEnc) name
            ++ assignRangedWire (src 286) (choiceRange outEnc) name choice
            ++ assignRangedWire (src 287) (contentRange outEnc) name (esc conj)
        | choiceRangeSize outEnc > 0 ->
            declareRangedWire (src 289) (choiceRange outEnc) name choice
        | contentRangeSize outEnc > 0 ->
            conjvalue ++ declareRangedWire (src 291) (contentRange outEnc) name (esc conj)
        | otherwise -> declareWire name (tokenParam $ src 319) where
            conjvalue = case c of Left c' -> createCFunction conj c' args cmap; Right c' -> createVFunction conj c' args bvrange
            (i, crange, cmap, bvrange)::DisjType = lookupM (src 139) val outEnc
            choice = vlog_number (rSize crange) i
            conj = name >. "content"
    XIfThenElseD bool true false -> if disjRangeSize (traceShowEnc 327 outEnc) == 0 then declareWire name (tokenParam $ src 324)
        else
            createBFunction (name >. "bool") bool args
         ++ createFunction (name >. "true") true args trueEnc
         ++ createFunction (name >. "false") false args falseEnc
         ++ (if trueEnc == outEnc then [] else toEncoding (name >. "true'") ((esc $ name >. "true", Nothing), TE trueEnc) (TE outEnc))
         ++ (if falseEnc == outEnc then [] else toEncoding (name >. "false'") ((esc $ name >. "false", Nothing), TE falseEnc) (TE outEnc))
         ++ declareRangedWire (src 356) (disjRange outEnc) name contentFunction where
            (TE trueEnc) = typeEncoding $ resultingTypeStrict (IM.map fst args) true
            (TE falseEnc) = typeEncoding $ resultingTypeStrict (IM.map fst args) false
            contentFunction = vlog_ite  (esc $ name >. "bool")
                                        (esc $ name >. if trueEnc == outEnc then "true" else "true'")
                                        (esc $ name >. if falseEnc == outEnc then "false" else "false'")
    XSelect d smap
        | Hash.size smap < 2 -> fatal 143 "Select should have at least 2 choices"
        | disjRangeSize (traceShowEnc 342 outEnc) == 0 -> declareWire name (tokenParam $ src 339)
        | otherwise -> disjvalue ++ choices ++
        if choiceRangeSize outEnc > 0 && contentRangeSize outEnc > 0 then
        declareEmptyRangedWire (src 302) (disjRange outEnc) name ++
        assignRangedWire (src 303) (choiceRange outEnc) name (choiceFunction +++ vlog_number 1 0) ++
        assignRangedWire (src 304) (contentRange outEnc) name (contentFunction +++ vlog_number 1 0) else
        if choiceRangeSize outEnc > 0 then
        declareRangedWire (src 306) (choiceRange outEnc) name (choiceFunction +++ vlog_number 1 0)
        else declareRangedWire (src 307) (contentRange outEnc) name (contentFunction +++ vlog_number 1 0) where

        disj = resultingTypeStrict (IM.map fst args) d
        (TE dmap) = typeEncoding disj
        disjvalue = createFunction disjname d args dmap
        disjname = name >. "sel"

        choices = concatMap (uncurry declareChoice) (Hash.assocs smap)
        declareChoice :: Text -> MFunctionDisj -> VerilogCode
        declareChoice key f' =
            (if choiceRangeSize choiceEnc > 0 || contentRangeSize outEnc > 0 then
            createFunction dataname f' args' choiceEnc else [])
            ++ (if choiceRangeSize outEnc > 0 then
             declareRangedWire (src 320) (choiceRange outEnc) choicename value else []) where
                dataname = name >. key >. "data"
                args'= case d of XVar i -> IM.adjust (uncurry editArgument) i args; _ -> args;

                editArgument :: ColorSet -> (Text, Maybe Range) -> (ColorSet, (Text, Maybe Range))
                editArgument cs (n, r) = (cs', (n, r')) where
                    cs' = makeColorSet [(key, lookupM (src 400) key cs)]
                    (TE csmap) = typeEncoding cs
                    r' = case choiceRangeSize csmap of 0 -> r; _ -> Just $ intersectRange (contentRange csmap) r

                choicename = name >. key
                choiceType = resultingTypeStrict (IM.map fst args') f'
                (TE choiceEnc) = typeEncoding choiceType

                value = if choiceRangeSize choiceEnc == 0 then vlog_number (rSize valRange) val  -- Type is always the same
                        else (concatMapT checkForMatch (Hash.assocs choiceEnc)) +++ vlog_number 1 0
                (val, valRange, _, _)::DisjType = lookupM (src 181) (head $ Hash.keys choiceEnc) outEnc

                checkForMatch :: (Text, DisjType) -> Text
                checkForMatch (k, (j, r, _, _)) = ifThen matchesKey (vlog_number (rSize choicevalRange) choiceval) where
                    matchesKey = T.unwords [esc dataname, declareRange (src 342) r, "==", vlog_number (rSize r) j]
                    (choiceval, choicevalRange, _, _)::DisjType = lookupM (src 186) k outEnc

        (choiceFunction, contentFunction) = tmap T.concat $ unzip $ map calcFunction (Hash.keys smap)

        calcFunction :: Text -> (Text, Text)
        calcFunction key = tmap (ifThen matchesKey) (choicename, dataname) where
            matchesKey = T.unwords [esc disjname, declareRange (src 352) r, "==", vlog_number (rSize r) i]
            choicename = esc (name >. key)
            dataname = esc (name >. key >. "data")
            (i, r, _, _)::DisjType = lookupM (src 367) key dmap

    XGetFieldDisj val c -> if disjRangeSize (traceShowEnc 395 outEnc) == 0
            then declareWire name (tokenParam $ src 393)
            else if rSize r /= disjRangeSize outEnc then fatal 476 "outEncoding does not correspond to conjEncoding"
            else conjvalue ++ declareRangedWire (src 359) (disjRange outEnc) name fieldvalue where
            conj = resultingTypeStrict (IM.map fst args) c
            cmap = fst $ conjEncoding 0 conj
            (r, _)::ConjType = lookupM (src 205) val cmap

            conjvalue = createCFunction conjname c args cmap
            fieldvalue = esc conjname +++ declareRange (src 365) r
            conjname = name >. "conj"

    XAppliedTo f' gs -> if disjRangeSize (traceShowEnc 407 outEnc) == 0
        then declareWire name (tokenParam $ src 405)
        else if any emptyColorSet $ map (resultingTypeStrict $ IM.map fst args) gs
            then declareRangedWire (src 491) (disjRange outEnc) name (vlog_number (disjRangeSize outEnc) 0)
            else arguments
            ++ createFunction fname f' args' outEnc
            ++ declareRangedWire (src 372) (disjRange outEnc) name (esc fname)
        where
            fname = name >. "f"

            (arguments, args') = foldr calcArg ([], IM.empty) (zip [0..] gs)
            calcArg :: (Int, MFunctionDisj) -> (VerilogCode, VArguments) -> (VerilogCode, VArguments)
            calcArg (i, g) (vcode, arg) = (vcode', arg') where
                vcode' = vcode ++ createFunction gname g args gEnc
                arg' = IM.insert i (gType, (esc gname, Nothing)) arg
                gname = name >. "g" +++ showT i
                gType = resultingTypeStrict (IM.map fst args) g
                (TE gEnc) = typeEncoding gType

    XVar i -> case IM.lookup i args of
        Nothing -> fatal 228 "Unknown variable"
        Just (t, (v, r)) -> case disjRangeSize (traceShowEnc 428 outEnc) of
            0 -> declareWire name (tokenParam $ src 426)
            s -> if traceShowEnc 438 inEnc == (TE outEnc)
                 then declareRangedWire (src 389) (0, s) name
                    (case r of
                        Nothing -> v
                        Just r' -> v +++ declareRange (src 400) r')
                 else toEncoding name ((v, r), inEnc) (TE outEnc) where
                    inEnc = typeEncoding t
    XInput _ -> fatal 379 "unimplemented"

-- | Convert the value from a wire with a certain typeencoding to a different typeencoding
toEncoding :: Text -> ((Text, Maybe Range), TypeEncoding) -> TypeEncoding  -> VerilogCode
toEncoding name ((inWire, irange), (TE inEnc)) (TE outEnc) = if disjRangeSize (traceShowEnc 440 outEnc) == 0
    then declareWire name (tokenParam $ src 438)
    else if choiceRangeSize outEnc > 0 && contentRangeSize outEnc > 0 then
            declareEmptyRangedWire (src 401) (disjRange outEnc) name ++
            assignRangedWire (src 402) (choiceRange outEnc) name (choiceFunction $ rSize (choiceRange outEnc)) ++
            content True else
            if choiceRangeSize outEnc > 0 then
            declareRangedWire (src 405) (choiceRange outEnc) name (choiceFunction $ rSize (choiceRange outEnc))
            else content False where
    crossKeys = intersect (Hash.keys inEnc) (Hash.keys outEnc)
    content assign = let
        z :: Text -> Text -> Bool -> VerilogCode
        z key name' assign' =
            if null outConj && assign'
                 then assignRangedWire (src 413) (contentRange outEnc) name'
                    (if rSize inRange == 0 then tokenParam (src 542) else inWire +++ declareRange (src 414) (intersectRange inRange irange))
            else if null outConj
                then declareRangedWire (src 415) (contentRange outEnc) name'
                    (if rSize inRange == 0 then tokenParam (src 455) else inWire +++ declareRange (src 416) (intersectRange inRange irange))
            else if assign'
                then concatMap assignField $ Hash.keys outConj
            else declareEmptyRangedWire (src 418) (contentRange outEnc) name'
                ++ concatMap assignField (Hash.keys outConj) where
            (_, _, inConj, inRange)::DisjType = lookupM (src 425) key inEnc
            (_, _, outConj, _)::DisjType = lookupM (src 428) key outEnc
            assignField :: Text -> VerilogCode
            assignField k = if rSize oRange == 0 then []
                else if Hash.null oE then assignRangedWire (src 473) oRange name' (inWire +++ declareRange (src 414) bitvecRange)
                else toEncoding (name' >. k) ((inWire, irange), inEnc') outEnc'
                     ++ assignRangedWire (src 426) oRange name' (esc $ name' >. k) where
                    bitvecRange = intersectRange (0, rSize oRange) . Just $ intersectRange iRange irange
                    (oRange, outEnc'@(TE oE))::ConjType = lookupM (src 435) k outConj
                    (iRange, inEnc')::ConjType = lookupM (src 437) k inConj in
        case crossKeys of
        [] -> if assign
            then assignRangedWire (src 432) (contentRange outEnc) name (tokenParam $ src 470)
            else declareRangedWire (src 433) (contentRange outEnc) name (tokenParam $ src 471)
        [key] -> z key name assign
        ks ->  concat (map (\k -> z k (name >. k) False) ks)
            ++ if assign
                then assignRangedWire (src 452) (contentRange outEnc) name contents
                else declareRangedWire (src 453) (contentRange outEnc) name contents where
            contents = concatMapT y ks +++ vlog_number 1 0
            y :: Text -> Text
            y key = ifThen isInKey (esc $ name >. key) where
                (inValue, inRange, _, _)::DisjType = lookupM (src 449) key inEnc
                isInKey = vlog_equals (inWire +++ declareRange (src 440) inRange) (vlog_number (rSize inRange) inValue)

    choiceFunction outsize = case crossKeys of
        [] -> tokenParam (src 484)
        [key] -> vlog_number (rSize outValueRange) outValue where
            (outValue, outValueRange, _, _)::DisjType = lookupM (src 456) key outEnc
        ks -> concatMapT y ks +++ vlog_number 1 0 where
            y :: Text -> Text
            y key = ifThen isInKey (vlog_number outsize outValue) where
                (outValue, _, _, _)::DisjType = lookupM (src 461) key outEnc
                (inValue, inRange, _, _)::DisjType = lookupM (src 470) key inEnc
                isInKey = vlog_equals (inWire +++ declareRange (src 450) inRange) (vlog_number (rSize inRange) inValue)

-------------------------
-- Auxiliary functions --
-------------------------

-- | Calculate arguments for functions using one or more bitvector arguments
getArguments :: Text -> [MFunctionVal] -> VArguments -> [(Text, VerilogCode)]
getArguments name arguments args = zipWith (curry calcArgument) [0..] arguments where
    calcArgument :: (Int, MFunctionVal) -> (Text, VerilogCode)
    calcArgument (i, x) = (esc argname, code) where
        argname = name >. "arg" +++ showT i
        code = createVFunction argname x args (0, h)
        h = bvSize $ resultingTypeStrict (IM.map fst args) x

-- | Calculate arguments for functions using one or more bitvector arguments
getArgumentsB :: Text -> [MFunctionBool] -> VArguments -> [(Text, VerilogCode)]
getArgumentsB name arguments args = zipWith (curry calcArgument) [0..] arguments where
    calcArgument :: (Int, MFunctionBool) -> (Text, VerilogCode)
    calcArgument (i, x) = (esc argname, code) where
        argname = name >. "arg" +++ showT i
        code = createBFunction argname x args

-- | Convenience function for the case of 2 arguments
get2Arguments :: [(Text, VerilogCode)] -> ((Text, VerilogCode), (Text, VerilogCode))
get2Arguments (arg0:arg1:_arguments) = (arg0, arg1)
get2Arguments _ = fatal 558 "Less than 2 arguments present."