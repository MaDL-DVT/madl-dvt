{-# LANGUAGE ScopedTypeVariables#-}
module Main(main) where

import System.Environment
import Madl2fsm.Madl2fsm
import Utils.File
import qualified Data.ByteString.Char8 as B

main :: IO ()
main = do
  args <- getArgs
  if ((length args) /= 2)
    then error "Wrong arguments"
    else return ()
  parsed <- readColoredNetworkFromFile defaultReadOptions $ head args
  let (sizeConst::Int) = (read $ args !! 1) :: Int
  network <- case parsed of
    Left err -> error err
    Right net -> return net
  B.putStrLn (sizeGen sizeConst)
  putStrLn "\n\n"
  B.putStrLn (typedefGen sizeConst network)
  putStrLn "\n\n"
  putStrLn
    (qFunGen sizeConst network ++ "\n" ++
    "\nmodule fsm_checker(\n" ++
    interfaceGen network ++ "\n);\n" ++ 
    localParamGen network ++ "\n\n" ++
    hasElemGen network ++ "\n\n" ++
    updQueueGen network ++ "\n\n" ++
    updGen network ++ "\n\n" ++
    checkIslsGen network ++ "\n\n")
  B.putStrLn (getLegalConfsGen sizeConst network)
  putStrLn "\n\n"
  putStrLn
    (checkActGen sizeConst network ++ "\n\n" ++
    varGen network ++ "\n\n" ++
    mainGen sizeConst network ++ "\n\n" ++
    "endmodule")

