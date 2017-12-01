{-# OPTIONS_GHC -Wall -Werror -fwarn-tabs -fwarn-incomplete-uni-patterns -fwarn-incomplete-record-updates -fwarn-monomorphism-restriction -Wmissing-local-signatures #-}
{-# LANGUAGE Safe, OverloadedStrings,DeriveFoldable,DeriveTraversable,DeriveFunctor,NoImplicitPrelude #-}

{-|
Module      : CommonDataTypes.TraverseProps
Copyright   : (c) Sebastiaan J C Joosten
-}
module CommonDataTypes.TraverseProps
 ( InverseProp(..)
 , InverseProps(..)
 , Instantiation(..)
 , VerilogPort(..)
 , PortStatement(..)
 , PortProperty(..)
 , PortDescription(..)
 , appendProps
 , findQueues
 )
 where
import qualified Data.Map as Map (Map)
import BaseLike.CustomPrelude
import CommonDataTypes.Syntax

-- | properties with easy traversing:
data InverseProp b = InverseProp ByteString     -- type of annotation, e.g. "queue"
                                 (Map.Map ByteString Int) -- arguments
                                 [ByteString]   -- instance name (may be a list due to nesting)
                                 [ ( ByteString -- property name
                                   , [Int]      -- arguments
                                   , [b]        -- boolean value
                                   )
                                 ]
                   deriving (Foldable, Functor, Traversable)
-- | TODO
newtype InverseProps b = InverseProps [InverseProp b] deriving (Foldable, Functor, Traversable)

-- | TODO
appendProps :: InverseProps b -> InverseProps b -> InverseProps b
appendProps (InverseProps lst1) (InverseProps lst2) = (InverseProps (lst1 ++ lst2))

-- | TODO
findQueues :: InverseProps t -> [([ByteString], [([Int],(t,[t]))], [([Int],(t,[t]))])]
findQueues (InverseProps lst)
  = [ ( strs
      , [(idf,(b, matchData "inputData"  idf lst')) | (nm,idf,[b]) <- lst', nm == "inputTransfer" || nm=="increase"]
      , [(idf,(b, matchData "outputData" idf lst')) | (nm,idf,[b]) <- lst', nm == "outputTransfer"|| nm=="decrease"])
    | (InverseProp nm' _ strs lst') <- lst
    , nm' == "queue"]
  where matchData :: ByteString -> [Int] -> [(ByteString, [Int], [t])] -> [t]
        matchData nm idf lst'
         = concat [bs | (nm',idf',bs) <- lst', nm==nm', idf==idf']
