{-# LANGUAGE OverloadedStrings, DeriveGeneric, ScopedTypeVariables #-}

import qualified Data.Map as Map
import Data.List (find,isPrefixOf)
import Data.Aeson
import GHC.Generics
import Control.Monad.Trans.Either
import Control.Monad.Trans.Class
import Data.Maybe
import System.IO.Temp
import System.FilePath

-- This is awful...
import qualified Data.Text as Text
-- import qualified Data.ByteString as B
import Data.Text.Encoding (decodeUtf8) -- encodeUtf8
-- import qualified Data.ByteString.Lazy as BLL
import qualified Data.Text.Lazy as TL 
-- import qualified Data.ByteString.Char8 as B8 (putStrLn)
--import qualified Data.ByteString.Lazy.Char8 as BL8 (putStrLn)
import qualified Data.Text.Lazy.Encoding as BLE (decodeUtf8) -- encodeUtf8
-- import qualified Data.Text.Lazy.IO as TLIO


import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200,status404)

import Utils.Text

import Madl.Deadlock.Runner
import Madl.Network
import Madl.Cycles
import Madl.Invariants (Invariant,getInvariants,showInvariants2)
import qualified Parser.MadlAST as AST (Network)
import Parser.MadlParser (madlParser)
import Parser.IncludeStatement
import Parser.MadlTypeChecker
import Parser.ASTTranslator
import Madl.Deadlock.SMT (SMTModel)

import Text.Parsec.Char
import Text.ParserCombinators.Parsec

import Debug.Trace



{-
	Main:
	listen on port 8888 and run function app for request/responses
-}
main :: IO ()
main = do
    let port = 8888
    putStrLn $ "Listening on port " ++ show port
    run port app


{-
    The reply from the server.
    This datatype is converted to JSON and send back to the client
-}
data ServerReply = ServerReply {
    errorOccurred :: Bool,
    errorString :: String,
    fileParses :: Bool,
    fileTypeChecks :: Bool,
    hasDeadlock :: Bool,
    deadlock :: SMTModel,
    cTypes :: Map.Map String String
    } deriving (Generic, Show)
instance ToJSON ServerReply



-- Uses the function fileParses, fileTypeChecks etc. and thus prevents warnings
defaultServerReply :: ServerReply
defaultServerReply = ServerReply {errorOccurred = False, errorString = "", fileParses = False, fileTypeChecks = False, hasDeadlock = True, deadlock = Map.empty, cTypes = Map.empty}


{-
    The server application

    Usage (from xmas/madl/src/server):
        curl -X POST "localhost:8888/?main=vcwbn.madl" -F "madl=@../../examples/MaDL/vcwbn.madl" -F "madl=@../../examples/MaDL/prodcon_v00.madl" -H "Content-Type: multipart/form-data; charset=UTF-8"


    Deals with incoming HTTP POST requests.
    An example of the value of the incoming "Content-Type" is:
        "multipart/form-data; charset=UTF-8; boundary=------------------------07cefd39cfdc70e5"
    It stores the boundary which is used as a delimiter for the different files sent in the body of the request.
    An example of the queryString is:
        [("main",Just "vcwbn.madl")]
    The body contains several parts, i.e., it is a s multipart/form-data request.

    If the POST request can be parsed, then the incoming .madl files are processed.
    This either yields a ServerReply, indicating an error.
    Otherwise, this yields a network. The network is verified, which produces a ServerReply.
    The ServerReply is send.


    TODO: check whether content-type is multipart/form-data, whther content-disposition has name="madl"
    TODO: ensure SSL
-}

app :: Application
app req respond =  do
    if requestMethod req == "POST" then
        case requestBodyLength req of
            KnownLength _ ->
              do
                print req
                -- Get the body of the request
                body <- strictRequestBody req
                -- parse the multipart/form-data contents
                let contents = do
                                    contentType <- lookup "Content-Type" $ requestHeaders req
                                    boundary <- find_boundary $ TL.fromStrict $ decodeUtf8 contentType
                                    mainFile <- lookup "main" $ queryString req
                                    mainFileName <- mainFile
                                    parsedBody <- parseMultipartFormdataBody boundary $ BLE.decodeUtf8 body
                                    return (Text.unpack $ decodeUtf8 mainFileName, map (mapBoth TL.unpack) parsedBody)
                case contents of
                    Just (mainFile,madls) ->
                      do
                        mapM_ putStrLn (map snd madls)
                        -- The contents could be parsed from the request, so process it as a MaDL
                        reply_or_network <- processMadls mainFile madls
                        case reply_or_network of
                            Left reply -> do
                                print reply
                                respond $ responseLBS status200 [("Content-Type", "application/json")] $ encode reply
                            Right network -> do
                                reply <- verifyNetwork network
                                print reply
                                respond $ responseLBS status200 [("Content-Type", "application/json")] $ encode reply
                    _ -> respond $ responseLBS status404 [] ""
            _ -> respond $ responseLBS status404 [] "Sending data in chunks is not supported."
    else
        respond $ responseLBS status404 [] "Only POST reqeusts supported."
  where find_boundary contentType = case find (TL.isPrefixOf "boundary") $ map TL.strip $ TL.splitOn ";" $ contentType of
            Nothing -> Nothing
            Just boundary -> Just $ TL.intercalate "=" $ tail $ TL.splitOn "=" boundary


mapBoth :: (a -> b) -> (a,a) -> (b,b)
mapBoth f (x,y) = (f x, f y)

{-
See https://tools.ietf.org/html/rfc7578 for the speficiation of a multipart/form-data request
Also, it assumes the request ends with an additional "--".

From the spec:
The parts are delimited with a boundary delimiter, constructed using CRLF, "--", and the value of the "boundary" parameter.
Each part MUST contain a Content-Disposition header field, which in our case has the form:

    Content-Disposition: form-data; name="madl"; filename="vcwbn.madl"

Each part MAY have an (optional) "Content-Type" header field
The multipart/form-data media type does not support any MIME header fields in parts other than Content-Type, Content-Disposition, and (in limited circumstances) Content-Transfer-Encoding.

Returns the parse multipart/form-data body, i.e., a list with a parts as plain-text
-}
parseMultipartFormdataBody :: TL.Text -> TL.Text -> Maybe [(TL.Text, TL.Text)]
parseMultipartFormdataBody boundary body = do
    step1 <- TL.stripPrefix (TL.append "--" boundary) $ TL.strip $ body
    step2 <- TL.stripSuffix (TL.concat ["--", boundary, "--"]) $ step1
    step3 <- Just $ TL.splitOn (TL.append "--" boundary) step2
    step4 <- Just $ map TL.lines step3
    let filenames = map findFileNameInContentDisposition step4
    step5 <- Just $ map (TL.intercalate "\n" . stripHeaders) step4
    if traceShow step3 $ Nothing `elem` filenames then
        Nothing
    else
        Just $ zip (map fromJust filenames) step5
  where
    stripHeaders s = if isHeader $ head s then stripHeaders $ tail s else s
    isHeader h = isContentDisposition h ||
                 TL.isPrefixOf "Content-Type:" h ||
                 TL.isPrefixOf "Content-Transfer-Encoding:" h ||
                 TL.strip h == ""

    findFileNameInContentDisposition :: [TL.Text] -> Maybe TL.Text
    findFileNameInContentDisposition s =
        case find isContentDisposition s of
            Nothing -> Nothing
            Just cd -> case parse parseContentDisposition "" (TL.unpack cd) of
                        Left _ -> Nothing
                        Right s1 -> Just (TL.pack s1)
        
    isContentDisposition = TL.isPrefixOf "Content-Disposition: form-data;"


parseContentDisposition :: Parser String
parseContentDisposition = do
    _ <- manyTill anyChar (try $ string "filename")
    spaces
    _ <- char '='
    spaces
    quotedString
    

quotedString :: Parser String
quotedString = do
    _ <- char '"'
    x <- many (noneOf "\"")
    _ <- char '"'
    return x



{-
    Takes as input the file contents of the .madl files
    Tries to parse and typecheck. If this fails, it returns a ServerReply.
    Otherwise, it returns a network with colors.
-}
processMadls :: String -> [(String,String)] -> IO (Either ServerReply ColoredNetwork)
processMadls mainFile madls = withTempDirectory "." "temp." $ \tmpDir -> runEitherT $ do
    let reply = defaultServerReply
    lift $ putStrLn ("Starting processing MaDls in temp dir " ++ takeDirectory (tmpDir </> mainFile))

    lift $ mapM_ (storeMadlInDir tmpDir) madls 

    contents <- case lookup mainFile madls of
                    Nothing -> left $ reply{errorString = "Main file not found."}
                    Just contents -> right contents

    ast <- case madlParser "" contents of
        Left err -> left $ reply{errorString = show err} -- File does not parse
        Right ast -> right ast
    lift $ putStrLn "Input was succesfully parsed."
    astOrError <- lift $ removeIncludeStatements (tmpDir </> mainFile) ast
    ast' <- case astOrError of
        Left err -> left $ reply{fileParses = True, errorString = err, errorOccurred = True} -- Error during flattening
        Right ast' -> right ast'
    ast'' <- case typecheckNetwork ast' of
        Left err -> left $ reply{fileParses = True, errorString = showError err, errorOccurred = True} -- Typechecking failed
        Right ast'' -> right $ makeNetwork ast''
    lift $ putStrLn "Input was succesfully typechecked."
    right ast''
  where
    makeNetwork = colorNetwork . flattenNetwork . makeMadLNetwork

    makeMadLNetwork :: AST.Network -> MadlNetwork
    makeMadLNetwork network = net where
        (NSpecSrc spec _) = translateNetwork network
        net = mkNetwork spec

    flattenNetwork :: MadlNetwork -> FlattenedNetwork
    flattenNetwork net = unflatten (unfoldMacros net :: FlatFlattenedNetwork)

    colorNetwork :: FlattenedNetwork -> ColoredNetwork
    colorNetwork = channelTypes


storeMadlInDir :: FilePath -> (String,String) -> IO()
storeMadlInDir dir (filename,contents) = do
    writeFile (dir </> filename) contents
    putStrLn $ "Written file: " ++ dir </> filename








-- TODO: see what options are relevant
verifyNetwork :: ColoredNetwork -> IO ServerReply
verifyNetwork network = do
    let reply = defaultServerReply{fileParses = True, fileTypeChecks = True}
    -- SMT only, since we need a SMT model 
    let options = Madl.Deadlock.Runner.defaultOptions{argRunMode = SmtOnly}

    -- Cycle check
    _ <- cycleCheck network
    -- Generate invariants
    invs <- generateInvariants network
    -- Queues that are never full
    nfqs <- neverFullQueues network options invs
    -- Deadlock Detection
    dl <- deadlockDetection network options invs nfqs
    case dl of
        Left err -> return $ reply{errorString = err, errorOccurred = True, cTypes = createChannelTypeMap network}
        Right (b,Nothing) -> return $ reply {hasDeadlock = b, cTypes = createChannelTypeMap network}
        Right (b,Just model) -> do
            return $ reply {hasDeadlock = b, deadlock = Map.mapKeys removeQPrefix $ Map.filterWithKey isSMTQueueVar model, cTypes = createChannelTypeMap network}


createChannelTypeMap :: ColoredNetwork -> Map.Map String String --Map.Map (XChannel Text) Madl.MsgTypes.ColorSet
createChannelTypeMap network =  Map.map (removeSetColorPrefix . show) $ Map.mapKeys (Text.unpack . channelName) $  Map.fromDistinctAscList (getChannels network)


removeSetColorPrefix :: String -> String
removeSetColorPrefix = drop 10

isSMTQueueVar :: String -> Int -> Bool
isSMTQueueVar var _ = isPrefixOf "Q___" var

removeQPrefix :: String -> String
removeQPrefix = drop 4 

cycleCheck :: ColoredNetwork -> IO Int
cycleCheck network = do
    let cycles = checkCycles $ removeColors network
    let num_cycles = length cycles
    putStrLn $ "The network contains " ++ show num_cycles ++ " cycles."
    return num_cycles

generateInvariants :: ColoredNetwork -> IO [Invariant Int]
generateInvariants network = do
    let invs = getInvariants network
    putStrLn $ "Found " ++ show (length invs) ++ " invariants."
    putStrLn $ "Invariants: \n"
    putStrLn $ utxt (showInvariants2 invs network)
    return invs

neverFullQueues :: ColoredNetwork -> CommandLineOptions -> [Invariant Int] -> IO [ComponentID]
neverFullQueues network options invs = do
    putStrLn $ "Computing never full queues ..."
    nfqs <- notFullQueues network (argSMTSolver options) invs
    putStrLn $ "Found " ++ show (length nfqs) ++ " queues that are never full."
    putStrLn ("Never full queues are: " ++ show nfqs)
    return nfqs

deadlockDetection :: ColoredNetwork -> CommandLineOptions -> [Invariant Int] ->[ComponentID] -> IO (Either String (Bool,Maybe SMTModel))
deadlockDetection network options invs nfqs = do
    putStrLn $ "Running deadlock detection."
    -- Run deadlock detection using the options specified by the user
    result <- runDeadlockDetection network options invs nfqs
    -- Handle the result of the deadlock detection
    return result


