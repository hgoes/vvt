module Main where

import Realization
import Realization.Lisp
import Realization.Lisp.Value
import System.IO
import System.Console.GetOpt
import System.Environment
import Language.SMTLib2.Pipe
import Language.SMTLib2
import Language.SMTLib2.Debug
import PartialArgs
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans (liftIO)
import qualified Data.Text as T
import qualified Data.AttoLisp as L
import Data.Typeable (gcast)
import Data.Time.Clock
import Control.Concurrent
import Control.Exception (catch)
import System.Exit

data Options = Options { showHelp :: Bool
                       , solver :: String
                       , solverArgs :: [String]
                       , bmcDepth :: Maybe Integer
                       , incremental :: Bool
                       , completeness :: Bool
                       , timing :: Bool
                       , timeout :: Maybe Int
                       , debug :: Bool }

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , solver = "z3"
                         , solverArgs = ["-in","-smt2"]
                         , bmcDepth = Just 10
                         , incremental = False
                         , completeness = False
                         , timing = False
                         , timeout = Nothing
                         , debug = False }

optDescr :: [OptDescr (Options -> Options)]
optDescr = [Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True }) "Show this help"
           ,Option ['d'] ["depth"] (ReqArg (\str opt -> opt { bmcDepth = case read str of
                                                                -1 -> Nothing
                                                                n -> Just n }) "n") "The BMC depth (-1 means no limit)"
           ,Option ['s'] ["solver"] (ReqArg (\str opt -> let solv:args = words str
                                                         in opt { solver = solv
                                                                , solverArgs = args }) "bin") "The SMT solver executable"
           ,Option ['i'] ["incremental"] (NoArg $ \opt -> opt { incremental = True }) "Run in incremental mode"
           ,Option ['c'] ["completeness"] (NoArg $ \opt -> opt { completeness = True }) "Check completeness"
           ,Option ['t'] ["timing"] (NoArg $ \opt -> opt { timing = True }) "Output timing information"
           ,Option [] ["timeout"] (ReqArg (\str opt -> opt { timeout = Just $ parseTime str
                                                           }) "time") "Abort the solver after a specified timeout"
           ,Option [] ["debug"] (NoArg $ \opt -> opt { debug = True }) "Output the SMT stream"]

parseTime :: String -> Int
parseTime str = parseNumber 0 0 str
  where
    parseNumber ful cur [] = ful+1000000*cur
    parseNumber ful cur ('0':rest) = parseNumber ful (cur*10) rest
    parseNumber ful cur ('1':rest) = parseNumber ful (cur*10+1) rest
    parseNumber ful cur ('2':rest) = parseNumber ful (cur*10+2) rest
    parseNumber ful cur ('3':rest) = parseNumber ful (cur*10+3) rest
    parseNumber ful cur ('4':rest) = parseNumber ful (cur*10+4) rest
    parseNumber ful cur ('5':rest) = parseNumber ful (cur*10+5) rest
    parseNumber ful cur ('6':rest) = parseNumber ful (cur*10+6) rest
    parseNumber ful cur ('7':rest) = parseNumber ful (cur*10+7) rest
    parseNumber ful cur ('8':rest) = parseNumber ful (cur*10+8) rest
    parseNumber ful cur ('9':rest) = parseNumber ful (cur*10+9) rest
    parseNumber ful cur ('s':rest) = parseNumber (ful+1000000*cur) 0 rest
    parseNumber ful cur ('m':rest) = parseNumber (ful+60000000*cur) 0 rest
    parseNumber ful cur ('h':rest) = parseNumber (ful+3600000000*cur) 0 rest

main = do
  args <- getArgs
  let (xs,extra,errs) = getOpt Permute optDescr args
  case extra of
   [] -> return ()
   _ -> error $ "Unknown arguments: "++show extra
  case errs of
   [] -> return ()
   _ -> error $ "Error while parsing arguments: "++unlines errs
  let opts = foldl (flip id) defaultOptions xs
  if showHelp opts
    then putStrLn $ usageInfo "Usage:\n\n    vvt-bmc [OPTIONS]\n\nAvailable options:" optDescr
    else (do
             startTime <- if timing opts
                          then fmap Just getCurrentTime
                          else return Nothing
             prog <- fmap parseLispProgram $ readLispFile stdin
             pipe <- createSMTPipe (solver opts) (solverArgs opts)
             let act = do
                   st0 <- createStateVars "" prog
                   inp0 <- createInputVars "" prog
                   assert $ initialState prog st0
                   bmc prog (completeness opts) (incremental opts) (bmcDepth opts)
                     0 startTime st0 inp0 []
                 act' = if debug opts
                        then (withSMTBackend (namedDebugBackend "bmc" pipe) act)
                        else (withSMTBackend pipe act)
             res <- case timeout opts of
               Nothing -> act'
               Just to -> do
                 mainThread <- myThreadId
                 timeoutThread <- forkOS (threadDelay to >> throwTo mainThread (ExitFailure (-2)))
                 catch act' (\ex -> case ex of
                              ExitFailure _ -> return (Left False))
             case startTime of
               Nothing -> return ()
               Just time -> do
                 time' <- getCurrentTime
                 putStrLn $ "Total runtime: "++show (diffUTCTime time' time)
             case res of
              Left compl -> putStrLn $ "No bug found ("++
                            (if compl then "Complete" else "Incomplete")++")"
              Right bug -> do
                pbug <- mapM (\st -> renderPartialState prog
                                     (unmaskValue (undefined::State LispProgram) st)
                             ) bug
                putStrLn $ "Bug found:"
                mapM_ putStrLn pbug)
  where
    bmc :: LispProgram -> Bool -> Bool -> Maybe Integer -> Integer
        -> Maybe UTCTime
        -> Map T.Text LispValue -> Map T.Text LispValue
        -> [(Map T.Text LispValue,SMTExpr Bool)]
        -> SMT (Either Bool [Map T.Text (LispStruct LispUValue)])
    bmc prog compl inc (Just l) n startTime st inp sts
      | n>=l = do
          if compl
            then push
            else return ()
          if inc
            then assert $ not' $ snd $ head sts
            else assert $ app or' $ fmap (not'.snd) sts
          res <- checkSat
          if res
            then do
            bug <- mapM (\(st,_) -> unliftArgs st getValue
                        ) sts
            if compl
              then pop
              else return ()
            return $ Right bug
            else if compl
                 then do
                   pop
                   isCompl <- checkCompleteness prog st
                   return (Left isCompl)
                 else return $ Left False
    bmc prog compl inc l n startTime st inp sts = do
      assert $ stateInvariant prog inp st
      (assumps,gts1) <- declareAssumptions prog st inp Map.empty
      mapM_ assert assumps
      (asserts,gts2) <- declareAssertions prog st inp gts1
      res <- if inc
             then do
               push
               diff <- case startTime of
                 Nothing -> return Nothing
                 Just time -> liftIO $ do
                   time' <- getCurrentTime
                   return $ Just $ diffUTCTime time' time
               liftIO $ putStrLn $ "Level "++show n++(case diff of
                                                       Nothing -> ""
                                                       Just diff' -> "("++show diff'++")")
               assert $ app or' $ fmap not' asserts
               r <- checkSat
               if r
                 then (do
                          vals <- mapM (\st -> unliftArgs st getValue
                                       ) (st:(fmap fst sts))
                          pop
                          return $ Right vals)
                 else do
                 pop
                 isComplete <- checkCompleteness prog st
                 return (Left isComplete)
             else return (Left False)
      case res of
       Right bug -> return $ Right bug
       Left True -> return $ Left True
       Left False -> do
         (nxt,gts3) <- declareNextState prog st inp Nothing gts2
         ninp <- createInputVars "" prog
         if compl
           then assert $ app or' (Map.elems $ Map.intersectionWith
                                  (\x y -> not' $ valueEq x y)
                                  st nxt)
           else return ()
         bmc prog compl inc l (n+1) startTime nxt ninp ((st,app and' asserts):sts)
 
    checkCompleteness :: LispProgram -> Map T.Text LispValue -> SMT Bool
    checkCompleteness prog st = stack $ do
      let pcs = Map.filter (\(_,ann) -> case Map.lookup "pc" ann of
                             Just (L.Symbol "true") -> True
                             _ -> False
                           ) (programState prog)
          acts = Map.intersectionWith
                 (\_ val -> case value val of
                   Singleton (Val e) -> case gcast e of
                     Just b -> b) pcs st
      assert $ app or' $ Map.elems acts
      fmap not checkSat
