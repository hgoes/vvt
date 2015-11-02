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
import Language.SMTLib2.DatatypeEmulator
import PartialArgs
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans (liftIO)
import qualified Data.Text as T

data Options = Options { showHelp :: Bool
                       , solver :: String
                       , solverArgs :: [String]
                       , bmcDepth :: Maybe Integer
                       , incremental :: Bool
                       , debug :: Bool }

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , solver = "z3"
                         , solverArgs = ["-in","-smt2"]
                         , bmcDepth = Just 10
                         , incremental = False
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
           ,Option [] ["debug"] (NoArg $ \opt -> opt { debug = True }) "Output the SMT stream"]

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
             prog <- fmap parseLispProgram $ readLispFile stdin
             pipe <- createSMTPipe (solver opts) (solverArgs opts)
             let act = do
                   st0 <- createStateVars "" prog
                   inp0 <- createInputVars "" prog
                   assert $ initialState prog st0
                   bmc prog (incremental opts) (bmcDepth opts) 0 st0 inp0 []
             res <- if debug opts
                    then (withSMTBackend ({-emulateDataTypes $-} namedDebugBackend "bmc" $ pipe) act)
                    else (withSMTBackend ({-emulateDataTypes-} pipe) act)
             case res of
              Nothing -> putStrLn "No bug found."
              Just bug -> do
                pbug <- mapM (\st -> renderPartialState prog
                                     (unmaskValue (undefined::State LispProgram) st)
                             ) bug
                putStrLn $ "Bug found:"
                mapM_ putStrLn pbug)
  where
    bmc :: LispProgram -> Bool -> Maybe Integer -> Integer
        -> Map T.Text LispValue -> Map T.Text LispValue
        -> [(Map T.Text LispValue,SMTExpr Bool)]
        -> SMT (Maybe [Map T.Text (LispStruct LispUValue)])
    bmc prog inc (Just l) n st inp sts
      | n>=l = do
          if inc
            then assert $ not' $ snd $ head sts
            else assert $ app or' $ fmap (not'.snd) sts
          res <- checkSat
          if res
            then fmap Just $
                 mapM (\(st,_) -> unliftArgs st getValue
                      ) sts
            else return Nothing
    bmc prog inc l n st inp sts = do
      assert $ stateInvariant prog inp st
      (assumps,gts1) <- declareAssumptions prog st inp Map.empty
      mapM_ assert assumps
      (asserts,gts2) <- declareAssertions prog st inp gts1
      res <- if inc
             then stack $ do
               liftIO $ putStrLn $ "Level "++show n
               assert $ app or' $ fmap not' asserts
               r <- checkSat
               if r
                 then (do
                          vals <- mapM (\st -> unliftArgs st getValue
                                       ) (st:(fmap fst sts))
                          return $ Just vals)
                 else return Nothing
             else return Nothing
      case res of
       Just bug -> return $ Just bug
       Nothing -> do
         (nxt,gts3) <- declareNextState prog st inp Nothing gts2
         ninp <- createInputVars "" prog
         bmc prog inc l (n+1) nxt ninp ((st,app and' asserts):sts)

               
