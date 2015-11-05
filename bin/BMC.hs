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

data Options = Options { showHelp :: Bool
                       , solver :: String
                       , solverArgs :: [String]
                       , bmcDepth :: Maybe Integer
                       , incremental :: Bool
                       , completeness :: Bool
                       , debug :: Bool }

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , solver = "z3"
                         , solverArgs = ["-in","-smt2"]
                         , bmcDepth = Just 10
                         , incremental = False
                         , completeness = False
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
                   bmc prog (completeness opts) (incremental opts) (bmcDepth opts) 0 st0 inp0 []
             res <- if debug opts
                    then (withSMTBackend ({-emulateDataTypes $-} namedDebugBackend "bmc" $ pipe) act)
                    else (withSMTBackend ({-emulateDataTypes-} pipe) act)
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
        -> Map T.Text LispValue -> Map T.Text LispValue
        -> [(Map T.Text LispValue,SMTExpr Bool)]
        -> SMT (Either Bool [Map T.Text (LispStruct LispUValue)])
    bmc prog compl inc (Just l) n st inp sts
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
                   isCompl <- checkCompleteness prog st
                   return (Left isCompl)
                 else return $ Left False
    bmc prog compl inc l n st inp sts = do
      assert $ stateInvariant prog inp st
      (assumps,gts1) <- declareAssumptions prog st inp Map.empty
      mapM_ assert assumps
      (asserts,gts2) <- declareAssertions prog st inp gts1
      res <- if inc
             then do
               push
               liftIO $ putStrLn $ "Level "++show n
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
         bmc prog compl inc l (n+1) nxt ninp ((st,app and' asserts):sts)
 
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
