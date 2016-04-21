module Main where

import Realization
import Realization.Lisp
import Realization.Lisp.Value
import System.IO
import System.Console.GetOpt hiding (NoArg)
import qualified System.Console.GetOpt as Opt
import System.Environment
import Language.SMTLib2
import Language.SMTLib2.Debug
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Interface
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Embed
import Args
import PartialArgs
import Control.Monad.Trans (MonadIO,liftIO)
import Data.Proxy
--import Data.GADT.Show
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
optDescr = [Option ['h'] ["help"] (Opt.NoArg $ \opt -> opt { showHelp = True }
                                  ) "Show this help"
           ,Option ['d'] ["depth"] (Opt.ReqArg (\str opt -> opt { bmcDepth = case read str of
                                                                  -1 -> Nothing
                                                                  n -> Just n }) "n"
                                   ) "The BMC depth (-1 means no limit)"
           ,Option ['s'] ["solver"] (Opt.ReqArg (\str opt -> let solv:args = words str
                                                             in opt { solver = solv
                                                                    , solverArgs = args }) "bin"
                                    ) "The SMT solver executable"
           ,Option ['i'] ["incremental"] (Opt.NoArg $ \opt -> opt { incremental = True }
                                         ) "Run in incremental mode"
           ,Option ['c'] ["completeness"] (Opt.NoArg $ \opt -> opt { completeness = True }
                                          ) "Check completeness"
           ,Option ['t'] ["timing"] (Opt.NoArg $ \opt -> opt { timing = True }
                                    ) "Output timing information"
           ,Option [] ["timeout"] (Opt.ReqArg (\str opt -> opt { timeout = Just $ parseTime str
                                                               }) "time"
                                  ) "Abort the solver after a specified timeout"
           ,Option [] ["debug"] (Opt.NoArg $ \opt -> opt { debug = True }
                                ) "Output the SMT stream"]

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
             prog <- fmap parseProgram $ readLispFile stdin
             let pipe = createPipe (solver opts) (solverArgs opts)
             --let pipe = z3Solver
             let act :: forall b. (Backend b,MonadIO (B.SMTMonad b))
                     => SMT b (Either Bool [(Unpacked (State LispProgram),Unpacked (Input LispProgram))])
                 act = do
                   st0 <- createState prog
                   inp0 <- createInput prog
                   init <- initialState prog st0
                   assert init
                   bmc prog (completeness opts) (incremental opts) (bmcDepth opts)
                     0 startTime st0 inp0 []
                 act' = if debug opts
                        then withBackend (fmap (namedDebugBackend "bmc") pipe) act
                        else withBackend pipe act
             res <- case timeout opts of
               Nothing -> act'
               Just to -> do
                 mainThread <- myThreadId
                 timeoutThread <- forkOS (threadDelay to >> throwTo mainThread (ExitFailure (-2)))
                 catch act' (\ex -> case ex of
                              ExitFailure _ -> return (Left False))
             case startTime of
               Just startTime' -> do
                 endTime <- getCurrentTime
                 putStrLn $ "Total runtime: "++show (diffUTCTime endTime startTime')
               Nothing -> return ()
             case res of
              Left compl -> putStrLn $ "No bug found ("++
                            (if compl then "Complete" else "Incomplete")++")"
              Right bug -> do
                mapM_ (\(st,inp) -> do
                          putStrLn $ showsPrec 0 st ""
                          putStrLn $ showsPrec 0 inp ""
                      ) (reverse bug))
  where
    bmc :: (TransitionRelation t,Backend b,MonadIO (B.SMTMonad b))
        => t -> Bool -> Bool -> Maybe Integer -> Integer
        -> Maybe UTCTime
        -> State t (B.Expr b) -> Input t (B.Expr b)
        -> [(State t (B.Expr b),Input t (B.Expr b),B.Expr b BoolType)]
        -> SMT b (Either Bool [(Unpacked (State t),Unpacked (Input t))])
    bmc prog compl inc (Just l) n startTime st inp sts
      | n>=l = do
          if compl
            then push
            else return ()
          if inc
            then let (_,_,prop) = head sts in assert $ not' prop
            else assert $ not' (or' $ fmap (\(_,_,prop) -> prop) sts)
          res <- checkSat
          case res of
            Sat -> do
              bug <- mapM (\(st,inp,_) -> do
                              rst <- unliftComp getValue st
                              rinp <- unliftComp getValue inp
                              return (rst,rinp)
                          ) sts
              if compl
                then pop
                else return ()
              return $ Right bug
            Unsat -> if compl
                     then do
                       pop
                       isCompl <- checkCompleteness prog st
                       return (Left isCompl)
                     else return (Left False)
    bmc prog compl inc l n startTime st inp sts = do
      invar <- stateInvariant prog st inp
      assert invar
      let gts0 = startingProgress prog
      (assumps,gts1) <- declareAssumptions
                        (\name e -> case name of
                            Nothing -> defineVar e
                            Just name' -> defineVarNamed name' e)
                        prog st inp gts0
      mapM_ assert assumps
      (asserts,gts2) <- declareAssertions
                        (\name e -> case name of
                            Nothing -> defineVar e
                            Just name' -> defineVarNamed name' e)
                        prog st inp gts1
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
               negProp <- not' $ and' asserts
               assert negProp
               r <- checkSat
               case r of
                 Sat -> do
                          vals <- mapM (\(st,inp,prop) -> do
                                           rst <- unliftComp getValue st
                                           rinp <- unliftComp getValue inp
                                           return (rst,rinp)
                                       ) ((st,inp,negProp):sts)
                          pop
                          return $ Right vals
                 Unsat -> do
                   pop
                   isComplete <- checkCompleteness prog st
                   return (Left isComplete)
             else return (Left False)
      case res of
       Right bug -> return $ Right bug
       Left True -> return $ Left True
       Left False -> do
         (nxt,gts3) <- declareNextState
                       (\name e -> case name of
                           Nothing -> defineVar e
                           Just name' -> defineVarNamed name' e)
                       prog st inp gts2
         ninp <- declareComposite declareVarNamed (inputAnnotation prog)
         if compl
           then do
           noProgress <- eqComposite st nxt
           progress <- not' noProgress
           assert progress
           else return ()
         conjAss <- and' asserts
         bmc prog compl inc l (n+1) startTime nxt ninp ((st,inp,conjAss):sts)

    checkCompleteness prog st = stack $ do
      end <- isEndState prog st
      not' end >>= assert
      res <- checkSat
      return $ res==Unsat
