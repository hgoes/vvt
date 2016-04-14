module Main where

import BackendOptions
import Realization
import Realization.Lisp
import CTIGAR (check)
import PartialArgs

import System.Console.GetOpt
import System.Environment
import System.Exit
import Control.Concurrent
import Control.Exception
import System.IO
import Data.Proxy
import Control.Monad (when)

data Options = Options { optBackends :: BackendOptions
                       , optShowHelp :: Bool
                       , optTimeout :: Maybe Int
                       , optVerbosity :: Int
                       , optStats :: Bool
                       , optDumpDomain :: Maybe String
                       , optPrintFixpoint :: Bool
                       , optDumpStats :: Maybe String
                       , optDumpStates :: Maybe String
                       }

defaultOptions :: Options
defaultOptions = Options { optBackends = defaultBackendOptions
                         , optShowHelp = False
                         , optTimeout = Nothing
                         , optVerbosity = 0
                         , optStats = False
                         , optDumpDomain = Nothing
                         , optDumpStats = Nothing
                         , optDumpStates = Nothing
                         , optPrintFixpoint = False
                         }

allOpts :: [OptDescr (Options -> Options)]
allOpts
  = [Option ['h'] ["help"] (NoArg $ \opt -> opt { optShowHelp = True })
     "Shows this documentation"
    ,Option [] ["backend"]
     (ReqArg (\b opt -> case readsPrec 0 b of
               [(backend,':':solver)]
                 -> opt { optBackends = setBackend backend (read solver)
                                        (optBackends opt)
                        }) "<backend>:solver")
     "The SMT solver used for the specified backend."
    ,Option [] ["debug-backend"]
     (ReqArg (\b opt -> case [ x | (x,"") <- readBackendDebug b ] of
                 (tp,dbg):_
                   -> opt { optBackends = setDebugBackend tp dbg (optBackends opt)
                          }) "<backend>")
     "Output the communication with the specified backend solver."
    ,Option ['t'] ["timeout"]
     (ReqArg (\t opt -> opt { optTimeout = Just $ parseTime t }) "time")
     "Abort the solver after a specified timeout"
    ,Option ['v'] ["verbose"]
     (OptArg (\v opt -> case v of
               Nothing -> opt { optVerbosity = 1 }
               Just vs -> opt { optVerbosity = read vs }) "level")
     "How much debugging output to show"
    ,Option ['s'] ["stats"] (NoArg $ \opt -> opt { optStats = True })
     "Print statistical information"
    ,Option [] ["dump-domain"]
     (ReqArg (\file opt -> opt { optDumpDomain = Just file }) "file")
     "Dump the domain graph into a file."
    ,Option [] ["dump-stats-to"]
     (ReqArg (\file opt -> opt { optDumpStats = Just file }) "file")
     "Dump the stats that IC3 produces to a file."
    ,Option [] ["dump-states-to"]
     (ReqArg (\file opt -> opt { optDumpStates = Just file }) "file")
     "Dump the states that IC3 collects during refinement to a file. The states will be printed in csv format."
    ,Option [] ["print-fixpoint"]
     (NoArg $ \opt -> opt { optPrintFixpoint = True }) "If the program can be proven correct, output the fixpoint."
    ]

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

readOptions :: IO (Either [String] Options)
readOptions = do
  args <- getArgs
  let (opts,rargs,errs) = getOpt Permute allOpts args
      ropts = foldl (flip id) defaultOptions opts
  if optShowHelp ropts
    then showHelp
    else (case errs of
           [] -> case rargs of
             [] -> return $ Right ropts
             _ -> return (Left ["Unknown extra arguments: "++show rargs])
           _ -> return (Left errs))

showHelp :: IO a
showHelp = do
  putStrLn $
    usageInfo
    (unlines ["USAGE: vvt-verify < <file>"
             ,"       where <file> is a transition relation in lisp format."
             ,""
             ,"  <backend> can be \"cons\", \"lifting\", \"domain\", \"init\" or \"interp\"."
             ]
    ) allOpts
  exitWith ExitSuccess

main :: IO ()
main = do
  opts <- readOptions
  case opts of
   Left errs -> do
     mapM_ (hPutStrLn stderr) errs
     exitWith (ExitFailure (-1))
   Right opts -> do
     prog <- fmap parseProgram (readLispFile stdin)
     tr <- case optTimeout opts of
            Nothing -> check prog
                       (optBackends opts)
                       (optVerbosity opts)
                       (optStats opts)
                       (optDumpDomain opts)
                       (optDumpStats opts)
                       (optDumpStates opts)
            Just to -> do
              mainThread <- myThreadId
              timeoutThread <- forkOS (threadDelay to >> throwTo mainThread (ExitFailure (-2)))
              res <- catch (do
                               res <- check prog
                                      (optBackends opts)
                                      (optVerbosity opts)
                                      (optStats opts)
                                      (optDumpDomain opts)
                                      (optDumpStats opts)
                                      (optDumpStates opts)
                               killThread timeoutThread
                               return (Just res)
                           )
                     (\ex -> case ex of
                       ExitFailure _ -> return Nothing)
              case res of
               Just tr -> return tr
               Nothing -> do
                 hPutStrLn stderr "Timeout"
                 exitWith ExitSuccess
     case tr of
      Right fp -> do
        putStrLn "No bug found."
        when (optPrintFixpoint opts) $
          putStrLn $ "Fixpoint: "++show fp
      Left tr' -> do
        putStrLn "Bug found:"
        mapM_ (\(step,inp) -> do
                  putStr "State: "
                  putStrLn $ renderPartialState prog
                    (unmaskValue (getUndefState prog) step)
                  putStr "Input: "
                  putStrLn $ renderPartialInput prog
                    (unmaskValue (getUndefInput prog) inp)
              ) tr'

getUndefState :: TransitionRelation tr => tr -> Proxy (State tr)
getUndefState _ = Proxy

getUndefInput :: TransitionRelation tr => tr -> Proxy (Input tr)
getUndefInput _ = Proxy
