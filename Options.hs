module Options where

import BackendOptions

import System.Console.GetOpt
import System.Environment
import System.Exit
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

data Options = Options { optBackends :: BackendOptions
                       , optEncoding :: Encoding
                       , optOptimizeTR :: Bool
                       , optFunction :: String
                       , optShowHelp :: Bool
                       , optTimeout :: Maybe Int
                       , optVerbosity :: Int
                       , optStats :: Bool
                       , optDumpModule :: Bool
                       , optKarr :: Bool
                       , optExtraPredicates :: Maybe String
                       }

data Encoding = Monolithic
              | BlockWise
              | TRGen
              | Lisp
              | Threaded

defaultOptions :: Options
defaultOptions = Options { optBackends = defaultBackendOptions
                         , optOptimizeTR = False
                         , optEncoding = Monolithic
                         , optFunction = "main"
                         , optShowHelp = False
                         , optTimeout = Nothing
                         , optVerbosity = 0
                         , optStats = False
                         , optDumpModule = False
                         , optKarr = True
                         , optExtraPredicates = Nothing
                         }

allOpts :: [OptDescr (Options -> Options)]
allOpts
  = [Option ['h'] ["help"] (NoArg $ \opt -> opt { optShowHelp = True })
     "Shows this documentation"
    ,Option ['e'] ["entry"]
     (ReqArg (\e opt -> opt { optFunction = e }) "function")
     "The entry function of the program"
    ,Option ['E'] ["encoding"]
     (ReqArg (\e opt -> opt { optEncoding = case e of
                               "monolithic" -> Monolithic
                               "blockwise" -> BlockWise
                               "trgen" -> TRGen
                               "lisp" -> Lisp
                               "threaded" -> Threaded
                            }) "name")
     "Choose an encoding for the transition relation:\n  monolithic - Translate the whole program graph into one step (default)\n  blockwise - Each LLVM block is its own step\n  trgen - Use the original CTIGAR encoding"
    ,Option [] ["backend"]
     (ReqArg (\b opt -> case readsPrec 0 b of
               [(backend,':':solver)]
                 -> opt { optBackends = setBackend backend (read solver) (optBackends opt)
                        }) "<backend>:<solver>")
     "The SMT solver used for the specified backend."
    ,Option [] ["debug-backend"]
     (ReqArg (\b opt -> case readsPrec 0 b of
               [(backend,[])]
                 -> opt { optBackends = setDebugBackend backend (optBackends opt)
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
    ,Option ['O'] ["optimize"] (NoArg $ \opt -> opt { optOptimizeTR = True })
     "Optimize the transition relation"
    ,Option [] ["no-karr"] (NoArg $ \opt -> opt { optKarr = False }) "Disable the Karr analysis"
    ,Option [] ["predicates"] (ReqArg (\str opt -> opt { optExtraPredicates = Just str }) "file")
     "Read extra predicates from a file"
    ,Option ['s'] ["stats"] (NoArg $ \opt -> opt { optStats = True })
     "Print statistical information"
    ,Option [] ["dump-module"] (NoArg $ \opt -> opt { optDumpModule = True })
     "Dump the LLVM module"
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

readOptions :: IO (Either [String] (String,Options))
readOptions = do
  args <- getArgs
  let (opts,rargs,errs) = getOpt Permute allOpts args
      ropts = foldl (flip id) defaultOptions opts
  if optShowHelp ropts
    then showHelp
    else (case errs of
           [] -> case rargs of
             [] -> return (Left ["Please provide an LLVM bitcode file"])
             [bc] -> return (Right (bc,ropts))
             _ -> return (Left ["Please provide only one LLVM bitcode file"])
           _ -> return (Left errs))

showHelp :: IO a
showHelp = do
  putStrLn $
    usageInfo
    (unlines ["USAGE: hctigar <file>"
             ,"       where <file> is an LLVM bitcode file."
             ,""
             ,"  <backend> can be \"cons\", \"lifting\", \"domain\", \"init\" or \"interp\"."
             ,"  <solver> can be:"
             ,"    pipe:EXEC [ARG...] - An executable with arguments that uses the SMTLib2 specification."
#ifdef NATIVE_Z3
             ,"    Z3 - Native Z3 C-API."
#endif
             ]
    ) allOpts
  exitWith ExitSuccess
