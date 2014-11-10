module Options where

import System.Console.GetOpt
import System.Environment
import System.Exit

data Options = Options { optBackendCons :: String
                       , optBackendLifting :: String
                       , optBackendDomain :: String
                       , optBackendBase :: String
                       , optBackendInit :: String
                       , optBackendInterp :: String
                       , optEncoding :: Encoding
                       , optOptimizeTR :: Bool
                       , optFunction :: String
                       , optShowHelp :: Bool
                       , optTimeout :: Maybe Int
                       , optVerbosity :: Int
                       , optStats :: Bool
                       , optDumpModule :: Bool
                       }

data Encoding = Monolithic
              | BlockWise
              | TRGen

defaultOptions :: Options
defaultOptions = Options { optBackendCons = z3
                         , optBackendLifting = z3
                         , optBackendDomain = z3
                         , optBackendBase = z3
                         , optBackendInit = z3
                         , optBackendInterp = mathsat
                         , optOptimizeTR = False
                         , optEncoding = Monolithic
                         , optFunction = "main"
                         , optShowHelp = False
                         , optTimeout = Nothing
                         , optVerbosity = 0
                         , optStats = False
                         , optDumpModule = False
                         }
  where
    z3 = "z3 -smt2 -in"
    mathsat = "mathsat"

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
                            }) "name")
     "Choose an encoding for the transition relation:\n  monolithic - Translate the whole program graph into one step (default)\n  blockwise - Each LLVM block is its own step\n  trgen - Use the original CTIGAR encoding"
    ,Option [] ["backend-cons"]
     (ReqArg (\b opt -> opt { optBackendCons = b }) "cmd")
     "The SMT solver used for consecution calls [default: z3]"
    ,Option [] ["backend-lifting"]
     (ReqArg (\b opt -> opt { optBackendLifting = b }) "cmd")
     "The SMT solver used for lifting calls [default: z3]"
    ,Option [] ["backend-domain"]
     (ReqArg (\b opt -> opt { optBackendDomain = b }) "cmd")
     "The SMT solver used for abstraction calls [default: z3]"
    ,Option [] ["backend-base"]
     (ReqArg (\b opt -> opt { optBackendBase = b }) "cmd")
     "The SMT solver used for base case feasibility [default: z3]"
    ,Option [] ["backend-init"]
     (ReqArg (\b opt -> opt { optBackendInit = b }) "cmd")
     "The SMT solver used for initiation checks [default: z3]"
    ,Option [] ["backend-interp"]
     (ReqArg (\b opt -> opt { optBackendInterp = b }) "cmd")
     "The SMT solver used for interpolation [default: mathsat]"
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
             ]
    ) allOpts
  exitWith ExitSuccess
