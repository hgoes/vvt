module Options where

import System.Console.GetOpt
import System.Environment
import System.Exit

data Options = Options { optBackendCons :: String
                       , optBackendDomain :: String
                       , optBackendBase :: String
                       , optBackendInit :: String
                       , optBackendInterp :: String
                       , optFunction :: String
                       , optShowHelp :: Bool
                       }

defaultOptions :: Options
defaultOptions = Options { optBackendCons = z3
                         , optBackendDomain = z3
                         , optBackendBase = z3
                         , optBackendInit = z3
                         , optBackendInterp = mathsat
                         , optFunction = "main"
                         , optShowHelp = False
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
    ,Option [] ["backend-cons"]
     (ReqArg (\b opt -> opt { optBackendCons = b }) "cmd")
     "The SMT solver used for consecution calls [default: z3]"
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
    ]

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
