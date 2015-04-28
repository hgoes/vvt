module Main where

import Realization.Lisp
import Realization.Lisp.Predicates

import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO

data Options = Options { addKarrPredicates :: Bool
                       , addIneqPredicates :: Bool
                       , addBoolPredicates :: Bool
                       , optShowHelp :: Bool
                       }

defaultOptions :: Options
defaultOptions = Options { addKarrPredicates = False
                         , addIneqPredicates = True
                         , addBoolPredicates = True
                         , optShowHelp = False }

allOpts :: [OptDescr (Options -> Options)]
allOpts
  = [Option ['h'] ["help"] (NoArg $ \opt -> opt { optShowHelp = True })
     "Shows this documentation"
    ,Option ['k'] ["karr"] (OptArg (\arg opt -> case arg of
                                     Nothing -> opt { addKarrPredicates = True }
                                     Just "on" -> opt { addKarrPredicates = True }
                                     Just "off" -> opt { addKarrPredicates = False }) "on|off")
     "Karr linear predicates"
    ,Option ['i'] ["ineq"] (OptArg (\arg opt -> case arg of
                                     Nothing -> opt { addIneqPredicates = True }
                                     Just "on" -> opt { addIneqPredicates = True }
                                     Just "off" -> opt { addIneqPredicates = False }) "on|off")
     "Inequality predicates"
    ,Option ['b'] ["bool"] (OptArg (\arg opt -> case arg of
                                                 Nothing -> opt { addBoolPredicates = True }
                                                 Just "on" -> opt { addBoolPredicates = True }
                                                 Just "off" -> opt { addBoolPredicates = False }) "on|off")
     "Boolean predicates"]

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
    (unlines ["USAGE: vvt-predicates < <file>"
             ,"       where <file> is a transition relation in lisp format."
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
     prog <- fmap parseLispProgram (readLispFile stdin)
     let lins = Set.toList $ linearStates prog
         ineqs = ineqPredicates lins
         prog1 = if addIneqPredicates opts
                 then prog { programPredicates = ineqs++programPredicates prog }
                 else prog
         prog2 = if addBoolPredicates opts
                 then prog1 { programPredicates = boolStates prog++programPredicates prog1
                            }
                 else prog1
     print $ programToLisp prog2
