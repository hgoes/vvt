{-# LANGUAGE ViewPatterns #-}
module Main where

import Realization.Lisp
import Realization.Lisp.Simplify.Dataflow
import Realization.Lisp.Simplify.Inliner
import Realization.Lisp.Simplify.ExprSimplify
import Realization.Lisp.Simplify.ValueSet
import Realization.Lisp.Simplify.Slicing
import Realization.Lisp.Transforms

import System.IO
import qualified Data.Text as T
import Data.Map (Map)
import Data.List (stripPrefix)
import System.Console.GetOpt
import System.Environment
import System.Exit
import Control.Monad
import Data.Foldable
import Prelude hiding (foldl)

data Options = Options { showHelp :: Bool
                       , solver :: String
                       , transformation :: [Transformation]
                       , verbose :: Int }

data Transformation = Inline
                    | Simplify
                    | ValueSetAnalysis Int
                    | Slice

options :: [OptDescr (Options -> Options)]
options = [Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True }) "Shows this help."
          ,Option ['v'] ["verbose"] (OptArg (\v opt -> case v of
                                               Just v' -> opt { verbose = read v' }
                                               Nothing -> opt { verbose = 1 }) "level"
                                    ) "Output more information while running (higher level = more info)"
          ,Option ['s'] ["solver"] (ReqArg (\s opt -> opt { solver = s }) "solver")
           "The SMT solver used for the value-set analysis."]

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , solver = "z3 -smt2 -in"
                         , transformation = []
                         , verbose = 0 }

getOptions :: IO Options
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
    (xs,transf,[]) -> do
       let opts = foldl (flip id) defaultOptions xs
       when (showHelp opts) $ do
         putStrLn $
           usageInfo
           (unlines ["USAGE: vvt-opt [TRANS...] < <file>"
                    ,"       where <file> is a transition relation in lisp format."
                    ,""
                    ,"  TRANS can be one of the following transformations:"
                    ,"    inline        - Inline gates that are used only once."
                    ,"    simplify      - Simplify expressions in the program."
                    ,"    value-set[=p] - Identify constant state variables."
                    ,"    slice         - Remove unreachable parts of the program."
                    ]
           ) options
         exitSuccess
       transf' <- mapM (\t -> case parseTransformation t of
                          Nothing -> do
                            hPutStrLn stderr $ "Failed to parse transformation: "++t
                            exitFailure
                          Just t' -> return t'
                       ) transf
       let transf'' = case transf' of
             [] -> [ValueSetAnalysis 1,Inline,Simplify,Slice]
             _ -> transf'
       return (opts { transformation = transf'' })
    (_,_,errs) -> do
      hPutStrLn stderr "vvt-opt: Error while parsing command-line options:"
      mapM (\err -> hPutStrLn stderr $ "  "++err) errs
      exitFailure

applyTransformation :: Options -> LispProgram -> Transformation -> IO LispProgram
applyTransformation _ prog Inline = return $ doInlining prog
applyTransformation _ prog Simplify = return $ simplifyProgram prog
applyTransformation opts prog (ValueSetAnalysis threshold)
  = valueSetAnalysis (verbose opts) threshold (solver opts) prog
applyTransformation _ prog Slice = return $ slice prog

parseTransformation :: String -> Maybe Transformation
parseTransformation "inline" = Just Inline
parseTransformation "simplify" = Just Simplify
parseTransformation "slice" = Just Slice
parseTransformation (stripPrefix "value-set" -> Just rest) = case rest of
  '=':n -> Just $ ValueSetAnalysis (read n)
  "" -> Just $ ValueSetAnalysis 5
  _ -> Nothing
parseTransformation _  = Nothing

main :: IO ()
main = do
  opts <- getOptions
  prog <- fmap parseProgram (readLispFile stdin)
  prog' <- foldlM (applyTransformation opts) prog (transformation opts)
  case fsck prog' of
    [] -> return ()
    msgs -> error $ "Invalid program generated:\n"++unlines msgs
  print $ programToLisp prog'
