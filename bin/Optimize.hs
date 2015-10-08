{-# LANGUAGE ViewPatterns #-}
module Main where

import Realization.Lisp
import Realization.Lisp.Simplify.Dataflow
import Realization.Lisp.Simplify.Inliner
import Realization.Lisp.Simplify.ExprSimplify
import Realization.Lisp.Simplify.ValueSet

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
                       , transformation :: [Transformation] }

data Transformation = Inline
                    | Simplify
                    | ValueSetAnalysis Int

options :: [OptDescr (Options -> Options)]
options = [Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True }) "Shows this help."]

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , transformation = [] }

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
             [] -> [ValueSetAnalysis 1,Inline,Simplify]
             _ -> transf'
       return (opts { transformation = transf'' })
    (_,_,errs) -> do
      hPutStrLn stderr "vvt-opt: Error while parsing command-line options:"
      mapM (\err -> hPutStrLn stderr $ "  "++err) errs
      exitFailure

applyTransformation :: LispProgram -> Transformation -> IO LispProgram
applyTransformation prog Inline = return $ doInlining prog
applyTransformation prog Simplify = return $ simplifyProgram prog
applyTransformation prog (ValueSetAnalysis threshold) = valueSetAnalysis threshold prog

parseTransformation :: String -> Maybe Transformation
parseTransformation "inline" = Just Inline
parseTransformation "simplify" = Just Simplify
parseTransformation (stripPrefix "value-set" -> Just rest) = case rest of
  '=':n -> Just $ ValueSetAnalysis (read n)
  "" -> Just $ ValueSetAnalysis 5
  _ -> Nothing
parseTransformation _  = Nothing

main :: IO ()
main = do
  opts <- getOptions
  prog <- fmap parseLispProgram (readLispFile stdin)
  prog' <- foldlM applyTransformation prog (transformation opts)
  print $ programToLisp prog'
