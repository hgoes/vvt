module Main where

import Realization.Lisp
import Realization.Lisp.Simplify.Dataflow
import Realization.Lisp.Simplify.Inliner
import Realization.Lisp.Simplify.ExprSimplify

import System.IO
import qualified Data.Text as T
import Data.Map (Map)

main :: IO ()
main = do
  prog <- fmap parseLispProgram (readLispFile stdin)
  print $ programToLisp (simplifyProgram $ doInlining prog)
