module Main where

import Realization.Lisp
import Realization.LispKarr

import System.Environment

main = do
  [file] <- getArgs
  prog <- fmap parseLispProgram $ readLispFile file
  nprog <- addKarrPredicates prog
  print $ programToLisp nprog
  
