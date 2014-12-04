module Main where

import Realization.Lisp
import Realization.LispKarr

import System.IO

main = do
  prog <- fmap parseLispProgram $ readLispFile stdin
  nprog <- addKarrPredicates prog
  print $ programToLisp nprog
  
