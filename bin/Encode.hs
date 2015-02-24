module Main where

import Realization.Common
import Realization.Threaded
import Realization.Threaded.Translation
import Realization.Lisp

import System.Environment

main = do
  [file] <- getArgs
  (mod,fun) <- getProgram False False "main" file
  real <- realizeProgram mod fun
  lisp <- toLispProgram real
  print $ programToLisp lisp
