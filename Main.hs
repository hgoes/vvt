module Main where

import LLVMLoader4
import Realization
import CTIGAR

import System.Environment

main = do
  [file,entry] <- getArgs
  fun <- getProgram entry file
  st <- realizeFunction fun
  tr <- check st
  case tr of
    Nothing -> putStrLn "No bug found."
    Just tr' -> print tr'
