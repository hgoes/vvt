module Main where

import Realization
import Options
import CTIGAR

import System.IO
import System.Exit

main = do
  opts <- readOptions
  case opts of
   Left errs -> do
     mapM_ (hPutStrLn stderr) errs
     exitWith (ExitFailure (-1))
   Right (file,opts) -> do
     fun <- getProgram (optFunction opts) file
     st <- realizeFunction fun
     tr <- check st opts
     case tr of
      Nothing -> putStrLn "No bug found."
      Just tr' -> print tr'
