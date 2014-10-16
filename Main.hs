module Main where

import Realization
import Options
import CTIGAR

import System.IO
import System.Exit
import System.Timeout
import Control.Concurrent
import Control.Exception
import Prelude (Either(..),mapM_,Maybe(..),(>>),return,Bool(..))

main = do
  opts <- readOptions
  case opts of
   Left errs -> do
     mapM_ (hPutStrLn stderr) errs
     exitWith (ExitFailure (-1))
   Right (file,opts) -> do
     let ropts = RealizationOptions { useErrorState = True
                                    , exactPredecessors = False
                                    , optimize = optOptimizeTR opts }
     fun <- getProgram ropts (optFunction opts) file
     st <- getModel ropts fun
     tr <- case optTimeout opts of
            Nothing -> check st opts
            Just to -> do
              mainThread <- myThreadId
              timeoutThread <- forkOS (threadDelay to >> throwTo mainThread (ExitFailure (-2)))
              res <- catch (do
                               res <- check st opts
                               killThread timeoutThread
                               return (Just res)
                           )
                     (\ex -> case ex of
                       ExitFailure _ -> return Nothing)
              case res of
               Just tr -> return tr
               Nothing -> do
                 hPutStrLn stderr "Timeout"
                 exitWith (ExitFailure (-2))
     case tr of
      Nothing -> putStrLn "No bug found."
      Just tr' -> do
        putStrLn "Bug found:"
        mapM_ print tr'
