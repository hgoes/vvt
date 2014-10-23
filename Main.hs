{-# LANGUAGE RankNTypes #-}
module Main where

import Realization
import Realization.Common
import Realization.Monolithic
import qualified Realization.BlockWise as BlockWise
import Options
import CTIGAR (check)
import PartialArgs

import System.IO
import System.Exit
import System.Timeout
import Control.Concurrent
import Control.Exception
import Prelude (Either(..),mapM_,Maybe(..),(>>),(>>=),return,Bool(..),undefined,($),String)

main = do
  opts <- readOptions
  case opts of
   Left errs -> do
     mapM_ (hPutStrLn stderr) errs
     exitWith (ExitFailure (-1))
   Right (file,opts) -> getTransitionRelation file opts $ \st -> do
     let ropts = RealizationOptions { useErrorState = True
                                    , exactPredecessors = False
                                    , optimize = optOptimizeTR opts }
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
        mapM_ (\(step,_) -> renderPartialState st
                            (unmaskValue (getUndefState st) step) >>= putStrLn
              ) tr'

getUndefState :: TransitionRelation tr => tr -> State tr
getUndefState _ = undefined

getTransitionRelation :: String -> Options
                         -> (forall mdl. TransitionRelation mdl => mdl -> IO a) -> IO a
getTransitionRelation file opts f = do
  let ropts = RealizationOptions { useErrorState = True
                                    , exactPredecessors = False
                                    , optimize = optOptimizeTR opts }
  fun <- getProgram (optOptimizeTR opts) (optFunction opts) file
  case optEncoding opts of
   Monolithic -> do
     st <- getModel ropts fun
     f st
   BlockWise -> do
     st <- BlockWise.realizeFunction fun
     f st
