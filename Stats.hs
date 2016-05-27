{-# LANGUAGE DeriveGeneric #-}
module Stats where

import Data.IORef
import Data.Time.Clock
import GHC.Generics
import Numeric
import qualified Data.Yaml as Y

data IC3Stats =
    IC3Stats { startTime :: UTCTime
             , consecutionTime :: IORef NominalDiffTime
             , consecutionNum :: IORef Int
             , domainTime :: IORef NominalDiffTime
             , domainNum :: IORef Int
             , interpolationTime :: IORef NominalDiffTime
             , interpolationNum :: IORef Int
             , liftingTime :: IORef NominalDiffTime
             , liftingNum :: IORef Int
             , initiationTime :: IORef NominalDiffTime
             , initiationNum :: IORef Int
             , rsmTime :: NominalDiffTime
             , numErased :: Int
             , numCTI :: Int
             , numUnliftedErased :: Int
             , numCTG :: Int
             , numMIC :: Int
             , numCoreReduced :: Int
             , numAbortJoin :: Int
             , numAbortMic :: Int
             , numRefinements :: Int
             , numAddPreds :: Int
             }

data IC3MachineReadableStats =
    IC3MachineReadableStats
    { mrs_totalTime :: Float
    , mrs_consecutionTime :: Float
    , mrs_consecutionNum :: Int
    , mrs_domainTime :: Float
    , mrs_domainNum :: Int
    , mrs_interpolationTime :: Float
    , mrs_interpolationNum :: Int
    , mrs_liftingTime :: Float
    , mrs_liftingNum :: Int
    , mrs_initiationTime :: Float
    , mrs_initiationNum :: Int
    , mrs_rsmTime :: Float
    , mrs_numErased :: Int
    , mrs_numCTI :: Int
    , mrs_numUnliftedErased :: Int
    , mrs_numCTG :: Int
    , mrs_numMIC :: Int
    , mrs_numCoreReduced :: Int
    , mrs_numAbortJoin :: Int
    , mrs_numAbortMic :: Int
    , mrs_numRefinements :: Int
    , mrs_numAddPreds :: Int
    , mrs_numPreds :: Int
    } deriving Generic

instance Y.ToJSON IC3MachineReadableStats
instance Y.FromJSON IC3MachineReadableStats

instance Show IC3MachineReadableStats where
    show mrs =
        (("totalTime: " ++ ((showFFloat Nothing (mrs_totalTime mrs) "") ++ "\n")
        ++ ("consecutionTime: " ++ (showFFloat Nothing  (mrs_consecutionTime mrs) "") ++ "\n"))
        ++ ("consecutionNum: " ++ show (mrs_consecutionNum mrs) ++ "\n")
        ++ ("domainTime:" ++ (showFFloat Nothing (mrs_domainTime mrs) "") ++ "\n")
        ++ ("domainNum:" ++ show (mrs_domainNum mrs) ++ "\n")
        ++ ("interpolationTime:" ++ ((showFFloat Nothing (mrs_interpolationTime mrs)) "") ++ "\n")
        ++ ("interpolationNum:" ++ show (mrs_interpolationNum mrs) ++ "\n")
        ++ ("liftingTime:" ++ ((showFFloat Nothing (mrs_liftingTime mrs)) "") ++ "\n")
        ++ ("liftingNum:" ++ show (mrs_liftingNum mrs) ++ "\n")
        ++ ("initiationTime:" ++ ((showFFloat Nothing (mrs_initiationTime mrs)) "") ++ "\n")
        ++ ("initiationNum:" ++ show (mrs_initiationNum mrs) ++ "\n")
        ++ ("rsmTime:" ++ show (mrs_rsmTime mrs) ++ "\n")
        ++ ("numErased:" ++ show (mrs_numErased mrs) ++ "\n")
        ++ ("numCTI:" ++ show (mrs_numCTI mrs) ++ "\n")
        ++ ("numUnliftedErased:" ++ show (mrs_numUnliftedErased mrs) ++ "\n")
        ++ ("numCTG:" ++ show (mrs_numCTG mrs) ++ "\n")
        ++ ("numMIC:" ++ show (mrs_numMIC mrs) ++ "\n")
        ++ ("numCoreReduced:" ++ show (mrs_numCoreReduced mrs) ++ "\n")
        ++ ("numAbortJoin:" ++ show (mrs_numAbortJoin mrs) ++ "\n")
        ++ ("numAbortMic:" ++ show (mrs_numAbortMic mrs) ++ "\n")
        ++ ("numRefinements:" ++ show (mrs_numRefinements mrs) ++ "\n")
        ++ ("numAddPreds:" ++ show (mrs_numAddPreds mrs) ++ "\n")
        ++ ("numPreds:" ++ show (mrs_numPreds mrs) ++ "\n"))


emptyIC3MRStats :: IC3MachineReadableStats
emptyIC3MRStats =
    IC3MachineReadableStats
    { mrs_totalTime = 0
    , mrs_consecutionTime = 0
    , mrs_consecutionNum = 0
    , mrs_domainTime = 0
    , mrs_domainNum = 0
    , mrs_interpolationTime = 0
    , mrs_interpolationNum = 0
    , mrs_liftingTime = 0
    , mrs_liftingNum = 0
    , mrs_initiationTime = 0
    , mrs_initiationNum = 0
    , mrs_rsmTime = 0
    , mrs_numErased = 0
    , mrs_numCTI = 0
    , mrs_numUnliftedErased = 0
    , mrs_numCTG = 0
    , mrs_numMIC = 0
    , mrs_numCoreReduced = 0
    , mrs_numAbortJoin = 0
    , mrs_numAbortMic = 0
    , mrs_numRefinements = 0
    , mrs_numAddPreds = 0
    , mrs_numPreds = 0
    }

