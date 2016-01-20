{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Benchmarks where

import Control.Monad(foldM)
import Numeric
import Prelude hiding (FilePath)
import Turtle
import GHC.Generics
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Yaml as Y

data BenchMarkStats =
    BenchMarkStats
    { mrs_consecutionTime :: Float
    , mrs_consecutionNum :: Float
    , mrs_domainTime :: Float
    , mrs_domainNum :: Float
    , mrs_interpolationTime :: Float
    , mrs_interpolationNum :: Float
    , mrs_liftingTime :: Float
    , mrs_liftingNum :: Float
    , mrs_initiationTime :: Float
    , mrs_initiationNum :: Float
    , mrs_numErased :: Float
    , mrs_numCTI :: Float
    , mrs_numUnliftedErased :: Float
    , mrs_numCTG :: Float
    , mrs_numMIC :: Float
    , mrs_numCoreReduced :: Float
    , mrs_numAbortJoin :: Float
    , mrs_numAbortMic :: Float
    , mrs_numRefinements :: Float
    , mrs_numAddPreds :: Float
    , mrs_numPreds :: Float
    } deriving Generic

instance Y.FromJSON BenchMarkStats

instance Show BenchMarkStats where
    show bms =
        ("consecutionTime: " ++ ((showFFloat Nothing (mrs_consecutionTime bms)) "") ++ "\n")
        ++ ("consecutionNum: " ++ ((showFFloat Nothing (mrs_consecutionNum bms)) "") ++ "\n")
        ++ ("domainTime:" ++ ((showFFloat Nothing (mrs_domainTime bms)) "") ++ "\n")
        ++ ("domainNum:" ++ ((showFFloat Nothing (mrs_domainNum bms)) "") ++ "\n")
        ++ ("interpolationTime:" ++ ((showFFloat Nothing (mrs_interpolationTime bms)) "") ++ "\n")
        ++ ("interpolationNum:" ++ ((showFFloat Nothing (mrs_interpolationNum bms)) "") ++ "\n")
        ++ ("liftingTime:" ++ ((showFFloat Nothing (mrs_liftingTime bms)) "") ++ "\n")
        ++ ("liftingNum:" ++ ((showFFloat Nothing (mrs_liftingNum bms)) "") ++ "\n")
        ++ ("initiationTime:" ++ ((showFFloat Nothing (mrs_initiationTime bms)) "") ++ "\n")
        ++ ("initiationNum:" ++ ((showFFloat Nothing (mrs_initiationNum bms)) "") ++ "\n")
        ++ ("numErased:" ++ ((showFFloat Nothing (mrs_numErased bms)) "") ++ "\n")
        ++ ("numCTI:" ++ ((showFFloat Nothing (mrs_numCTI bms)) "") ++ "\n")
        ++ ("numUnliftedErased:" ++ ((showFFloat Nothing (mrs_numUnliftedErased bms)) "") ++ "\n")
        ++ ("numCTG:" ++ ((showFFloat Nothing (mrs_numCTG bms)) "") ++ "\n")
        ++ ("numMIC:" ++ ((showFFloat Nothing (mrs_numMIC bms)) "") ++ "\n")
        ++ ("numCoreReduced:" ++ ((showFFloat Nothing (mrs_numCoreReduced bms)) "") ++ "\n")
        ++ ("numAbortJoin:" ++ ((showFFloat Nothing (mrs_numAbortJoin bms)) "") ++ "\n")
        ++ ("numAbortMic:" ++ ((showFFloat Nothing (mrs_numAbortMic bms)) "") ++ "\n")
        ++ ("numRefinements:" ++ ((showFFloat Nothing (mrs_numRefinements bms)) "") ++ "\n")
        ++ ("numAddPreds:" ++ ((showFFloat Nothing (mrs_numAddPreds bms)) "") ++ "\n")
        ++ ("numPreds:" ++ ((showFFloat Nothing (mrs_numPreds bms)) "") ++ "\n")

emptyIC3MrsStats :: BenchMarkStats
emptyIC3MrsStats =
    BenchMarkStats
    { mrs_consecutionTime = 0
    , mrs_consecutionNum = 0
    , mrs_domainTime = 0
    , mrs_domainNum = 0
    , mrs_interpolationTime = 0
    , mrs_interpolationNum = 0
    , mrs_liftingTime = 0
    , mrs_liftingNum = 0
    , mrs_initiationTime = 0
    , mrs_initiationNum = 0
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


type BenchConf = [FilePath]

benchmarks :: BenchConf
benchmarks = [ "bound.c"
             , "barbrprime.c"
             , "simple_nest.c"
             , "pldi08.c"
             , "xy0.c"
             , "up5.c"
             ]

binDir :: FilePath
binDir = ".stack-work/install/x86_64-linux/lts-2.22/7.8.4/bin/"

progDir :: FilePath
progDir = "test/"

trDir :: FilePath
trDir = "trcache/"

benchResults :: FilePath
benchResults = "bench.log"

runBench :: IO ()
runBench = do
  dir <- pwd
  putStrLn $ show dir
  mapM_ (\prog -> do
           trExists <- testfile (trDir </> (dropExtension prog))
           case trExists of
             True -> return ()
             False -> do
               progAsTxt <- safeToText (progDir </> prog)
               vvtBinary <- safeToText (binDir </> "vvt")
               let dest = trDir </> (dropExtension prog)
               output dest $ Turtle.inproc
                             vvtBinary
                             ["encode", progAsTxt]
                             Turtle.empty
               return ()
        ) benchmarks
  benchFileExists <- testfile "bench.log"
  case benchFileExists of
    True -> rm "bench.log"
    False -> return ()
  (accumStats, _) <-
      foldM (\(accumulatedStats, n) prog-> do
               transitionRelation <- safeToText $ trDir </> (dropExtension prog)
               verifyBinary <- safeToText (binDir </> "vvt-verify")
               putStrLn $ T.unpack $ verifyBinary <> (" < " <> transitionRelation)
               _ <- sh $ inshell (verifyBinary <> " < " <> (T.pack $ show $ transitionRelation)) Turtle.empty
               mStats <- (return . Y.decode =<< BS.readFile "stats.yaml") :: IO (Maybe BenchMarkStats)
               case mStats of
                 Just stats -> do
                   append benchResults $ select $ fmap T.pack [ ("benchmark " ++ (show n))
                                                              , (show stats)
                                                              ]
                   let addToAccumStats field = (field stats) + (field accumulatedStats)
                   return (BenchMarkStats
                           { mrs_consecutionTime = addToAccumStats mrs_consecutionTime
                           , mrs_consecutionNum = addToAccumStats mrs_consecutionNum
                           , mrs_domainTime = addToAccumStats mrs_domainTime
                           , mrs_domainNum = addToAccumStats mrs_domainNum
                           , mrs_interpolationTime = addToAccumStats mrs_interpolationTime
                           , mrs_interpolationNum = addToAccumStats mrs_interpolationNum
                           , mrs_liftingTime = addToAccumStats mrs_liftingTime
                           , mrs_liftingNum = addToAccumStats mrs_liftingNum
                           , mrs_initiationTime = addToAccumStats mrs_initiationTime
                           , mrs_initiationNum = addToAccumStats mrs_initiationNum
                           , mrs_numErased = addToAccumStats mrs_numErased
                           , mrs_numCTI = addToAccumStats mrs_numCTI
                           , mrs_numUnliftedErased = addToAccumStats mrs_numUnliftedErased
                           , mrs_numCTG = addToAccumStats mrs_numCTG
                           , mrs_numMIC = addToAccumStats mrs_numMIC
                           , mrs_numCoreReduced = addToAccumStats mrs_numCoreReduced
                           , mrs_numAbortJoin = addToAccumStats mrs_numAbortJoin
                           , mrs_numAbortMic = addToAccumStats mrs_numAbortMic
                           , mrs_numRefinements = addToAccumStats mrs_numRefinements
                           , mrs_numAddPreds = addToAccumStats mrs_numAddPreds
                           , mrs_numPreds = addToAccumStats mrs_numPreds
                           }
                          , n+1 )
                 Nothing -> fail "could not parse stats.yaml file"
            ) (emptyIC3MrsStats, 1) benchmarks :: IO (BenchMarkStats, Int)
  let calcMean field = (field accumStats) / (fromIntegral (length benchmarks)) :: Float
      meanVals =
          BenchMarkStats
          { mrs_consecutionTime = calcMean mrs_consecutionTime
          , mrs_consecutionNum = calcMean mrs_consecutionNum
          , mrs_domainTime = calcMean mrs_domainTime
          , mrs_domainNum = calcMean mrs_domainNum
          , mrs_interpolationTime = calcMean mrs_interpolationTime
          , mrs_interpolationNum = calcMean mrs_interpolationNum
          , mrs_liftingTime = calcMean mrs_liftingTime
          , mrs_liftingNum = calcMean mrs_liftingNum
          , mrs_initiationTime = calcMean mrs_initiationTime
          , mrs_initiationNum = calcMean mrs_initiationNum
          , mrs_numErased = calcMean mrs_numErased
          , mrs_numCTI = calcMean mrs_numCTI
          , mrs_numUnliftedErased = calcMean mrs_numUnliftedErased
          , mrs_numCTG = calcMean mrs_numCTG
          , mrs_numMIC = calcMean mrs_numMIC
          , mrs_numCoreReduced = calcMean mrs_numCoreReduced
          , mrs_numAbortJoin = calcMean mrs_numAbortJoin
          , mrs_numAbortMic = calcMean mrs_numAbortMic
          , mrs_numRefinements = calcMean mrs_numRefinements
          , mrs_numAddPreds = calcMean mrs_numAddPreds
          , mrs_numPreds = calcMean mrs_numPreds
          }

  append benchResults $ select $ fmap T.pack ["mean values over all benchmarks:", (show meanVals)]



safeToText :: MonadIO io => FilePath -> io T.Text
safeToText filepath =
    case toText filepath of
      Right decodedFp -> return decodedFp
      Left approxFp -> fail $ "could not decode fp: " ++ (show approxFp)

-- benchStatsToList :: BenchMarkStats -> [Float]
-- benchStatsToList bms =
--     [ mrs_consecutionTime bms
--     , mrs_consecutionNum bms
--     , mrs_domainTime bms
--     , mrs_domainNum bms
--     , mrs_interpolationTime bms
--     , mrs_interpolationNum bms
--     , mrs_liftingTime bms
--     , mrs_liftingNum bms
--     , mrs_initiationTime bms
--     , mrs_initiationNum bms
--     , mrs_numErased bms
--     , mrs_numCTI bms
--     , mrs_numUnliftedErased bms
--     , mrs_numCTG bms
--     , mrs_numMIC bms
--     , mrs_numCoreReduced bms
--     , mrs_numAbortJoin bms
--     , mrs_numAbortMic bms
--     , mrs_numRefinements bms
--     , mrs_numAddPreds bms
--     , mrs_numPreds bms ]

-- benchStatsFromList :: [FLoat] -> BenchMarkStats
-- benchStatsFromList lst
--     | length list != 21 = error "error converting List to BenchMarkStats: check if the dataType was changed"
--     | otherwise =
--         BenchMarkStats
--         { mrs_consecutionTime = lst !! 0
--         , mrs_consecutionNum = lst !! 1
--         , mrs_domainTime = lst !! 2
--         , mrs_domainNum = lst !! 3
--         , mrs_interpolationTime = lst !! 4
--         , mrs_interpolationNum = lst !! 5
--         , mrs_liftingTime = lst !! 6
--         , mrs_liftingNum = lst !! 7
--         , mrs_initiationTime = lst !! 8
--         , mrs_initiationNum = lst !! 9
--         , mrs_numErased = lst !! 10
--         , mrs_numCTI = lst !! 11
--         , mrs_numUnliftedErased = lst !! 12
--         , mrs_numCTG = lst !! 13
--         , mrs_numMIC = lst !! 14
--         , mrs_numCoreReduced = lst !! 15
--         , mrs_numAbortJoin = lst !! 16
--         , mrs_numAbortMic = lst !! 17
--         , mrs_numRefinements = lst !! 18
--         , mrs_numAddPreds = lst !! 19
--         , mrs_numPreds = lst !! 20 }
