{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Benchmarks where

-- Local --
import Stats

-- StandardLib --
import Control.Monad(foldM)
import Data.Maybe(catMaybes)
import Filesystem.Path(addExtension)
import Numeric
import Prelude hiding (FilePath)
import Turtle
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Yaml as Y


type BenchConf = [FilePath]

benchmarks_hard :: BenchConf
benchmarks_hard = [ "svd4.c"
                  , "cars.c"
                  , "mergesort.c"
                  , "simple_nest.c"
                  ]

getAllBenchmarks :: IO BenchConf
getAllBenchmarks = do
  benchmarks <- liftIO $ Turtle.fold
                         (Turtle.ls progDir)
                         (Fold
                          (\benchs newFP ->
                               case extension newFP of
                                 Just "c" -> newFP : benchs
                                 _ -> benchs
                          )
                          []
                          id
                         )
  let parentDir = commonPrefix benchmarks
      benchmarksStripped = catMaybes $ map (stripPrefix parentDir) benchmarks
  return benchmarksStripped

getSVCompPrecompiledBenchmarks :: IO BenchConf
getSVCompPrecompiledBenchmarks = do
  benchmarks <- liftIO $ Turtle.fold
                         (Turtle.ls trDir)
                         (Fold
                          (\benchs newFP ->
                               case extension newFP of
                                 Just "l" -> (addExtension newFP "c" ) : benchs
                                 _ -> benchs
                          )
                          []
                          id
                         )
  let parentDir = commonPrefix benchmarks
      benchmarksStripped = catMaybes $ map (stripPrefix parentDir) benchmarks
  return benchmarksStripped

binDir :: FilePath
binDir = ".stack-work/install/x86_64-linux/lts-3.19/7.10.3/bin/"

progDir :: FilePath
progDir = "test/"

trDir :: FilePath
trDir = "trcache/"

benchResults :: FilePath
benchResults = "bench.log"

_onlyHardBenchmarks_ :: Bool
_onlyHardBenchmarks_ = False

_dontCreateTransitionRelations_ :: Bool
_dontCreateTransitionRelations_ = True

runBench :: IO ()
runBench = do
  benchmarks <-
      case _onlyHardBenchmarks_ of
        True -> return benchmarks_hard
        False -> getAllBenchmarks
  case _dontCreateTransitionRelations_ of
    True -> return ()
    False ->
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
               let transitionRelation = trDir </> (dropExtension prog)
               trAsText <- safeToText transitionRelation
               verifyBinary <- safeToText (binDir </> "vvt-verify")
               putStrLn $ T.unpack $ verifyBinary <> (" < " <> trAsText)
               logFile <- safeToText (addExtension ("log" </> (dropExtension prog)) "log")
               _ <- sh $ inshell (verifyBinary
                                 <> " < " <> (T.pack $ show $ trAsText)
                                 <> " > " <> logFile
                                 ) Turtle.empty
               mStats <- (return . Y.decode =<< BS.readFile "stats.yaml") :: IO (Maybe IC3MachineReadableStats)
               case mStats of
                 Just stats -> do
                   append benchResults $ select $ fmap T.pack [ ("benchmark " ++ (show n) ++ ": " ++ (show prog))
                                                              , (show stats)
                                                              ]
                   let addToAccumStats field = (field stats) + (field accumulatedStats)
                   return (IC3MachineReadableStats
                           { mrs_totalTime = addToAccumStats mrs_totalTime
                           , mrs_consecutionTime = addToAccumStats mrs_consecutionTime
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
            ) (emptyIC3MRStats, 1) benchmarks :: IO (IC3MachineReadableStats, Int)
  let calcMean field = (field accumStats) / (fromIntegral (length benchmarks)) :: Float
      meanValsPrettyString =
          (("totalTime: " ++((showFFloat Nothing (calcMean mrs_totalTime)) "") ++ "\n")
        ++ ("consecutionTime: " ++ ((showFFloat Nothing (calcMean mrs_consecutionTime)) "") ++ "\n"))
        ++ ("consecutionNum: " ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_consecutionNum))) "") ++ "\n")
        ++ ("domainTime:" ++ ((showFFloat Nothing (calcMean mrs_domainTime)) "") ++ "\n")
        ++ ("domainNum:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_domainNum))) "") ++ "\n")
        ++ ("interpolationTime:" ++ ((showFFloat Nothing (calcMean mrs_interpolationTime)) "") ++ "\n")
        ++ ("interpolationNum:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_interpolationNum))) "") ++ "\n")
        ++ ("liftingTime:" ++ ((showFFloat Nothing (calcMean mrs_liftingTime)) "") ++ "\n")
        ++ ("liftingNum:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_liftingNum))) "") ++ "\n")
        ++ ("initiationTime:" ++ ((showFFloat Nothing (calcMean mrs_initiationTime)) "") ++ "\n")
        ++ ("initiationNum:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_initiationNum))) "") ++ "\n")
        ++ ("numErased:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numErased))) "") ++ "\n")
        ++ ("numCTI:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numCTI))) "") ++ "\n")
        ++ ("numUnliftedErased:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numUnliftedErased))) "") ++ "\n")
        ++ ("numCTG:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numCTG))) "") ++ "\n")
        ++ ("numMIC:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numMIC))) "") ++ "\n")
        ++ ("numCoreReduced:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numCoreReduced))) "") ++ "\n")
        ++ ("numAbortJoin:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numAbortJoin))) "") ++ "\n")
        ++ ("numAbortMic:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numAbortMic))) "") ++ "\n")
        ++ ("numRefinements:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numRefinements))) "") ++ "\n")
        ++ ("numAddPreds:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numAddPreds))) "") ++ "\n")
        ++ ("numPreds:" ++ ((showFFloat Nothing (calcMean (fromIntegral . mrs_numPreds))) "") ++ "\n")

  append benchResults $ select $ fmap T.pack ["mean values over all benchmarks:", meanValsPrettyString]



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
