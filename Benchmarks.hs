{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Benchmarks where

-- Local --
import Stats

-- StandardLib --
import Control.Monad(foldM)
import Filesystem.Path(addExtension)
import Numeric
import Options.Applicative
import Prelude hiding (FilePath)
import Turtle
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Yaml as Y
import qualified Options.Applicative as OA

newtype Benchmark = Benchmark { bm_toFilePath :: FilePath }

data BenchConf =
    BenchConf
    { bc_binDir :: FilePath
    , bc_trDir :: FilePath
    , bc_logDir :: FilePath
    , bc_dontCreateTr :: Bool
    , bc_optimizeTr :: Bool
    , bc_results :: FilePath
    , bc_benchmarks :: FilePath
    }

benchConfParser :: Parser BenchConf
benchConfParser =
    BenchConf
    <$>
    OA.option (fmap (fromText . T.pack) str)
      (  long "bin-dir"
      <> value _DEFAULT_BINDIR_
      <> metavar "FILEPATH"
      <> help "Directory where vvt binaries are installed"
      )
    <*>
    OA.option (fmap (fromText . T.pack) str)
      (  long "tr-cache"
      <> value _DEFAULT_TRDIR_
      <> metavar "FILEPATH"
      <> help "Directory where Transition Relations Files are cached"
      )
    <*>
    OA.option (fmap (fromText . T.pack) str)
      (  long "log-dir"
      <> value _DEFAULT_LOGDIR_
      <> metavar "FILEPATH"
      <> help "Directory where vvt-verify execution logs are written to"
      )
    <*>
    OA.flag False True
      (  long "dont-create-tr"
      <> help "If this option is chosen, a new transition relation will be created if no one is found"
      )
    <*>
    OA.flag True False
      (  long "no-opt"
      <> help "If this option is chosen, transition relations will be built without optimization"
      )
    <*>
    OA.option (fmap (fromText . T.pack) str)
      (  long "results-file"
      <> value _DEFAULT_RESULTSFILE_
      <> metavar "FILEPATH"
      <> help "File, in which results are published"
      )
    <*>
    OA.option (fmap (fromText . T.pack) str)
      (  long "benchmarks"
      <> value _DEFAULT_BENCHDIR_
      <> metavar "FILEPATH"
      <> help "Directory, where benchmarks are located"
      )

_DEFAULT_BINDIR_ :: FilePath
_DEFAULT_BINDIR_ = ".stack-work/install/x86_64-linux/lts-3.19/7.10.3/bin/"

_DEFAULT_TRDIR_ :: FilePath
_DEFAULT_TRDIR_ = "trcache/"

_DEFAULT_RESULTSFILE_ :: FilePath
_DEFAULT_RESULTSFILE_ = "bench.log"

_DEFAULT_BENCHDIR_ :: FilePath
_DEFAULT_BENCHDIR_ = "test/"

_DEFAULT_LOGDIR_ :: FilePath
_DEFAULT_LOGDIR_ = "log/"

_VERIFY_OPTS_ :: T.Text
_VERIFY_OPTS_ = " -v5 --stats --timeout=200s"

getAllBenchmarks :: BenchConf -> IO [Benchmark]
getAllBenchmarks conf =
  liftIO $ Turtle.fold
             (Turtle.ls benchDir)
             (Fold
              (\benchs newFP ->
                   case extension newFP of
                     Just "c" -> (Benchmark newFP) : benchs
                     _ -> benchs
              )
              []
              id
             )
    where
      benchDir = bc_benchmarks conf

benchMain :: IO ()
benchMain = execParser opts >>= runBench
  where
    opts = info (helper <*> benchConfParser)
           (fullDesc <> progDesc "Run a set of benchmarks")

runBench :: BenchConf -> IO ()
runBench conf = do
  let resultsFile = bc_results conf
  resFileExists <- testfile resultsFile
  case resFileExists of
    True -> do
      let resFileAsText = safeToText resultsFile
      stderr . return $ "ResultsFile: " <> resFileAsText <> " already exists! Not proceeding"
    False -> do
      benchmarks <- getAllBenchmarks conf
      let benchName bench = basename bench
          trDir = bc_trDir conf
          binDir = bc_binDir conf
          logDir = bc_logDir conf
      case bc_dontCreateTr conf of
        True -> return ()
        False ->
            mapM_ (\(Benchmark bench) -> do
                     trExists <- testfile (trDir </> benchName bench)
                     case trExists of
                       True -> return ()
                       False ->
                           let benchAsTxt = safeToText bench
                               vvtBinary = safeToText (binDir </> "vvt")
                               vvtenc = safeToText (binDir </> "vvt-enc")
                               vvtpreds = safeToText (binDir </> "vvt-predicates")
                               vvtpp = safeToText (binDir </> "vvt-pp")
                               dest = safeToText $ trDir </> (benchName bench)
                               cmdToExecute =
                                   case bc_optimizeTr conf of
                                     True ->
                                         vvtBinary
                                         <> " encode -o " <> dest
                                         <> " -i "
                                         <> benchAsTxt
                                         <> " > /dev/null" <> " 2>&1"
                                     False ->
                                         vvtBinary
                                         <> " show-llvm "
                                         <> benchAsTxt
                                         <> " | " <> vvtenc
                                         <> " 2>/dev/null "
                                         <> " | " <> vvtpreds <> " -i"
                                         <> " | " <> vvtpp
                                         <> " 1> " <> dest
                           in do
                             echo cmdToExecute
                             exitCode <- shell cmdToExecute Turtle.empty
                             case exitCode of
                               ExitFailure _ ->
                                   echo $ "vvt-verify encode failed on benchmark: "
                                            <> benchAsTxt
                               _ -> return ()
                  ) benchmarks
      (accumStats, _) <-
          foldM (\(accumulatedStats, n) (Benchmark bench) -> do
                   let transitionRelation = trDir </> (benchName bench)
                       trAsText = safeToText transitionRelation
                       verifyBinary = safeToText (binDir </> "vvt-verify")
                       logFile = safeToText (addExtension (logDir </> benchName bench) "log")
                   with (mktempfile "" "/tmp/") (\tmp -> do
                       let tmpFileForStats = safeToText tmp
                           cmdToExecute =
                               verifyBinary
                                <> " --dump-stats-to " <> tmpFileForStats
                                <> _VERIFY_OPTS_
                                <> " < " <> (T.pack $ show $ trAsText)
                                <> " > " <> logFile
                                <> " 2>&1"
                       echo cmdToExecute
                       exitCode <- shell cmdToExecute Turtle.empty
                       case exitCode of
                         ExitFailure ec -> do
                             echo $ "vvt-verify exited with exit-code " <> (T.pack $ show ec)
                                 <> " on benchmark: " <> (T.pack $ show bench)
                             return (accumulatedStats, n+1)
                         ExitSuccess -> do
                             statsAsByteString <- BS.readFile (T.unpack tmpFileForStats)
                             let mStats = Y.decode statsAsByteString
                             case mStats of
                               Just newStats -> do
                                   append resultsFile $ select $
                                          fmap T.pack [ ("benchmark " ++ (show n)
                                                        ++ ": " ++ (show (benchName bench))
                                                        )
                                                      , (show newStats)
                                                      ]
                                   return (addToAccumulatedStats newStats accumulatedStats, n+1)
                               Nothing -> fail "could not parse stats file"
                                                )
                ) (emptyIC3MRStats, 1) benchmarks :: IO (IC3MachineReadableStats, Int)

      append resultsFile $ select $
          fmap T.pack ["mean values over all benchmarks:"
                      , meanValsPrettyString accumStats (length benchmarks)
                      ]

safeToText :: FilePath -> T.Text
safeToText = format fp

addToAccumulatedStats ::
       IC3MachineReadableStats
    -> IC3MachineReadableStats
    -> IC3MachineReadableStats
addToAccumulatedStats newStats accumStats =
    let addToAccumStats field = (field newStats) + (field accumStats)
    in
      IC3MachineReadableStats
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


meanValsPrettyString :: IC3MachineReadableStats -> Int -> String
meanValsPrettyString stats benchmarkCount =
    let calcMean field = (field stats) / (fromIntegral benchmarkCount) :: Float
        showMean val = showFFloat Nothing (calcMean val) ""
    in    ("totalTime: " ++ showMean mrs_totalTime ++ "\n"
        ++ "consecutionTime: " ++ showMean mrs_consecutionTime ++ "\n"
        ++ "consecutionNum: " ++ showMean (fromIntegral . mrs_consecutionNum) ++ "\n"
        ++ "domainTime:" ++ showMean mrs_domainTime ++ "\n"
        ++ "domainNum:" ++ showMean (fromIntegral . mrs_domainNum) ++ "\n"
        ++ "interpolationTime:" ++ showMean mrs_interpolationTime ++ "\n"
        ++ "interpolationNum:" ++ showMean (fromIntegral . mrs_interpolationNum) ++ "\n"
        ++ "liftingTime:" ++ showMean mrs_liftingTime ++ "\n"
        ++ "liftingNum:" ++ showMean (fromIntegral . mrs_liftingNum) ++ "\n"
        ++ "initiationTime:" ++ showMean mrs_initiationTime ++ "\n"
        ++ "initiationNum:" ++ showMean (fromIntegral . mrs_initiationNum) ++ "\n"
        ++ "numErased:" ++ showMean (fromIntegral . mrs_numErased) ++ "\n"
        ++ "numCTI:" ++ showMean (fromIntegral . mrs_numCTI) ++ "\n"
        ++ "numUnliftedErased:" ++ showMean (fromIntegral . mrs_numUnliftedErased) ++ "\n"
        ++ "numCTG:" ++ showMean (fromIntegral . mrs_numCTG) ++ "\n"
        ++ "numMIC:" ++ showMean (fromIntegral . mrs_numMIC) ++ "\n"
        ++ "numCoreReduced:" ++ showMean (fromIntegral . mrs_numCoreReduced) ++ "\n"
        ++ "numAbortJoin:" ++ showMean (fromIntegral . mrs_numAbortJoin) ++ "\n"
        ++ "numAbortMic:" ++ showMean (fromIntegral . mrs_numAbortMic) ++ "\n"
        ++ "numRefinements:" ++ showMean (fromIntegral . mrs_numRefinements) ++ "\n"
        ++ "numAddPreds:" ++ showMean (fromIntegral . mrs_numAddPreds) ++ "\n"
        ++ "numPreds:" ++ showMean (fromIntegral . mrs_numPreds) ++ "\n"
          )
