import HSBencher

to :: Int
to = 500

main = do
  benchmarks <- readFile "benchmarks"
  defaultMainWithBechmarks
       [Benchmark { target = "../ic3.cabal"
                  , cmdargs = ["-t",show (to+5)++"s"]
                  , configs = Or [Set (Variant name) (RuntimeParam $ name++".bc")
                                 | name <- lines benchmarks ]
                  , progname = Just "hctigar"
                  , benchTimeOut = Just (fromIntegral to)
                  }
       ]
