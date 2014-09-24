import HSBencher

main = do
  benchmarks <- readFile "benchmarks"
  defaultMainWithBechmarks
       [Benchmark { target = "../ic3.cabal"
                  , cmdargs = ["-t","4m5s"]
                  , configs = Or [Set (Variant name) (RuntimeParam $ name++".bc")
                                 | name <- lines benchmarks ]
                  , progname = Nothing
                  , benchTimeOut = Just 240
                  }
       ]
