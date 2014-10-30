import HSBencher

to :: Int
to = 500

main = do
  benchmarks <- readFile "benchmarks"
  defaultMainWithBechmarks
       [Benchmark { target = "../ic3.cabal"
                  , cmdargs = ["-t",show (to+5)++"s"]
                  , configs = And [Or [Set (Variant name) (RuntimeParam $ name++".bc")
                                      | name <- lines benchmarks ]
                                  ,Or [Set NoMeaning (RuntimeParam "-E monolithic")
                                      ,Set NoMeaning (RuntimeParam "-E blockwise")]
                                  ,Or [Set NoMeaning (RuntimeParam "-O")
                                      ,Set NoMeaning (RuntimeParam "")]]
                  , progname = Just "hctigar"
                  , benchTimeOut = Just (fromIntegral to)
                  }
       ]
