import HSBencher

to :: Int
to = 500

main = do
  benchmarks <- readFile "benchmarks"
  defaultMainWithBechmarks
       [Benchmark { target = "../ic3.cabal"
                  , cmdargs = ["-t",show (to+5)++"s"]
                  , configs = Or [Set (Variant (name++","++senc++sopt)) (RuntimeParam $ name++".bc -E "++enc++opt)
                                 | name <- lines benchmarks
                                 , (enc,senc) <- [("monolithic","mono")
                                                 ,("blockwise","blk")]
                                 , (opt,sopt) <- [(" -O",",opt")
                                                 ,("","")]]
                  , progname = Just "hctigar"
                  , benchTimeOut = Just (fromIntegral to)
                  }
       ]
