import HSBencher

main = do
  benchmarks <- readFile "benchmarks"
  defaultMainWithBechmarks
       [mkBenchmark "../ic3.cabal" []
        (Or [Set (Variant name) (RuntimeParam $ name++".bc")
            | name <- lines benchmarks ])
       ]
