import Data.List

data TestCase = TestCase { name :: String
                         , probeMax :: Int
                         , threads :: [(Int,Bool)]
                         } deriving (Eq,Ord,Show)

data Config = Config { clangBin :: String
                     , liptonBin :: String
                     , optBin :: String
                     , vvtInclude :: String
                     , optPre :: String
                     , optPost :: String
                     , simplification :: String
                     , runs :: Int
                     , flags :: [Maybe String]
                     , timeout :: Maybe String
                     } deriving (Eq,Ord,Show)

defaultConfig :: Config
defaultConfig = Config { clangBin = "clang-3.4"
                       , optBin = "opt-3.5"
                       , liptonBin = "/home/eq/repos/lipton/LiptonPass"
                       , vvtInclude = "../../include"
                       , optPre = "-mem2reg -loops -loop-simplify -loop-rotate -lcssa"
                       , optPost = "-mem2reg -constprop -instsimplify -correlated-propagation -die -simplifycfg -globaldce -instnamer"
                       , simplification = "simplify inline slice value-set=2 simplify inline"
                       , runs = 4
                       , flags = [Nothing,Just "n",Just "l"]
                       , timeout = Just "15m"
                       }

mkCLang :: TestCase -> String
mkCLang tc = "$(CLANG) -I$(VVT_INCLUDE) -O0 -emit-llvm -c dynlocks.cpp -o - -DPROBE_MAX="++
             show (probeMax tc)++
             " -DSEQUENCE=\""++
             foldl (\seq (val,lock) -> "SPAWN("++show val++","++(if lock then "true" else "false")++","++seq++")"
                   ) "0" (threads tc)++
             "\""

mkVars :: Config -> String
mkVars cfg = unlines ["CLANG="++clangBin cfg
                     ,"OPT="++optBin cfg
                     ,"LIPTON="++liptonBin cfg
                     ,"VVT_INCLUDE="++vvtInclude cfg
                     ,"OPT_PRE="++optPre cfg
                     ,"OPT_POST="++optPost cfg
                     ,"SIMPLIFICATION="++simplification cfg]

flagName :: Maybe String -> TestCase -> String -> String
flagName flag tc post
  = name tc++"."++
    (case flag of
      Nothing -> ""
      Just f -> f++".")++post

mkCompile :: Maybe String -> TestCase -> String
mkCompile flag tc
  = unlines [flagName flag tc "l"++": dynlocks.cpp"
            ,"\t"++mkCLang tc++" |\\"
            ,"\t  vvt-svcomp inline |\\"
            ,"\t  $(OPT) $(OPT_PRE) |\\"
            ,"\t  $(LIPTON)"++
             (case flag of
               Nothing -> ""
               Just f -> " -"++f)++
             " |\\"
            ,"\t  $(OPT) $(OPT_POST) |\\"
            ,"\t  vvt-enc |\\"
            ,"\t  vvt-opt $(SIMPLIFICATION) |\\"
            ,"\t  vvt-predicates -ioff -bon |\\"
            ,"\t  vvt-pp > "++flagName flag tc "l"]

allLisp :: Config -> [TestCase] -> String
allLisp cfg cases = unwords [ flagName flag tc "l"
                            | tc <- cases
                            , flag <- flags cfg]

allOutputIC3 :: Config -> [TestCase] -> String
allOutputIC3 cfg cases
  = unwords [ flagName flag tc (show run++".output-ic3")
            | tc <- cases
            , flag <- flags cfg
            , run <- [0..(runs cfg)-1]]

allOutputBMC :: Config -> [TestCase] -> String
allOutputBMC cfg cases
  = unwords [ flagName flag tc (show run++".output-bmc")
            | tc <- cases
            , flag <- flags cfg
            , run <- [0..(runs cfg)-1]]

mkIC3 :: Config -> Int -> Maybe String -> TestCase -> String
mkIC3 cfg run flag tc
  = unlines [oname++": "++flagName flag tc "l"
            ,"\tvvt-verify --stats"++
             (case timeout cfg of
               Nothing -> ""
               Just to -> " --timeout="++to)++
             " < "++flagName flag tc "l"++" > "++oname]
  where
    oname = flagName flag tc (show run++".output-ic3")

mkBMC :: Config -> Int -> Maybe String -> TestCase -> String
mkBMC cfg run flag tc
  = unlines [oname++": "++flagName flag tc "l"
            ,"\tvvt-bmc -d -1 -i -t -c"++
             (case timeout cfg of
               Nothing -> ""
               Just to -> " --timeout="++to)++
             " < "++flagName flag tc "l"++" > "++oname]
  where
    oname = flagName flag tc (show run++".output-bmc")

mkResults :: Config -> Maybe String -> String -> [TestCase] -> String
mkResults cfg flag post cases
  = unlines [fn++": "++files
            ,"\t./extracts.sh "++show (runs cfg)++" "++post++" "++
             intercalate " " [ name tc++(case flag of
                                          Nothing -> ""
                                          Just f -> "."++f)
                             | tc <- cases ]++" > "++fn
            ]
  where
    sflag = case flag of
      Nothing -> ""
      Just f -> "-"++f
    fn = "results-"++post++sflag
    files = intercalate " " [ flagName flag tc (show run++".output-"++post)
                            | tc <- cases
                            , run <- [0..runs cfg-1] ]
      
mkMake :: Config -> [TestCase] -> IO ()
mkMake cfg cases = do
  putStrLn $ mkVars cfg
  putStrLn $ "ALL: "++allLisp cfg cases
  putStrLn $ "output-ic3: "++allOutputIC3 cfg cases
  putStrLn $ "output-bmc: "++allOutputBMC cfg cases
  putStrLn "include extra.mk"
  putStrLn ""
  putStrLn "clean:"
  putStrLn $ "\trm -f "++allLisp cfg cases++" "++
    allOutputIC3 cfg cases++" "++
    allOutputBMC cfg cases
  putStrLn ""
  mapM_ (\flag -> do
            putStrLn $ mkResults cfg flag "ic3" cases
            putStrLn ""
            putStrLn $ mkResults cfg flag "bmc" cases
            putStrLn ""
        ) (flags cfg)
  mapM_ (\tc -> mapM_ (\flag -> do
                          putStrLn $ mkCompile flag tc
                          mapM_ (\n -> putStrLn $ mkIC3 cfg n flag tc
                                ) [0..runs cfg]
                          mapM_ (\n -> putStrLn $ mkBMC cfg n flag tc
                                ) [0..runs cfg]
                      ) (flags cfg)
        ) cases

cases :: [TestCase]
cases = [TestCase { name = "t"++show n++"-probe"++show pm
                  , probeMax = pm
                  , threads = take n $ zip [0..] (cycle [True,False])
                  }
        | pm <- [1..4]
        , n <- [1..4] ]

main = mkMake defaultConfig cases
