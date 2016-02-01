module Main where

import Paths_vvt

import System.Process
import System.IO
import System.Environment
import System.FilePath
import System.Console.GetOpt

data Action = Verify FilePath
            | Encode FilePath
            | ShowLLVM FilePath

data Options = Options { karrAnalysis :: Bool
                       , showHelp :: Bool
                       , defines :: [String]
                       , llvmDir :: Maybe String
                       , unroll :: Bool
                       , ineqPreds :: Bool
                       , lipton :: Maybe String
                       }

llvmExec :: String -> Options -> String
llvmExec bin opts = case llvmDir opts of
  Nothing -> bin
  Just dir -> dir </> bin

defaultOptions :: Options
defaultOptions = Options { karrAnalysis = False
                         , showHelp = False
                         , defines = []
                         , llvmDir = Nothing
                         , unroll = False
                         , ineqPreds = False
                         , lipton = Nothing }

optDescr :: [OptDescr (Options -> Options)]
optDescr = [Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True }) "Show this help"
           ,Option ['k'] ["karr"] (NoArg $ \opt -> opt { karrAnalysis = True }) "Use Karr analysis to get better predicates"
           ,Option [] ["with-llvm"] (ReqArg (\arg opt -> opt { llvmDir = Just arg }) "path") "The path to the directory containing the LLVM binaries"
           ,Option ['D'] [] (ReqArg (\arg opt -> opt { defines = arg:defines opt }) "VAR[=VAL]") "Define macros for the C-preprocessor"
           ,Option [] ["unroll"] (NoArg $ \opt -> opt { unroll = True }) "Use LLVM to unroll loops"
           ,Option [] ["ineq"] (NoArg $ \opt -> opt { ineqPreds = True }) "Add inequality predicates"
           ,Option [] ["lipton"] (OptArg (\arg opt -> case arg of
                                             Nothing -> opt { lipton = Just "LiptonPass" }
                                             Just bin -> opt { lipton = Just bin }) "path") "Use the lipton reduction tool to annotate parallel programs."]

getAction :: IO (Maybe (Action,Options))
getAction = do
  args <- getArgs
  let (xs,extra,errs) = getOpt Permute optDescr args
      opts = foldl (flip id) defaultOptions xs
  if showHelp opts
    then do
    putStrLn $ usageInfo "Usage:\n\n    vvt ACTION [OPTIONS] [FILE..]\n\nAvailable actions:\n  encode - Create a transition relation from a C file.\n  show-llvm - Show the LLVM code that is used for the translation.\n\nAvailable options:" optDescr
    return Nothing
    else do
    act <- case extra of
            [] -> error "Please provide an action."
            "verify":rest -> case rest of
              [] -> error "Please provide a C-file to verify."
              [file] -> return (Encode file)
            "encode":rest -> case rest of
              [] -> error "Please provide a C-file to encode."
              [file] -> return (Encode file)
            "show-llvm":rest -> case rest of
              [] -> error "Please provide a C-file to compile."
              [file] -> return (ShowLLVM file)
            (x:_) -> error $ "Unknown action "++show x++"."
    return (Just (act,opts))

performAction :: (Action,Options) -> IO ()
performAction (Encode fn,opts) = do
  outp <- openFile (replaceExtension fn "l") WriteMode
  (inp,_) <- compile opts fn
  let pipe = case lipton opts of
        Nothing -> [progOptimize opts
                   ,progEncode
                   ,progSimplify
                   ,progPredicates opts
                   ,progPretty]
        Just _ -> [return (llvmExec "opt" opts,
                           ["-mem2reg"
                           ,"-internalize-public-api-list=main"
                           ,"-internalize"
                           ,"-inline"
                           ,"-loops"
                           ,"-loop-simplify"
                           ,"-loop-rotate"
                           ,"-lcssa"]++
                           (if unroll opts
                            then ["-loop-unroll"]
                            else []))
                  ,progLipton opts
                  ,return (llvmExec "opt" opts,
                           ["-mem2reg"
                           ,"-constprop"
                           ,"-instsimplify"
                           ,"-instcombine"
                           ,"-correlated-propagation"
                           ,"-die"
                           ,"-simplifycfg"
                           ,"-globaldce"
                           ,"-instnamer"])
                  ,progEncode
                  ,progSimplify
                  ,progPredicates opts
                  ,progPretty]
  ph <- execPipe inp outp pipe
  waitForProcess ph
  return ()
performAction (ShowLLVM fn,opts) = do
  (inp,_) <- compile opts fn
  ph <- execPipe inp stdout [progOptimize opts,progDisassemble opts]
  waitForProcess ph
  return ()

main :: IO ()
main = do
  act <- getAction
  case act of
   Nothing -> return ()
   Just act -> performAction act

execPipe :: Handle -> Handle -> [IO (FilePath,[String])] -> IO ProcessHandle
execPipe inp outp [act] = do
  (prog,args) <- act
  (_,_,_,ph) <- createProcess ((proc prog args) { std_in = UseHandle inp
                                                , std_out = UseHandle outp })
  return ph
execPipe inp outp (act:acts) = do
  (prog,args) <- act
  (_,Just pout,_,ph) <- createProcess ((proc prog args) { std_in = UseHandle inp
                                                        , std_out = CreatePipe })
  execPipe pout outp acts

compile :: Options -> FilePath -> IO (Handle,ProcessHandle)
compile opts fp = do
  includePath <- getDataFileName "include"
  let clang = (proc (llvmExec "clang" opts) $
                    ["-O0","-emit-llvm","-c","-o","-",fp,"-I"++includePath,"-DVVT"]++
                    ["-D"++def | def <- defines opts ]) { std_out = CreatePipe }
  --let clang = (proc "ls" ["-l"]) { std_out = CreatePipe }
  (_,Just pout,_,ph) <- createProcess clang
  return (pout,ph)

progOptimize :: Options -> IO (FilePath,[String])
progOptimize opt = return (llvmExec "opt" opt,
                           ["-mem2reg"
                           ,"-internalize-public-api-list=main"
                           ,"-internalize"
                           ,"-inline"
                           ,"-loops"
                           ,"-loop-simplify"
                           ,"-loop-rotate"
                           ,"-lcssa"
                           ,"-instsimplify"
                           ,"-instcombine"]++
                           (if unroll opt
                            then ["-loop-unroll"]
                            else [])++
                           ["-instnamer"
                           ,"-","-o","-"])

progDisassemble :: Options -> IO (FilePath,[String])
progDisassemble opts = return (llvmExec "llvm-dis" opts,["-","-o","-"])

progEncode :: IO (FilePath,[String])
progEncode = do
  bin <- getBinDir
  return (bin </> "vvt-enc",[])

progPredicates :: Options -> IO (FilePath,[String])
progPredicates opts = do
  bin <- getBinDir
  return (bin </> "vvt-predicates",
          (if karrAnalysis opts then ["--karr=on"] else ["--karr=off"])++
          (if ineqPreds opts then ["--ineq=on"] else ["--ineq=off"]))

progVerify :: IO (FilePath,[String])
progVerify = do
  bin <- getBinDir
  return (bin </> "vvt-verify",["-v2"])

progPretty :: IO (FilePath,[String])
progPretty = do
  bin <- getBinDir
  return (bin </> "vvt-pp",[])

progSimplify :: IO (FilePath,[String])
progSimplify = do
  bin <- getBinDir
  return (bin </> "vvt-opt",[])

progLipton :: Options -> IO (FilePath,[String])
progLipton opts = case lipton opts of
  Just cmd -> let bin:args = words cmd in return (bin,args)
  Nothing -> return ("LiptonPass",[])
