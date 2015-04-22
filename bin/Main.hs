module Main where

import Paths_hctigar

import System.Process
import System.IO
import System.Environment
import System.FilePath

data Action = Verify FilePath
            | Encode FilePath
            | ShowLLVM FilePath

getAction :: IO Action
getAction = do
  args <- getArgs
  case args of
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

performAction :: Action -> IO ()
performAction (Encode fn) = do
  outp <- openFile (replaceExtension fn "l") WriteMode
  (inp,_) <- compile fn
  ph <- execPipe inp outp [progOptimize,progEncode,progPredicates,progPretty]
  waitForProcess ph
  return ()
performAction (ShowLLVM fn) = do
  (inp,_) <- compile fn
  ph <- execPipe inp stdout [progOptimize,progDisassemble]
  waitForProcess ph
  return ()  

main :: IO ()
main = getAction >>= performAction

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

compile :: FilePath -> IO (Handle,ProcessHandle)
compile fp = do
  includePath <- getDataFileName "include"
  let clang = (proc "clang-3.4" ["-O0","-emit-llvm","-c","-o","-",fp,"-I"++includePath,"-DHCTIGAR"]) { std_out = CreatePipe }
  --let clang = (proc "ls" ["-l"]) { std_out = CreatePipe }
  (_,Just pout,_,ph) <- createProcess clang
  return (pout,ph)

progOptimize :: IO (FilePath,[String])
progOptimize = return ("opt",["-mem2reg","-inline","-loops","-loop-reduce","-loop-unroll","-instnamer","-","-o","-"])

progDisassemble :: IO (FilePath,[String])
progDisassemble = return ("llvm-dis",["-","-o","-"])

progEncode :: IO (FilePath,[String])
progEncode = do
  bin <- getBinDir
  return (bin </> "vvt-enc",[])

progPredicates :: IO (FilePath,[String])
progPredicates = do
  bin <- getBinDir
  return (bin </> "vvt-predicates",[])

progVerify :: IO (FilePath,[String])
progVerify = do
  bin <- getBinDir
  return (bin </> "vvt-verify",["-v2"])

progPretty :: IO (FilePath,[String])
progPretty = do
  bin <- getBinDir
  return (bin </> "vvt-pp",[])
