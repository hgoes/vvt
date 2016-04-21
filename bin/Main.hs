module Main where

import Paths_vvt

import System.Process
import System.IO
import System.Environment
import System.FilePath
import System.Console.GetOpt
import System.Directory
import Data.Version
import Text.ParserCombinators.ReadP
import Control.Monad.Except
import Data.Char (isDigit)

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
                       , output :: OutputLocation
                       }

data OutputLocation
  = OutputFile FilePath
  | OutputHandle Handle
  | OutputDefault

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
                         , lipton = Nothing
                         , output = OutputDefault }

optDescr :: [OptDescr (Options -> Options)]
optDescr = [Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True }) "Show this help"
           ,Option ['k'] ["karr"] (NoArg $ \opt -> opt { karrAnalysis = True }) "Use Karr analysis to get better predicates"
           ,Option [] ["with-llvm"] (ReqArg (\arg opt -> opt { llvmDir = Just arg }) "path") "The path to the directory containing the LLVM binaries"
           ,Option ['D'] [] (ReqArg (\arg opt -> opt { defines = arg:defines opt }) "VAR[=VAL]") "Define macros for the C-preprocessor"
           ,Option [] ["unroll"] (NoArg $ \opt -> opt { unroll = True }) "Use LLVM to unroll loops"
           ,Option [] ["ineq"] (NoArg $ \opt -> opt { ineqPreds = True }) "Add inequality predicates"
           ,Option [] ["lipton"] (OptArg (\arg opt -> case arg of
                                             Nothing -> opt { lipton = Just "LiptonPass" }
                                             Just bin -> opt { lipton = Just bin }) "path") "Use the lipton reduction tool to annotate parallel programs."
           ,Option ['o'] ["output"] (ReqArg (\arg opt -> opt { output = case arg of
                                                                 "-" -> OutputHandle stdout
                                                                 _ -> OutputFile arg }) "file") "Output file location (Use \"-\" for stdout)."]

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
    let accept v = (v >= makeVersion [3,5]) && (v < makeVersion [3,6])
        wanted = "3.5.*"
    llvm <- case llvmDir opts of
      Just dir -> return (Just dir)
      Nothing -> guessLLVMDir accept ["llvm-config","llvm-config-3.5"]
    res <- runExceptT (verifyLLVMDir wanted accept llvm)
    case res of
      Left err -> error err
      Right () -> return (Just (act,opts { llvmDir = llvm }))

performAction :: (Action,Options) -> IO ()
performAction (Encode fn,opts) = do
  outp <- case output opts of
    OutputDefault -> openFile (replaceExtension fn "l") WriteMode
    OutputFile name -> openFile name WriteMode
    OutputHandle h -> return h
  (inp,_) <- compile opts fn
  let pipe = case lipton opts of
        Nothing -> [progOptimize opts
                   ,progEncode
                   ,progSimplify
                   ,progPredicates opts
                   ,progPretty]
        Just _ -> [progOptimizePreLipton opts
                  ,progLipton opts
                  ,progOptimizePostLipton opts
                  ,progEncode
                  ,progSimplify
                  ,progPredicates opts
                  ,progPretty]
  ph <- execPipe inp outp pipe
  waitForProcess ph
  return ()
performAction (ShowLLVM fn,opts) = do
  (inp,_) <- compile opts fn
  let pipe = case lipton opts of
        Nothing -> [progOptimize opts,progDisassemble opts]
        Just _ -> [progOptimizePreLipton opts
                  ,progLipton opts
                  ,progOptimizePostLipton opts
                  ,progDisassemble opts]
  outh <- case output opts of
    OutputDefault -> return stdout
    OutputFile name -> openFile name WriteMode
    OutputHandle h -> return h
  ph <- execPipe inp outh pipe
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
                           ,"-always-inline"
                           ,"-loops"
                           ,"-loop-simplify"
                           ,"-lcssa"
                           ,"-instsimplify"
                           ,"-instcombine"]++
                           (if unroll opt
                            then ["-loop-unroll"]
                            else [])++
                           ["-instnamer"
                           ,"-","-o","-"])

progOptimizePreLipton :: Options -> IO (FilePath,[String])
progOptimizePreLipton opts
  = return (llvmExec "opt" opts,
            ["-mem2reg"
            ,"-internalize-public-api-list=main"
            ,"-internalize"
            ,"-inline"
            ,"-always-inline"
            ,"-loops"
            ,"-loop-simplify"
            ,"-lcssa"]++
            (if unroll opts
             then ["-loop-unroll"]
             else []))

progOptimizePostLipton :: Options -> IO (FilePath,[String])
progOptimizePostLipton opts
  = return (llvmExec "opt" opts,
            ["-mem2reg"
            ,"-constprop"
            ,"-instsimplify"
            ,"-instcombine"
            ,"-correlated-propagation"
            ,"-die"
            ,"-simplifycfg"
            ,"-globaldce"
            ,"-instnamer"])

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

verifyLLVMDir :: String -> (Version -> Bool) -> Maybe FilePath -> ExceptT String IO ()
verifyLLVMDir wanted accept fp = do
  check "clang"
  check "opt"
  check "llvm-as"
  check "llvm-dis"
  where
    check :: String -> ExceptT String IO ()
    check name = do
      exec <- bin name
      vers <- lift $ versionFromBinary exec
      case vers of
        Nothing -> throwError $ "Cannot determine version of "++show exec++" binary "++hint
        Just vers' -> if accept vers'
                      then return ()
                      else throwError $ "Version "++showVersion vers'++" of "++show exec++" binary is not acceptable, "++wanted++" is required "++hint
    bin :: String -> ExceptT String IO FilePath
    bin name = case fp of
      Nothing -> do
        exec <- lift $ findExecutable name
        case exec of
          Nothing -> throwError $ "Binary "++show name++" not found "++hint
          Just exec' -> return exec'
      Just fp' -> return $ fp' </> name
    hint = "(Use --with-llvm=... to specify the path where it can be found."
      
guessLLVMDir :: (Version -> Bool) -> [String] -> IO (Maybe FilePath)
guessLLVMDir accept [] = return Nothing
guessLLVMDir accept (name:names) = do
  exec <- findExecutable name
  case exec of
    Nothing -> guessLLVMDir accept names
    Just exec' -> do
      vers <- versionFromBinary exec'
      case vers of
        Nothing -> guessLLVMDir accept names
        Just v -> if accept v
                  then do
          dir <- readProcess exec' ["--bindir"] ""
          case lines dir of
            [dir'] -> return (Just dir')
            _ -> guessLLVMDir accept names
                  else guessLLVMDir accept names

versionFromBinary :: FilePath -> IO (Maybe Version)
versionFromBinary bin = do
  exists <- doesFileExist bin
  if exists
    then do
    outp <- readProcess bin ["--version"] ""
    case [ vers | ln <- lines outp
                , wrd <- words ln
                , (vers,"") <- readP_to_S parseVersion (takeWhile (\c -> c=='.' || isDigit c) wrd) ] of
      res:_ -> return (Just res)
      [] -> return Nothing
    else return Nothing
