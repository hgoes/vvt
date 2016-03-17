module Main where

--import Realization.Common
import Realization.Threaded
import Realization.Threaded.Translation
import Realization.Threaded.Options
import Realization.Lisp

import LLVM.FFI
import Foreign.Ptr
import System.Console.GetOpt
import System.Environment

defaultOptions :: TranslationOptions
defaultOptions = TranslationOptions { dedicatedErrorState = True
                                    , safeSteps = True
                                    , defaultInit = True
                                    , bitPrecise = False
                                    , showHelp = False }

optDescr :: [OptDescr (TranslationOptions -> TranslationOptions)]
optDescr = [Option [] ["bitprecise"] (NoArg $ \opt -> opt { bitPrecise = True })
            "Use bitvectors instead of linear integers"
           ,Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True })
            "Show this documentation."]

main = do
  args <- getArgs
  let (xs,extra,errs) = getOpt Permute optDescr args
  case extra of
   [] -> return ()
   _ -> error $ "Unknown arguments: "++show extra
  case errs of
   [] -> return ()
   _ -> error $ "Error while parsing arguments: "++unlines errs
  let opts = foldl (flip id) defaultOptions xs
  if showHelp opts
    then putStrLn $ usageInfo "Usage:\n\n    vvt-enc [OPTIONS] < program.bc \n\nAvailable options:" optDescr
    else do
      (mod,fun) <- getProgram "main"
      real <- realizeProgramFix opts mod fun
      let lisp = toLispProgram real
      print $ programToLisp lisp

getProgram :: String -> IO (Ptr Module,Ptr Function)
getProgram entry = do
  loadRes <- getStdInMemoryBufferSimple
  buf <- case loadRes of
    Left err -> error $ "Error while loading bitcode file: "++show err
    Right b -> return b
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  fun <- moduleGetFunctionString mod entry
  return (mod,fun)
