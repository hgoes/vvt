module Main where

--import Realization.Common
import Realization.Threaded
import Realization.Threaded.Translation
import Realization.Threaded.Options
import Realization.Lisp

import LLVM.FFI
import Foreign.Ptr

defaultOptions :: TranslationOptions
defaultOptions = TranslationOptions { dedicatedErrorState = True
                                    , safeSteps = True
                                    , defaultInit = True }

main = do
  (mod,fun) <- getProgram "main"
  real <- realizeProgramFix defaultOptions mod fun
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
