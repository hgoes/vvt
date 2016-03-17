module BackendOptions where

import Data.Map (Map)
import qualified Data.Map as Map
import System.IO
import Control.Monad.Trans

import Language.SMTLib2.Internals.Backend (Backend,SMTMonad)
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Debug (DebugBackend,namedDebugBackend,debugBackend')
#ifdef NATIVE_Z3
import Language.SMTLib2.Z3 (z3Solver)
#endif
#ifdef NATIVE_MATHSAT
import Language.SMTLib2.MathSAT (mathsatBackend)
#endif

data BackendType = ConsecutionBackend
                 | Lifting
                 | Domain
                 | Base
                 | Initiation
                 | Interpolation
                 deriving (Eq,Ord)

data BackendUse = BackendPipe String [String]
                | NativeZ3
                | NativeMathSAT

data BackendDebug = DebugPipe
                  | DebugFile FilePath

data BackendOptions = BackendOptions { optBackend :: Map BackendType BackendUse
                                     , optDebugBackend :: Map BackendType BackendDebug
                                     }

instance Show BackendType where
  show ConsecutionBackend = "cons"
  show Lifting = "lifting"
  show Domain = "domain"
  show Initiation = "init"
  show Interpolation = "interp"
  show Base = "base"

instance Read BackendType where
  readsPrec _ ('c':'o':'n':'s':rest) = [(ConsecutionBackend,rest)]
  readsPrec _ ('l':'i':'f':'t':'i':'n':'g':rest) = [(Lifting,rest)]
  readsPrec _ ('d':'o':'m':'a':'i':'n':rest) = [(Domain,rest)]
  readsPrec _ ('i':'n':'i':'t':rest) = [(Initiation,rest)]
  readsPrec _ ('i':'n':'t':'e':'r':'p':rest) = [(Interpolation,rest)]
  readsPrec _ ('b':'a':'s':'e':rest) = [(Base,rest)]
  readsPrec _ _ = []

instance Show BackendUse where
  show (BackendPipe name opts) = "pipe:"++unwords (name:opts)
  show NativeZ3 = "Z3"
  show NativeMathSAT = "MathSAT"

instance Read BackendUse where
  readsPrec _ ('p':'i':'p':'e':':':(words -> name:opts))
    = [(BackendPipe name opts,[])]
  readsPrec _ "Z3" = [(NativeZ3,[])]
  readsPrec _ "MathSAT" = [(NativeMathSAT,[])]
  readsPrec _ (words -> name:opts) = [(BackendPipe name opts,[])]

readBackendDebug :: ReadS (BackendType,BackendDebug)
readBackendDebug str0 = [ ((tp,dbg),str2)
                        | (tp,str1) <- readsPrec 0 str0
                        , (dbg,str2) <- case str1 of
                            "" -> [(DebugPipe,"")]
                            ':':file -> [(DebugFile file,"")]
                            _ -> [(DebugPipe,str1)] ]

defaultBackendOptions :: BackendOptions
defaultBackendOptions
  = BackendOptions { optBackend = Map.fromList
                                  [(ConsecutionBackend,z3)
                                  ,(Lifting,z3)
                                  ,(Domain,z3)
                                  ,(Base,z3)
                                  ,(Initiation,z3)
                                  ,(Interpolation,mathsat)]
                   , optDebugBackend = Map.empty }
  where
#ifdef NATIVE_Z3
    z3 = NativeZ3
#else
    z3 = BackendPipe "z3" ["-smt2","-in"]
#endif
#ifdef NATIVE_MATHSAT
    mathsat = NativeMathSAT
#else
    mathsat = BackendPipe "mathsat" ["-random_seed=1"]
#endif

setBackend :: BackendType -> BackendUse -> BackendOptions -> BackendOptions
setBackend tp solver opts = opts { optBackend = Map.insert tp solver
                                                (optBackend opts)
                                 }

setDebugBackend :: BackendType -> BackendDebug -> BackendOptions -> BackendOptions
setDebugBackend tp dbg opts = opts { optDebugBackend = Map.insert tp dbg
                                                       (optDebugBackend opts)
                                   }

createBackend :: BackendUse -> (forall b. (Backend b,SMTMonad b ~ IO) => IO b -> a)
              -> a
createBackend (BackendPipe name args) f = f (createPipe name args)
#ifdef NATIVE_Z3
createBackend NativeZ3 f = f (return z3Solver)
#else
createBackend NativeZ3 _ = error "Native Z3 support not enabled (build with -fNative-Z3 to enable)."
#endif
#ifdef NATIVE_MATHSAT
createBackend NativeMathSAT f = f (return mathsatBackend)
#else
createBackend NativeMathSAT _ = error "Native MathSAT support not enabled (build with -fNative-MathSAT to enable)."
#endif

createDebugBackend :: (Backend b,MonadIO (SMTMonad b))
                   => String -> BackendDebug -> b -> IO (DebugBackend b)
createDebugBackend name DebugPipe b = return $ namedDebugBackend name b
createDebugBackend name (DebugFile fp) b = do
  h <- openFile fp AppendMode
  return $ debugBackend' False False Nothing h b
