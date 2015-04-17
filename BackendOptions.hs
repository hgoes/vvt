module BackendOptions where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set

data BackendType = ConsecutionBackend
                 | Lifting
                 | Domain
                 | Base
                 | Initiation
                 | Interpolation
                 deriving (Eq,Ord)

data BackendOptions = BackendOptions { optBackend :: Map BackendType String
                                     , optDebugBackend :: Set BackendType
                                     }

instance Show BackendType where
  show ConsecutionBackend = "cons"
  show Lifting = "lifting"
  show Domain = "domain"
  show Initiation = "init"
  show Interpolation = "interp"

instance Read BackendType where
  readsPrec _ ('c':'o':'n':'s':rest) = [(ConsecutionBackend,rest)]
  readsPrec _ ('l':'i':'f':'t':'i':'n':'g':rest) = [(Lifting,rest)]
  readsPrec _ ('d':'o':'m':'a':'i':'n':rest) = [(Domain,rest)]
  readsPrec _ ('i':'n':'i':'t':rest) = [(Initiation,rest)]
  readsPrec _ ('i':'n':'t':'e':'r':'p':rest) = [(Interpolation,rest)]
  readsPrec _ _ = []

defaultBackendOptions :: BackendOptions
defaultBackendOptions
  = BackendOptions { optBackend = Map.fromList
                                  [(ConsecutionBackend,z3)
                                  ,(Lifting,z3)
                                  ,(Domain,z3)
                                  ,(Base,z3)
                                  ,(Initiation,z3)
                                  ,(Interpolation,mathsat)]
                   , optDebugBackend = Set.empty }
  where
    z3 = "z3 -smt2 -in"
    mathsat = "mathsat"

setBackend :: BackendType -> String -> BackendOptions -> BackendOptions
setBackend tp solver opts = opts { optBackend = Map.insert tp solver
                                                (optBackend opts)
                                 }

setDebugBackend :: BackendType -> BackendOptions -> BackendOptions
setDebugBackend tp opts = opts { optDebugBackend = Set.insert tp
                                                   (optDebugBackend opts)
                               }
