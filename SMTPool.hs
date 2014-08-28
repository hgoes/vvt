{-# LANGUAGE ExistentialQuantification,FlexibleContexts #-}
module SMTPool where

import Language.SMTLib2
import Language.SMTLib2.Connection

import Data.Pool

data SMTInstance a = forall b. SMTBackend b IO =>
                     SMTInstance { instanceConn :: SMTConnection b
                                 , instanceVars :: a
                                 }

type SMTPool a = Pool (SMTInstance a)

createSMTPool :: SMTBackend b IO
                 => IO b
                 -> SMT a
                 -> IO (SMTPool a)
createSMTPool createBackend act
  = createPool (do
                   b <- createBackend
                   conn <- open b
                   vars <- performSMT conn act
                   return $ SMTInstance conn vars)
    (\(SMTInstance { instanceConn = conn }) -> close conn)
    1 5 10

withSMTPool :: SMTPool a -> (a -> SMT b) -> IO b
withSMTPool pool act
  = withResource pool $
    \(SMTInstance { instanceConn = conn
                  , instanceVars = vars })
    -> performSMT conn (act vars)
