{-# LANGUAGE ExistentialQuantification,FlexibleContexts #-}
module SMTPool where

import Language.SMTLib2.LowLevel
import Language.SMTLib2.Internals.Backend
--import Language.SMTLib2.Connection

import Data.Pool
import Control.Exception
import Control.Monad.State.Strict

data SMTInstance info b a = SMTInstance { instanceState :: SMTState b
                                        , instanceVars :: a (Expr b)
                                        , instanceInfo :: info
                                        }

type SMTPool info b a = Pool (SMTInstance info b a)

createSMTPool :: (Backend b,SMTMonad b ~ IO)
              => IO b
              -> SMT b (a (Expr b))
              -> IO (SMTPool () b a)
createSMTPool backend act = createSMTPool' backend () act

createSMTPool' :: (Backend b,SMTMonad b ~ IO)
               => IO b
               -> info
               -> SMT b (a (Expr b))
               -> IO (SMTPool info b a)
createSMTPool' createBackend info (SMT act)
  = createPool (do
                   b <- createBackend
                   let st0 = SMTState b emptyDatatypeInfo
                   (vars,st1) <- (runStateT act st0) `onException`
                                 (exit b)
                   return $ SMTInstance st1 vars info)
    (\(SMTInstance { instanceState = st }) -> exit (backend st))
    1 5 10

withSMTPool :: (Backend b,SMTMonad b ~ IO) => SMTPool info b a -> (a (Expr b) -> SMT b c) -> IO c
withSMTPool pool act = do
  Right res <- withSMTPool' pool (\info vars -> do
                                     res <- act vars
                                     return (Right (res,info)))
  return res

withSMTPool' :: (Backend b,SMTMonad b ~ IO) => SMTPool info b a
             -> (info -> a (Expr b) -> SMT b (Either c (r,info)))
             -> IO (Either c r)
withSMTPool' pool act = do
  (inst@SMTInstance { instanceState = st0
                    , instanceVars = vars
                    , instanceInfo = info },local) <- takeResource pool
  (do
      let SMT act' = act info vars
      (res,st1) <- (runStateT act' st0) `onException`
                   (exit $ backend st0)
      case res of
       Left x -> do
         destroyResource pool local inst
         return (Left x)
       Right (res,info') -> do
         putResource local (SMTInstance { instanceState = st1
                                        , instanceVars = vars
                                        , instanceInfo = info' })
         return (Right res))
    `onException` (destroyResource pool local inst)
