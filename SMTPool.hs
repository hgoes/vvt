{-# LANGUAGE ExistentialQuantification,FlexibleContexts #-}
module SMTPool where

import Language.SMTLib2.Internals.Backend
import Language.SMTLib2.Internals.Monad

import Data.Pool
import Control.Exception
import Control.Monad.State.Strict

data SMTInstance info b = SMTInstance { instanceState :: SMTState b
                                      , instanceInfo :: info b
                                      }

data SMTPool info = forall b. (Backend b,SMTMonad b ~ IO)
                    => SMTPool (Pool (SMTInstance info b))

newtype PoolVars a b = PoolVars (a (Expr b))

createSMTPool :: (Backend b,SMTMonad b ~ IO)
               => IO b
               -> SMT b (info b)
               -> IO (SMTPool info)
createSMTPool createBackend (SMT info)
  = fmap SMTPool $
    createPool (do
                   b <- createBackend
                   let st0 = SMTState b emptyDatatypeInfo
                   (info',st1) <- (runStateT info st0) `onException`
                                  (exit b)
                   return $ SMTInstance st1 info')
    (\(SMTInstance { instanceState = st }) -> exit (backend st) >> return ())
    1 5 10

withSMTPool :: SMTPool info
            -> (forall b. Backend b => info b -> SMT b c)
            -> IO c
withSMTPool pool act = do
  Right res <- withSMTPool' pool
               (\info -> do
                   res <- act info
                   return (Right (res,info)))
  return res

withSMTPool' :: SMTPool info
             -> (forall b. Backend b => info b -> SMT b (Either c (r,info b)))
             -> IO (Either c r)
withSMTPool' (SMTPool pool) act = do
  (inst@SMTInstance { instanceState = st0
                    , instanceInfo = info },local) <- takeResource pool
  (do
      let SMT act' = act info
      (res,st1) <- (runStateT act' st0) `onException`
                   (exit $ backend st0)
      case res of
       Left x -> do
         destroyResource pool local inst
         return (Left x)
       Right (res,info') -> do
         putResource local (SMTInstance { instanceState = st1
                                        , instanceInfo = info' })
         return (Right res))
    `onException` (destroyResource pool local inst)
