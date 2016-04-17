{-# LANGUAGE ViewPatterns,ScopedTypeVariables #-}
module Realization.Threaded.ProgramInfo where

import Realization.Threaded.ThreadFinder
import Realization.Threaded.Slicing (getSlicing)

import LLVM.FFI
import Foreign.Ptr (Ptr)
import Data.Map (Map)
import qualified Data.Map as Map
import Text.Show
import System.IO.Unsafe

data ThreadInfo = ThreadInfo { blockOrder :: [(Ptr BasicBlock,Int)]
                             , entryPoints :: Map (Ptr BasicBlock,Int) ()
                             , threadFunction :: Ptr Function
                             , threadArg :: Maybe (Ptr Argument,Either (Ptr Type) (Ptr IntegerType))
                             , threadSliceMapping :: Map Integer [(Ptr BasicBlock,Int)]
                             , spawnQuantity :: Quantity
                             }

data AllocInfo = AllocInfo { allocQuantity :: Quantity
                           , allocType :: AllocKind
                           , allocSize :: Maybe (Ptr Value) } deriving Show

data ProgramInfo = ProgramInfo { mainThread :: ThreadInfo
                               , threads :: Map (Ptr CallInst) ThreadInfo
                               , allocations :: Map (Ptr Instruction) AllocInfo
                               , functionReturns :: Map (Ptr Function) (Ptr Type)
                               } deriving Show

getProgramInfo :: Ptr Module -> Ptr Function -> IO ProgramInfo
getProgramInfo mod mainFun = do
  (entries,order,slMp) <- getSlicing mainFun
  mainLocs <- getThreadSpawns' mod mainFun
  applyLocs mainLocs
    (ProgramInfo { mainThread = ThreadInfo { blockOrder = order
                                           , entryPoints = entries
                                           , threadFunction = mainFun
                                           , threadArg = Nothing
                                           , threadSliceMapping = slMp
                                           , spawnQuantity = Finite 1 }
                 , threads = Map.empty
                 , allocations = Map.empty
                 , functionReturns = Map.empty })
  where
    applyLocs [] pi = return pi
    applyLocs ((ThreadSpawnLocation { spawningInstruction = inst
                                    , spawnedFunction = fun
                                    , quantity = n }):locs) pi
      = case Map.lookup inst (threads pi) of
         Just ti -> applyLocs locs $ pi { threads = Map.insert inst
                                                    (ti { spawnQuantity = (spawnQuantity ti)+n })
                                                    (threads pi) }
         Nothing -> do
           (entries,order,slMp) <- getSlicing fun
           nlocs <- getThreadSpawns' mod fun
           arg <- getThreadArgument fun
           applyLocs (locs++(fmap (updateQuantity (*n)) nlocs))
             (pi { threads = Map.insert inst (ThreadInfo { blockOrder = order
                                                         , entryPoints = entries
                                                         , threadFunction = fun
                                                         , threadArg = arg
                                                         , threadSliceMapping = slMp
                                                         , spawnQuantity = n })
                             (threads pi) })
    applyLocs ((AllocationLocation { allocInstruction = inst
                                   , quantity = n
                                   , allocType' = tp
                                   , allocSize' = sz }):locs) pi
      = applyLocs locs (pi { allocations = Map.insert inst (AllocInfo n tp sz)
                                           (allocations pi) })
    applyLocs ((ReturnLocation { returningFunction = fun
                               , returnedType = tp
                               }):locs) pi
      = applyLocs locs (pi { functionReturns = Map.insertWith
                                               (\tp1 tp2 -> if tp1==tp2
                                                            then tp1
                                                            else error $ "vvt-enc: Conflicting return types in thread.")
                                               fun tp
                                               (functionReturns pi)
                           })

instance Show ThreadInfo where
  showsPrec p ti = showParen (p>10) $
    showString "ThreadInfo {blockOrder = " .
    showListWith (\(blk,n) -> showChar '(' .
                              showValue blk .
                              showChar ',' .
                              showsPrec 0 n .
                              showChar ')') (blockOrder ti) .
    showString ", entryPoints = " .
    showListWith (\(blk,n) -> showChar '(' .
                              showValue blk .
                              showChar ',' .
                              showsPrec 0 n .
                              showChar ')') (Map.keys (entryPoints ti)) .
    showString ", threadFunction = " .
    showValue (threadFunction ti) .
    showString ", threadArg = " .
    showsPrec 1 (threadArg ti) .
    showString ", threadSliceMapping = " .
    showsPrec 1 (threadSliceMapping ti) .
    showString ", spawnQuantity = " .
    showsPrec 1 (spawnQuantity ti) .
    showChar '}'
    where
      showValue :: ValueC v => Ptr v -> ShowS
      showValue = showString . unsafePerformIO . getNameString
