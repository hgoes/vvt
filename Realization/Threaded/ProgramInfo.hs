{-# LANGUAGE ViewPatterns,ScopedTypeVariables #-}
module Realization.Threaded.ProgramInfo where

import Realization.Threaded.ThreadFinder
import Realization.Threaded.Slicing (getSlicing)

import LLVM.FFI
import Foreign.Ptr (Ptr,nullPtr)
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map

data ThreadInfo = ThreadInfo { blockOrder :: [(Ptr BasicBlock,Int)]
                             , entryPoints :: Map (Ptr BasicBlock,Int) ()
                             , threadArg :: Maybe (Ptr Argument,Ptr Type)
                             , spawnQuantity :: Quantity
                             }

data AllocInfo = AllocInfo { allocQuantity :: Quantity }

data ProgramInfo = ProgramInfo { mainThread :: ThreadInfo
                               , threads :: Map (Ptr CallInst) ThreadInfo
                               , allocations :: Map (Ptr AllocaInst) AllocInfo
                               }

getProgramInfo :: Ptr Module -> Ptr Function -> IO ProgramInfo
getProgramInfo mod mainFun = do
  (entries,order) <- getSlicing mainFun
  mainLocs <- getThreadSpawns' mod mainFun
  applyLocs mainLocs
    (ProgramInfo { mainThread = ThreadInfo { blockOrder = order
                                           , entryPoints = entries
                                           , threadArg = Nothing
                                           , spawnQuantity = Finite 1 }
                 , threads = Map.empty
                 , allocations = Map.empty })
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
           (entries,order) <- getSlicing fun
           nlocs <- getThreadSpawns' mod fun
           arg <- getThreadArgument fun
           applyLocs (locs++(fmap (\l -> l { quantity = (quantity l)*n }) nlocs))
             (pi { threads = Map.insert inst (ThreadInfo { blockOrder = order
                                                         , entryPoints = entries
                                                         , threadArg = arg
                                                         , spawnQuantity = n })
                             (threads pi) })
    applyLocs ((AllocationLocation { allocInstruction = inst
                                   , quantity = n }):locs) pi
      = applyLocs locs (pi { allocations = Map.insert inst (AllocInfo n)
                                           (allocations pi) })
