{-# LANGUAGE ScopedTypeVariables,TypeFamilies #-}
module Realization.Threaded.ThreadFinder where

import LLVM.FFI
import LLVM.FFI.Loop
import Foreign.Ptr (Ptr,nullPtr)

data Quantity = Finite Integer
              | Infinite
              deriving (Show,Eq)

data ThreadLocation = ThreadSpawnLocation { spawningInstruction :: Ptr CallInst
                                          , spawnedFunction :: Ptr Function
                                          , quantity :: Quantity
                                          }
                    | AllocationLocation { allocInstruction :: Ptr AllocaInst
                                         , quantity :: Quantity
                                         }
                    deriving (Show,Eq,Ord)

getThreadSpawns' :: Ptr Module -> Ptr Function -> IO [ThreadLocation]
getThreadSpawns' mod fun = do
  loopInfo <- newLoopInfo
  manager <- newFunctionPassManager mod
  functionPassManagerAdd manager loopInfo
  errors <- functionPassManagerRun manager fun
  if not errors
    then do
    base <- loopInfoGetBase loopInfo
    getThreadSpawns fun base
    else error "Failed to run loop info pass."

getThreadSpawns :: Ptr Function -> Ptr (LoopInfoBase BasicBlock Loop) -> IO [ThreadLocation]
getThreadSpawns fun loopInfo = do
  blks <- getBasicBlockList fun >>= ipListToList
  analyzeBlocks blks
  where
    analyzeBlocks [] = return []
    analyzeBlocks (blk:blks) = do
      instrs <- getInstList blk >>= ipListToList
      analyzeInstructions instrs blk blks
    analyzeInstructions [] _ blks = analyzeBlocks blks
    analyzeInstructions (i:is) blk blks = case castDown i of
      Just call -> do
        cv <- callInstGetCalledValue call
        case castDown cv of
         Just (fun::Ptr Function) -> do
           name <- getNameString fun
           case name of
            "pthread_create" -> do
              threadVal <- callInstGetArgOperand call 2
              case castDown threadVal of
               Just threadFun -> do
                 loop <- loopInfoBaseGetLoopFor loopInfo blk
                 rest <- analyzeInstructions is blk blks
                 return $ (ThreadSpawnLocation { spawningInstruction = call
                                               , spawnedFunction = threadFun
                                               , quantity = if loop==nullPtr
                                                            then Finite 1
                                                            else Infinite
                                               }):rest
               Nothing -> error "Spawning dynamic functions not supported."
            _ -> analyzeInstructions is blk blks
      Nothing -> case castDown i of
        Just alloc -> do
          loop <- loopInfoBaseGetLoopFor loopInfo blk
          rest <- analyzeInstructions is blk blks
          return $ (AllocationLocation { allocInstruction = alloc
                                       , quantity = if loop==nullPtr
                                                    then Finite 1
                                                    else Infinite
                                       }):rest
        Nothing -> analyzeInstructions is blk blks

instance Num Quantity where
  (+) Infinite _ = Infinite
  (+) _ Infinite = Infinite
  (+) (Finite n) (Finite m) = Finite (n*m)
  (-) Infinite _ = Infinite
  (-) _ Infinite = Infinite
  (-) (Finite n) (Finite m) = Finite (n-m)
  abs Infinite = Infinite
  abs (Finite n) = Finite (abs n)
  signum Infinite = Infinite
  signum (Finite n) = Finite (signum n)
  fromInteger n = Finite n

instance Ord Quantity where
  compare Infinite Infinite = EQ
  compare Infinite _ = GT
  compare _ Infinite = LT
  compare (Finite n) (Finite m) = compare n m
