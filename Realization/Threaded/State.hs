{-# LANGUAGE DeriveDataTypeable,TypeFamilies #-}
module Realization.Threaded.State where

import Realization.Threaded.Value

import Language.SMTLib2
import Language.SMTLib2.Internals
import LLVM.FFI
import Foreign.Ptr (Ptr)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable

data ThreadState = ThreadState { latchBlocks :: Map (Ptr BasicBlock,Int) (SMTExpr Bool)
                               , latchValues :: Map (Ptr Instruction) SymVal
                               } deriving (Typeable,Eq,Ord,Show)

data ThreadStateDesc = ThreadStateDesc { latchBlockDesc :: Map (Ptr BasicBlock,Int) ()
                                       , latchValueDesc :: Map (Ptr Instruction) SymType
                                       } deriving (Typeable,Eq,Ord,Show)

data ProgramState = ProgramState { mainState :: ThreadState
                                 , threadState :: Map (Ptr CallInst) (SMTExpr Bool,ThreadState)
                                 , memory :: Map MemoryLoc SymVal
                                 } deriving (Typeable,Eq,Ord,Show)

data ProgramStateDesc = ProgramStateDesc { mainStateDesc :: ThreadStateDesc
                                         , threadStateDesc :: Map (Ptr CallInst) ThreadStateDesc
                                         , memoryDesc :: Map MemoryLoc SymType
                                         } deriving (Typeable,Eq,Ord,Show)

data ThreadInput = ThreadInput { step :: SMTExpr Bool
                               , nondets :: Map (Ptr Instruction) SymVal
                               } deriving (Typeable,Show,Eq,Ord)

newtype ThreadInputDesc = ThreadInputDesc { nondetTypes :: Map (Ptr Instruction) SymType }
                        deriving (Typeable,Eq,Ord,Show)

data ProgramInput = ProgramInput { mainInput :: ThreadInput
                                 , threadInput :: Map (Ptr CallInst) ThreadInput
                                 } deriving (Typeable,Eq,Ord,Show)

data ProgramInputDesc = ProgramInputDesc { mainInputDesc :: ThreadInputDesc
                                         , threadInputDesc :: Map (Ptr CallInst) ThreadInputDesc
                                         } deriving (Typeable,Eq,Ord,Show)

updateThreadStateDesc :: Maybe (Ptr CallInst) -> (ThreadStateDesc -> ThreadStateDesc)
                      -> ProgramStateDesc -> ProgramStateDesc
updateThreadStateDesc Nothing f ps = ps { mainStateDesc = f (mainStateDesc ps) }
updateThreadStateDesc (Just thread) f ps
  = ps { threadStateDesc = Map.adjust f thread (threadStateDesc ps) }

updateThreadInputDesc :: Maybe (Ptr CallInst) -> (ThreadInputDesc -> ThreadInputDesc)
                      -> ProgramInputDesc -> ProgramInputDesc
updateThreadInputDesc Nothing f pi = pi { mainInputDesc = f (mainInputDesc pi) }
updateThreadInputDesc (Just thread) f pi
  = pi { threadInputDesc = Map.adjust f thread (threadInputDesc pi) }

getThreadState :: Maybe (Ptr CallInst) -> ProgramState -> ThreadState
getThreadState Nothing st = mainState st
getThreadState (Just th) st = snd $ (threadState st) Map.! th

getThreadInput :: Maybe (Ptr CallInst) -> ProgramInput -> ThreadInput
getThreadInput Nothing inp = mainInput inp
getThreadInput (Just th) inp = (threadInput inp) Map.! th

instance Args ThreadInput where
  type ArgAnnotation ThreadInput = ThreadInputDesc
  foldExprs f s ti (ThreadInputDesc ann) = do
    (s1,nstep) <- foldExprs f s (step ti) ()
    (s2,nnondet) <- foldExprs f s1 (nondets ti) ann
    return (s2,ThreadInput { step = nstep
                           , nondets = nnondet })
  foldsExprs f s lst (ThreadInputDesc ann) = do
    (s1,nsteps,nstep) <- f s [ (step ti,b) | (ti,b) <- lst ] ()
    (s2,nnondets,nnondet) <- foldsExprs f s1 [ (nondets ti,b) | (ti,b) <- lst ] ann
    return (s2,zipWith ThreadInput nsteps nnondets,ThreadInput nstep nnondet)
  extractArgAnnotation ti = ThreadInputDesc $ extractArgAnnotation (nondets ti)
  toArgs _ [] = Nothing
  toArgs (ThreadInputDesc ann) (e:es) = do
    b <- entype cast e
    (n,rest) <- toArgs ann es
    return (ThreadInput b n,rest)
  fromArgs ti = (UntypedExpr (step ti)):fromArgs (nondets ti)
  getTypes ti (ThreadInputDesc ann) = (ProxyArg (undefined::Bool) ()):getTypes (nondets ti) ann
  getArgAnnotation ti (_:sorts)
    = let (res,rest) = getArgAnnotation (nondets ti) sorts
      in (ThreadInputDesc res,rest)

instance Args ProgramInput where
  type ArgAnnotation ProgramInput = ProgramInputDesc
  foldExprs f s pi ann = do
    (s1,nmain) <- foldExprs f s (mainInput pi) (mainInputDesc ann)
    (s2,nthreads) <- foldExprs f s1 (threadInput pi) (threadInputDesc ann)
    return (s2,ProgramInput nmain nthreads)
  foldsExprs f s lst ann = do
    (s1,nmains,nmain) <- foldsExprs f s [ (mainInput pi,b) | (pi,b) <- lst ]
                         (mainInputDesc ann)
    (s2,nthreads,nthread) <- foldsExprs f s1 [ (threadInput pi,b) | (pi,b) <- lst ]
                             (threadInputDesc ann)
    return (s2,zipWith ProgramInput nmains nthreads,ProgramInput nmain nthread)
  extractArgAnnotation pi = ProgramInputDesc
                            (extractArgAnnotation (mainInput pi))
                            (extractArgAnnotation (threadInput pi))
  toArgs ann exprs = do
    (main,r1) <- toArgs (mainInputDesc ann) exprs
    (rest,r2) <- toArgs (threadInputDesc ann) r1
    return (ProgramInput main rest,r2)
  fromArgs pi = fromArgs (mainInput pi) ++
                fromArgs (threadInput pi)
  getTypes pi ann = getTypes (mainInput pi) (mainInputDesc ann) ++
                    getTypes (threadInput pi) (threadInputDesc ann)
  getArgAnnotation pi sorts = let (mainAnn,s1) = getArgAnnotation (mainInput pi) sorts
                                  (restAnn,s2) = getArgAnnotation (threadInput pi) s1
                              in (ProgramInputDesc mainAnn restAnn,s2)

instance Args ThreadState where
  type ArgAnnotation ThreadState = ThreadStateDesc
  foldExprs f s ts ann = do
    (s1,blk) <- foldExprs f s (latchBlocks ts) (latchBlockDesc ann)
    (s2,instrs) <- foldExprs f s1 (latchValues ts) (latchValueDesc ann)
    return (s2,ThreadState blk instrs)
  foldsExprs f s lst ann = do
    (s1,blks,blk) <- foldsExprs f s [ (latchBlocks ts,b) | (ts,b) <- lst ]
                     (latchBlockDesc ann)
    (s2,instrs,instr) <- foldsExprs f s1 [ (latchValues ts,b) | (ts,b) <- lst ]
                         (latchValueDesc ann)
    return (s2,zipWith ThreadState blks instrs,ThreadState blk instr)
  extractArgAnnotation ts = ThreadStateDesc
                            (extractArgAnnotation (latchBlocks ts))
                            (extractArgAnnotation (latchValues ts))
  toArgs ann exprs = do
    (blk,es1) <- toArgs (latchBlockDesc ann) exprs
    (instr,es2) <- toArgs (latchValueDesc ann) es1
    return (ThreadState blk instr,es2)
  fromArgs ts = fromArgs (latchBlocks ts) ++
                fromArgs (latchValues ts)
  getTypes ts ann = getTypes (latchBlocks ts) (latchBlockDesc ann) ++
                    getTypes (latchValues ts) (latchValueDesc ann)
  getArgAnnotation ts sorts = let (blkAnn,s1) = getArgAnnotation (latchBlocks ts) sorts
                                  (iAnn,s2) = getArgAnnotation (latchValues ts) s1
                              in (ThreadStateDesc blkAnn iAnn,s2)

instance Args ProgramState where
  type ArgAnnotation ProgramState = ProgramStateDesc
  foldExprs f s ps ann = do
    (s1,nmain) <- foldExprs f s (mainState ps) (mainStateDesc ann)
    (s2,nthread) <- foldExprs f s1 (threadState ps)
                    (fmap (\x -> ((),x)) $ threadStateDesc ann)
    (s3,nmem) <- foldExprs f s2 (memory ps) (memoryDesc ann)
    return (s3,ProgramState nmain nthread nmem)
  foldsExprs f s lst ann = do
    (s1,nmains,nmain) <- foldsExprs f s [ (mainState ps,b) | (ps,b) <- lst ]
                         (mainStateDesc ann)
    (s2,nthreads,nthread) <- foldsExprs f s1 [ (threadState ps,b) | (ps,b) <- lst ]
                             (fmap (\x -> ((),x)) $ threadStateDesc ann)
    (s3,nmems,nmem) <- foldsExprs f s2 [ (memory ps,b) | (ps,b) <- lst ]
                       (memoryDesc ann)
    return (s3,zipWith3 ProgramState nmains nthreads nmems,
            ProgramState nmain nthread nmem)
  extractArgAnnotation ps = ProgramStateDesc
                            (extractArgAnnotation (mainState ps))
                            (fmap snd $ extractArgAnnotation (threadState ps))
                            (extractArgAnnotation (memory ps))
  toArgs ann exprs = do
    (nmain,r1) <- toArgs (mainStateDesc ann) exprs
    (nthread,r2) <- toArgs (fmap (\x -> ((),x)) $ threadStateDesc ann) r1
    (nmem,r3) <- toArgs (memoryDesc ann) r2
    return (ProgramState nmain nthread nmem,r3)
  fromArgs ps = fromArgs (mainState ps) ++
                fromArgs (threadState ps) ++
                fromArgs (memory ps)
  getTypes ps ann = getTypes (mainState ps) (mainStateDesc ann) ++
                    getTypes (threadState ps) (fmap (\x -> ((),x)) $ threadStateDesc ann) ++
                    getTypes (memory ps) (memoryDesc ann)
  getArgAnnotation ps s = let (ms,s1) = getArgAnnotation (mainState ps) s
                              (ts,s2) = getArgAnnotation (threadState ps) s1
                              (allocs,s3) = getArgAnnotation (memory ps) s2
                          in (ProgramStateDesc ms (fmap snd ts) allocs,s3)
