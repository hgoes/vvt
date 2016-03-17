{-| Used to determine the entry points and realization order for thread
    functions. -}
{-# LANGUAGE ViewPatterns,ScopedTypeVariables #-}
module Realization.Threaded.Slicing where

import LLVM.FFI
import Foreign.Ptr (Ptr,nullPtr)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Foreign.Storable (peek)
import Prelude hiding (sequence_,mapM_)

data Slicing = Slicing { entryPoints :: Map (Ptr BasicBlock,Int) ()
                       , blockStack :: [(Ptr BasicBlock,[Ptr BasicBlock])]
                       , visitedBlocks :: Set (Ptr BasicBlock)
                       , sliceQueue :: Map (Ptr BasicBlock,Int) [Ptr Instruction]
                       , realizationOrder :: [(Ptr BasicBlock,Int)]
                       , currentSlice :: Maybe (Ptr BasicBlock,Int,[Ptr Instruction])
                       , sliceMapping :: Map Integer [(Ptr BasicBlock,Int)]
                       }

getSlicing :: Ptr Function -> IO (Map (Ptr BasicBlock,Int) (),[(Ptr BasicBlock,Int)],Map Integer [(Ptr BasicBlock,Int)])
getSlicing fun = do
  entry <- getEntryBlock fun
  instrs <- getInstList entry >>= ipListToList
  let s0 = Slicing { entryPoints = Map.singleton (entry,0) ()
                   , blockStack = []
                   , visitedBlocks = Set.singleton entry
                   , sliceQueue = Map.empty
                   , realizationOrder = []
                   , currentSlice = Just (entry,0,instrs)
                   , sliceMapping = Map.singleton 0 [(entry,0)] }
  getSlicing' s0
  where
    getSlicing' s = do
      s' <- stepSlicing s
      case s' of
       Nothing -> return (entryPoints s,realizationOrder s,sliceMapping s)
       Just ns -> getSlicing' ns

stepSlicing :: Slicing -> IO (Maybe Slicing)
stepSlicing sl = case currentSlice sl of
  Nothing -> case Map.minViewWithKey (sliceQueue sl) of
    Nothing -> return Nothing
    Just (((blk,sblk),instrs),nqueue) -> return $ Just sl { currentSlice = Just (blk,sblk,instrs)
                                                          , blockStack = []
                                                          , visitedBlocks = Set.insert blk (visitedBlocks sl)
                                                          , entryPoints = Map.insert (blk,sblk) () (entryPoints sl)
                                                          , sliceQueue = nqueue }
  Just (blk,sblk,instrs) -> case instrs of
    [] -> case blockStack sl of
      (blk,[]):nstack -> return $ Just sl { blockStack = nstack
                                          , realizationOrder = if blk==nullPtr
                                                               then realizationOrder sl
                                                               else (blk,0):realizationOrder sl }
      (blk',nblk:blks):rstack
        | (blk==nblk && sblk==0) ||
          any ((==nblk).fst) (blockStack sl) -> return $ Just sl { blockStack = (blk',blks):rstack
                                                                 , entryPoints = Map.insert (nblk,0) () (entryPoints sl) }
        | Set.member nblk (visitedBlocks sl) -> return $ Just sl { blockStack = (blk',blks):rstack }
        | otherwise -> do
            ninstrs <- getInstList nblk >>= ipListToList
            return $ Just sl { blockStack = (nblk,blks):rstack
                             , currentSlice = Just (blk,sblk,ninstrs)
                             , realizationOrder = if blk'==nullPtr
                                                  then realizationOrder sl
                                                  else (blk',0):realizationOrder sl
                             , visitedBlocks = Set.insert nblk (visitedBlocks sl) }
      [] -> return $ Just sl { realizationOrder = (blk,sblk):realizationOrder sl
                             , currentSlice = Nothing }
    (castDown -> Just call):is -> do
      cv <- callInstGetCalledValue call
      case castDown cv of
       Just (fun::Ptr Function) -> do
         name <- getNameString fun
         case name of
          "pthread_yield" -> return $ Just sl { currentSlice = Just (blk,sblk,[])
                                              , sliceQueue = case blockStack sl of
                                                 [] -> Map.insert (blk,sblk+1) is (sliceQueue sl)
                                                 (blk,_):_ -> Map.insert (blk,1) is (sliceQueue sl)
                                              }
          "__yield" -> processYield
          "__yield_local" -> processYield
          "pthread_exit" -> return $ Just sl { currentSlice = Just (blk,sblk,[])
                                             , blockStack = (nullPtr,[]):blockStack sl }
          _ -> return $ Just sl { currentSlice = Just (blk,sblk,is) }
          where
            processYield = do
              num <- callInstGetArgOperand call 0
              case castDown num of
                Just cint -> do
                  val <- constantIntGetValue cint
                  APInt _ rval <- peek val
                  return $ Just sl { currentSlice = Just (blk,sblk,[])
                                   , sliceQueue = case blockStack sl of
                                       [] -> Map.insert (blk,sblk+1) is (sliceQueue sl)
                                       (blk,_):_ -> Map.insert (blk,1) is (sliceQueue sl)
                                   , sliceMapping = case blockStack sl of
                                       [] -> Map.insertWith (++) rval [(blk,sblk+1)] (sliceMapping sl)
                                       (blk,_):_ -> Map.insertWith (++) rval [(blk,1)] (sliceMapping sl)
                                   }
    [(castDown -> Just term)] -> do
      numSuccs <- terminatorInstGetNumSuccessors (term::Ptr TerminatorInst)
      succs <- mapM (terminatorInstGetSuccessor term) [0..numSuccs-1]
      return $ Just sl { currentSlice = Just (blk,sblk,[])
                       , blockStack = (nullPtr,succs):blockStack sl }
    _:is -> return $ Just sl { currentSlice = Just (blk,sblk,is) }
