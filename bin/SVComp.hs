module Main where

import LLVM.FFI
import Foreign.Ptr
import Data.List (stripPrefix)
import System.IO
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable

threadIdType :: Ptr Module -> IO (Ptr StructType)
threadIdType mod = withStringRef "struct.__thread_id" $ \name -> do
  tp <- moduleGetTypeByName mod name
  if tp/=nullPtr
    then return tp
    else do
    ctx <- moduleGetContext mod
    i8 <- getIntegerType ctx 8
    pi8 <- pointerTypeGet i8 0
    withArrayRef [castUp pi8] $ \ref -> newNamedStructType ctx ref name False

mutexType :: Ptr Module -> IO (Ptr StructType)
mutexType mod = withStringRef "struct.pthread_mutex_t" $ \name -> do
  tp <- moduleGetTypeByName mod name
  if tp/=nullPtr
    then return tp
    else do
    ctx <- moduleGetContext mod
    i32 <- getIntegerType ctx 32
    withArrayRef [castUp i32] $ \ref -> newNamedStructType ctx ref name False

atomicFun :: Ptr Module -> String -> IO (Ptr Function)
atomicFun mod name = withStringRef name $ \str -> do
  ctx <- moduleGetContext mod
  void <- getVoidType ctx
  tp <- withArrayRef [] $ \arr -> newFunctionType void arr False
  attrs <- newAttributeSet
  c <- moduleGetOrInsertFunction mod str tp attrs
  case castDown c of
    Just fun -> return fun

threadSpawnFun :: Ptr Module -> IO (Ptr Function)
threadSpawnFun mod = do
  ctx <- moduleGetContext mod
  tpThreadId <- threadIdType mod
  tpThreadIdPtr <- pointerTypeGet tpThreadId 0
  void <- getVoidType ctx
  void8 <- getIntegerType ctx 8
  voidPtr <- pointerTypeGet void8 0
  threadFun <- withArrayRef [castUp voidPtr] $ \arr -> newFunctionType voidPtr arr False
  threadFunPtr <- pointerTypeGet threadFun 0
  funSig <- withArrayRef [castUp tpThreadIdPtr,castUp threadFunPtr,castUp voidPtr] $
            \arr -> newFunctionType void arr False
  attrs <- newAttributeSet
  c <- withStringRef "__thread_spawn" $
       \name -> moduleGetOrInsertFunction mod name funSig attrs
  deleteAttributeSet attrs
  case castDown c of
    Just fun -> return fun
  
makeAtomic :: Ptr Module -> IO ()
makeAtomic mod = do
  funs <- moduleGetFunctionList mod >>= ipListToList
  mapM_ (\fun -> do
             name <- getNameString fun
             case stripPrefix "__VERIFIER_atomic_" name of
               Just rname -> makeAtomic' fun
               Nothing -> return ()
        ) funs
  where
    makeAtomic' :: Ptr Function -> IO ()
    makeAtomic' fun = do
      begin <- atomicFun mod "__atomic_begin"
      blk <- getEntryBlock fun
      instr <- getFirstNonPHI blk
      callName <- newTwineEmpty
      callBegin <- withArrayRef [] $ \arr -> newCallInst begin arr callName
      instructionInsertBefore callBegin instr
      makeAtomic'' Set.empty blk
      return ()
    makeAtomic'' :: Set (Ptr BasicBlock) -> Ptr BasicBlock -> IO (Set (Ptr BasicBlock))
    makeAtomic'' visited blk
      | Set.member blk visited = return visited
    makeAtomic'' visited blk = do
      term <- getTerminator blk
      case castDown term of
        Just (_::Ptr ReturnInst) -> do
          end <- atomicFun mod "__atomic_end"
          callName <- newTwineEmpty
          callEnd <- withArrayRef [] $ \arr -> newCallInst end arr callName
          instructionInsertBefore callEnd term
          return (Set.insert blk visited)
        Nothing -> do
          nsuccs <- terminatorInstGetNumSuccessors term
          foldlM (\visited' n -> do
                    succ <- terminatorInstGetSuccessor term n
                    makeAtomic'' visited' succ
                 ) (Set.insert blk visited) [0..nsuccs-1]

data IdentifiedLock = IdentifiedLock { lockAquires :: [(Ptr CallInst,Ptr CallInst)]
                                     , lockReleases :: [(Ptr CallInst,Ptr CallInst)]
                                     } deriving Show

instance Monoid IdentifiedLock where
  mempty = IdentifiedLock [] []
  mappend (IdentifiedLock a1 r1) (IdentifiedLock a2 r2)
    = IdentifiedLock (a1++a2) (r1++r2)

insertLocks :: Ptr Module -> IO ()
insertLocks mod = do
  ctx <- moduleGetContext mod
  locks <- identifyLocks mod
  hPutStrLn stderr $ "Identified locks: "++show locks
  mtype <- mutexType mod
  ptrMType <- pointerTypeGet mtype 0
  i32 <- getIntegerType ctx 32
  lockSig <- withArrayRef [castUp ptrMType] $
             \arr -> newFunctionType i32 arr False
  attrs <- newAttributeSet
  lockFun <- withStringRef "pthread_mutex_lock" $
             \name -> moduleGetOrInsertFunction mod name lockSig attrs
  unlockFun <- withStringRef "pthread_mutex_unlock" $
               \name -> moduleGetOrInsertFunction mod name lockSig attrs
  val0 <- mallocAPInt (APInt 32 0) >>= createConstantInt ctx
  struct <- withArrayRef [castUp val0] $ \arr -> newConstantStruct mtype arr
  deleteAttributeSet attrs
  mapM_ (\((var,lock),n) -> do
            name <- newTwineString $ "__infered_lock_"++show n
            nvar <- newGlobalVariable mtype False InternalLinkage struct name NotThreadLocal 0 False
            globs <- moduleGetGlobalList mod
            ipListPushBack globs nvar
            mapM_ (\(beginAquire,endAquire) -> do
                     name <- newTwineEmpty
                     lockCall <- withArrayRef [castUp nvar] $
                                 \args -> newCallInst lockFun args name
                     blk <- instructionGetParent beginAquire
                     instrs <- getInstList blk
                     begin <- ipListBegin instrs
                     replaceSeq instrs begin (castUp beginAquire) (castUp endAquire) (castUp lockCall)
                     ipListToList instrs >>= mapM valueToString >>= hPutStrLn stderr . unlines
                     return ()
                  ) (lockAquires lock)
            mapM_ (\(beginRelease,endRelease) -> do
                     name <- newTwineEmpty
                     unlockCall <- withArrayRef [castUp nvar] $
                                   \args -> newCallInst unlockFun args name
                     blk <- instructionGetParent beginRelease
                     instrs <- getInstList blk
                     begin <- ipListBegin instrs
                     replaceSeq instrs begin (castUp beginRelease) (castUp endRelease) (castUp unlockCall)
                     return ()
                  ) (lockReleases lock)
        ) (zip (Map.toList $ Map.mapMaybe id locks) [0..])
  where
    replaceSeq instrs cur begin end repl = do
      last <- ipListEnd instrs
      isLast <- iListIteratorEq cur last
      if isLast
        then error "Lock cannot be found."
        else do
          instr <- iListIteratorDeref cur
          if instr==begin
            then removeUntil instrs cur end repl
            else do
              iListIteratorNext cur
              replaceSeq instrs cur begin end repl
    removeUntil :: Ptr (Iplist Instruction) -> Ptr (Ilist_iterator Instruction) -> Ptr Instruction -> Ptr Instruction -> IO ()
    removeUntil instrs cur end repl = do
      last <- ipListEnd instrs
      isLast <- iListIteratorEq cur last
      if isLast
        then error "Lock end cannot be found."
        else do
          instr <- iListIteratorDeref cur
          ipListRemove instrs cur
          if instr==end
            then ipListInsert instrs cur repl >> return ()
            else removeUntil instrs cur end repl

identifyLocks :: Ptr Module -> IO (Map (Ptr GlobalVariable) (Maybe IdentifiedLock))
identifyLocks mod = do
  atBegin <- atomicFun mod "__atomic_begin"
  atEnd <- atomicFun mod "__atomic_end"
  funs <- moduleGetFunctionList mod >>= ipListToList
  foldlM (\locks fun -> do
            blks <- getBasicBlockList fun >>= ipListToList
            foldlM (\locks blk -> do
                      instrs <- getInstList blk >>= ipListToList
                      identify atBegin atEnd locks instrs
                   ) locks blks
         ) Map.empty funs
  where
    identify :: Ptr Function -> Ptr Function
             -> Map (Ptr GlobalVariable) (Maybe IdentifiedLock)
             -> [Ptr Instruction]
             -> IO (Map (Ptr GlobalVariable) (Maybe IdentifiedLock))
    identify _ _ locks [] = return locks
    identify begin end locks ((castDown -> Just call):is1) = do
      obj <- callInstGetCalledValue call
      case castDown obj of
        Just fun
          | fun == begin -> do
            hPutStrLn stderr "Matching atomic section..."
            getLocking call begin end locks is1
        _ -> identify begin end locks is1
    identify begin end locks ((castDown -> Just load):is) = do
      -- Mark loads from globals as non-locks
      ptr <- loadInstGetPointerOperand load
      case castDown ptr of
        Just glob -> identify begin end (Map.insert glob Nothing locks) is
        Nothing -> identify begin end locks is
    identify begin end locks ((castDown -> Just store):is) = do
      -- Mark stores to globals as non-locks
      ptr <- storeInstGetPointerOperand store
      case castDown ptr of
        Just glob -> identify begin end (Map.insert glob Nothing locks) is
        Nothing -> identify begin end locks is
    identify begin end locks (_:is) = identify begin end locks is

    getLocking cur begin end locks
      ((castDown -> Just load):
       rest@((castDown -> Just cmp):
             (castDown -> Just assume):
             (castDown -> Just store):
             (castDown -> Just callEnd):is)) = do
      hPutStrLn stderr "Matched!"
      lockPtr <- loadInstGetPointerOperand load
      case castDown lockPtr of
        Nothing -> abort
        Just glob -> do
          hPutStrLn stderr "Is global"
          cmpOp <- getICmpOp cmp
          if cmpOp==I_EQ
            then do
              hPutStrLn stderr "Is EQ"
              lhs <- getOperand cmp 0
              rhs <- getOperand cmp 1
              hPutStrLn stderr "LHS:"
              valueToString lhs >>= hPutStrLn stderr
              hPutStrLn stderr "RHS:"
              valueToString rhs >>= hPutStrLn stderr
              if lhs==castUp load
                then case castDown rhs of
                  Nothing -> abort
                  Just cint -> do
                    hPutStrLn stderr "Is int EQ"
                    checkVal <- constantIntGetValue cint >>= apIntGetSExtValue
                    assumeName <- callInstGetCalledValue assume >>= getNameString
                    if assumeName=="__assume"
                      then do
                        hPutStrLn stderr "Is assume"
                        assumeOp <- getOperand assume 0
                        if assumeOp==castUp cmp
                          then do
                            storePtr <- storeInstGetPointerOperand store
                            if storePtr==lockPtr
                              then do
                                hPutStrLn stderr "Store is to same address"
                                storeVal <- storeInstGetValueOperand store
                                case castDown storeVal of
                                  Just cint -> do
                                    hPutStrLn stderr "Stores int"
                                    newVal <- constantIntGetValue cint >>= apIntGetSExtValue
                                    endFun <- callInstGetCalledValue callEnd
                                    case castDown endFun of
                                      Just endFun'
                                        -> if endFun'==end
                                           then (if checkVal==0 && newVal==1
                                                 then identify begin end
                                                      (Map.insertWith mappend glob
                                                       (Just $ IdentifiedLock [(cur,callEnd)] [])
                                                       locks) is
                                                 else if checkVal==1 && newVal==0
                                                      then identify begin end
                                                           (Map.insertWith mappend glob
                                                            (Just $ IdentifiedLock [] [(cur,callEnd)])
                                                            locks) is
                                                      else abort)
                                           else abort
                                      Nothing -> abort
                                  Nothing -> abort
                              else abort
                          else abort
                      else abort
                else abort
            else abort
      where
        abort = identify begin end locks rest
    getLocking cur begin end locks (_:is) = identify begin end locks is

makeFiniteThreads :: Int -> Ptr Module -> IO ()
makeFiniteThreads n mod = do
  funs <- moduleGetFunctionList mod >>= ipListToList
  mapM_ (\fun -> do
           blks <- getBasicBlockList fun >>= ipListToList
           mapM_ (\blk -> do
                    term <- getTerminator blk
                    case castDown term of
                      Just br -> do
                        isCond <- branchInstIsConditional br
                        if isCond
                          then return ()
                          else do
                            nxt <- terminatorInstGetSuccessor br 0
                            if nxt==blk
                              then do
                                thr <- hasThreadCreate blk
                                if thr
                                  then unrollBlock fun (n-1) blk
                                  else return ()
                              else return ()
                      Nothing -> return ()
                 ) blks
        ) funs
  where
    hasThreadCreate :: Ptr BasicBlock -> IO Bool
    hasThreadCreate blk = do
      instrs <- getInstList blk >>= ipListToList
      findThreadCreate instrs
    findThreadCreate :: [Ptr Instruction] -> IO Bool
    findThreadCreate [] = return False
    findThreadCreate (i:is) = case castDown i of
      Just call -> do
        cv <- callInstGetCalledValue call
        case castDown cv of
          Just fun -> do
            name <- getNameString (fun::Ptr Function)
            if name=="pthread_create"
              then return True
              else findThreadCreate is
          Nothing -> findThreadCreate is
      Nothing -> findThreadCreate is
    unrollBlock :: Ptr Function -> Int -> Ptr BasicBlock -> IO ()
    unrollBlock fun 0 blk = do
      ctx <- moduleGetContext mod
      zero' <- newAPIntLimited 32 0 False
      zero <- createConstantInt ctx zero'
      deleteAPInt zero'
      ret <- newReturnInst ctx zero
      lst <- getInstList blk
      last <- ipListEnd lst >>= iListIteratorPrev
      ipListRemove lst last
      ipListPushBack lst (castUp ret)
    unrollBlock fun n blk = do
      ctx <- moduleGetContext mod
      blkName <- newTwineEmpty
      mapping <- newValueMap
      nblk <- cloneBasicBlock blk mapping blkName fun nullPtr
      deleteValueMap mapping
      br <- newBranchInst nblk
      lst <- getInstList blk
      last <- ipListEnd lst >>= iListIteratorPrev
      ipListRemove lst last
      ipListPushBack lst (castUp br)
      unrollBlock fun (n-1) nblk

fixPThreadCalls :: Ptr Module -> IO ()
fixPThreadCalls mod = do
  pthreadCreate <- threadSpawnFun mod
  moduleGetFunctionList mod >>= ipListToLazyList >>=
    mapM_ (\fun -> do
              getBasicBlockList fun >>= ipListToLazyList >>=
                mapM_ (\blk -> do
                         getInstList blk >>= ipListToLazyList >>=
                           mapM_ (\i -> case castDown i of
                                          Nothing -> return ()
                                          Just call -> fixCall pthreadCreate call
                                 )))
  where
    fixCall :: Ptr Function -> Ptr CallInst -> IO ()
    fixCall create call = do
      ctx <- moduleGetContext mod
      void <- getIntegerType ctx 8 >>= \p -> pointerTypeGet p 0
      cv <- callInstGetCalledValue call
      name <- getNameString cv
      case name of
        "pthread_create" -> do
          hPutStrLn stderr $ "Replacing call:"
          valueDump call
          noName <- newTwineEmpty
          ref <- callInstGetArgOperand call 0
          nref <- case castDown ref of
            Just (allocRef::Ptr AllocaInst) -> do
              tp <- threadIdType mod
              name <- newTwineEmpty
              sz <- mallocAPInt (APInt 32 0) >>= createConstantInt ctx
              nalloc <- newAllocaInst tp sz 0 name
              instructionInsertAfter nalloc allocRef
              return nalloc
          --nref <- newBitCastInst ref void noName
          hPutStrLn stderr $ "New reference:"
          valueDump nref
          --instructionInsertBefore nref call
          thr <- callInstGetArgOperand call 2
          arg <- callInstGetArgOperand call 3
          ncall <- withArrayRef [castUp nref,thr,arg] $ \arr -> newCallInst create arr noName
          hPutStrLn stderr $ "Replacement call:"
          valueDump ncall
          instructionInsertBefore ncall call
          rtp <- getType call
          bw <- case castDown rtp of
            Just itp -> getBitWidth itp
            Nothing -> return 32
          zero <- newAPIntLimited (fromIntegral bw) 0 False
          czero <- createConstantInt ctx zero
          deleteAPInt zero
          valueReplaceAllUsesWith call czero
          instructionRemoveFromParent call
        _ -> return ()

getProgram :: IO (Ptr Module)
getProgram = do
  loadRes <- getStdInMemoryBufferSimple
  buf <- case loadRes of
    Left err -> error $ "Error while loading bitcode file: "++show err
    Right b -> return b
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  return mod

main :: IO ()
main = do
  mod <- getProgram
  hPutStrLn stderr "Creating atomic blocks..."
  makeAtomic mod
  hPutStrLn stderr "Unrolling thread creation loops..."
  makeFiniteThreads 2 mod
  hPutStrLn stderr "Fixing pthread calls..."
  fixPThreadCalls mod
  hPutStrLn stderr "Inserting locks..."
  insertLocks mod
  hPutStrLn stderr "done."
  writeBitCodeToFile mod "/dev/stdout"
  return ()
