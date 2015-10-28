module Main where

import LLVM.FFI
import Foreign.Ptr
import Foreign.C
import Data.List (stripPrefix)
import System.IO
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable
import System.Console.GetOpt
import System.Exit
import System.Environment
import Control.Monad (when)
import Data.Int
import Data.Monoid
import Prelude hiding (mapM_,elem,foldl)

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

threadJoinFun :: Ptr Module -> IO (Ptr Function)
threadJoinFun mod = do
  ctx <- moduleGetContext mod
  tpThreadId <- threadIdType mod
  tpThreadIdPtr <- pointerTypeGet tpThreadId 0
  void <- getVoidType ctx
  void8 <- getIntegerType ctx 8
  voidPtr <- pointerTypeGet void8 0
  voidPtrPtr <- pointerTypeGet voidPtr 0
  funSig <- withArrayRef [castUp tpThreadIdPtr,castUp voidPtrPtr] $
            \arr -> newFunctionType void arr False
  attrs <- newAttributeSet
  c <- withStringRef "__thread_join" $
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
                                     , lockTests :: [(Ptr LoadInst,Ptr TruncInst)]
                                     } deriving Show

instance Monoid IdentifiedLock where
  mempty = IdentifiedLock [] [] []
  mappend (IdentifiedLock a1 r1 t1) (IdentifiedLock a2 r2 t2)
    = IdentifiedLock (a1++a2) (r1++r2) (t1++t2)

mergeLocks :: Maybe IdentifiedLock -> Maybe IdentifiedLock -> Maybe IdentifiedLock
mergeLocks (Just l1) (Just l2) = Just $ mappend l1 l2
mergeLocks _ _ = Nothing

insertLocks :: Ptr Module -> IO ()
insertLocks mod = do
  ctx <- moduleGetContext mod
  locks <- identifyLocks mod
  hPutStrLn stderr $ "Identified locks:"
  mapM_ (\(var,locking) -> do
             varName <- getNameString var
             hPutStrLn stderr $ "  "++varName++": "++show locking
        ) (Map.toList locks)
  mtype <- mutexType mod
  ptrMType <- pointerTypeGet mtype 0
  i32 <- getIntegerType ctx 32
  i1 <- getIntegerType ctx 1
  lockSig <- withArrayRef [castUp ptrMType] $
             \arr -> newFunctionType i32 arr False
  testSig <- withArrayRef [castUp ptrMType] $
             \arr -> newFunctionType i1 arr False
  attrs <- newAttributeSet
  lockFun <- withStringRef "pthread_mutex_lock" $
             \name -> moduleGetOrInsertFunction mod name lockSig attrs
  unlockFun <- withStringRef "pthread_mutex_unlock" $
               \name -> moduleGetOrInsertFunction mod name lockSig attrs
  testFun <- withStringRef "pthread_mutex_locked" $
             \name -> moduleGetOrInsertFunction mod name testSig attrs
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
            mapM_ (\(loadMtx,truncLoad) -> do
                       name <- newTwineEmpty
                       testCall <- withArrayRef [castUp nvar] $
                                   \args -> newCallInst testFun args name
                       instructionInsertBefore testCall loadMtx
                       valueReplaceAllUsesWith truncLoad testCall
                       instructionRemoveFromParent loadMtx
                       instructionRemoveFromParent truncLoad
                  ) (lockTests lock)
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
        Just glob -> case is of
          (castDown -> Just (trunc::Ptr TruncInst)):is -> do
            hPutStrLn stderr $ "Load-trunk of global"
            truncOp <- getOperand trunc 0
            if truncOp==castUp load
              then identify begin end (Map.insertWith mergeLocks glob
                                       (Just $ IdentifiedLock
                                        [] [] [(load,trunc)]) locks) is
              else identify begin end (Map.insert glob Nothing locks) is
          _ -> identify begin end (Map.insert glob Nothing locks) is
        Nothing -> identify begin end locks is
    identify begin end locks ((castDown -> Just store):is) = do
      -- Mark stores to globals as non-locks
      ptr <- storeInstGetPointerOperand store
      case castDown ptr of
        Just glob -> do
          name <- getNameString glob
          hPutStrLn stderr $ name++" is not a lock (store detected)."
          identify begin end (Map.insert glob Nothing locks) is
        Nothing -> identify begin end locks is
    identify begin end locks (_:is) = identify begin end locks is
    getMutexLoad :: [Ptr Instruction] -> IO (Maybe (Ptr Value,[Ptr Value]),[Ptr Instruction])
    getMutexLoad
      ((castDown -> Just load):
       rest@((castDown -> Just (trunc::Ptr TruncInst)):
             (castDown -> Just (zext::Ptr ZExtInst)):
             is)) = do
        lockPtr <- loadInstGetPointerOperand load
        truncOp <- getOperand trunc 0
        if truncOp==castUp load
          then do
          zextOp <- getOperand zext 0
          if zextOp==castUp trunc
            then return (Just (lockPtr,[castUp zext,castUp trunc]),is)
            else return (Nothing,rest)
          else return (Nothing,rest)
    getMutexLoad
      ((castDown -> Just load):is) = do
        lockPtr <- loadInstGetPointerOperand load
        return (Just (lockPtr,[castUp load]),is)
    getMutexLoad (i:is) = return (Nothing,is)

    getMutexAssume :: [Ptr Value] -> [Ptr Instruction]
                   -> IO (Maybe (Int64,[Ptr Value],[Ptr Instruction]))
    getMutexAssume lockRes ((castDown -> Just cmp):rest) = do
      lhs <- getOperand cmp 0
      rhs <- getOperand cmp 1
      cmpOp <- getICmpOp cmp
      if lhs `elem` lockRes && cmpOp==I_EQ
        then case castDown rhs of
        Just cint -> do
          checkVal <- constantIntGetValue cint >>= apIntGetSExtValue
          return (Just (checkVal,[castUp cmp],rest))
        Nothing -> return Nothing
        else return Nothing
    getMutexAssume lockRes rest = return $ Just (1,lockRes,rest)
          

    getLocking cur begin end locks is = do
      (res,rest) <- getMutexLoad is
      case res of
        Nothing -> identify begin end locks is
        Just (lockPtr,lockRes) -> do
          res <- getMutexAssume lockRes rest
          case res of
            Nothing -> abort
            Just (checkVal,cmpRes,rest) -> case rest of
              ((castDown -> Just assume):
               (castDown -> Just store):
               (castDown -> Just callEnd):is) -> do
                hPutStrLn stderr "Matched!"
                case castDown lockPtr of
                  Nothing -> abort
                  Just glob -> do
                    hPutStrLn stderr "Is global"
                    assumeName <- callInstGetCalledValue assume >>= getNameString
                    if assumeName=="__assume"
                      then do
                      hPutStrLn stderr "Is assume"
                      assumeOp <- getOperand assume 0
                      if assumeOp `elem` cmpRes
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
                                           then do
                                             globName <- getNameString glob
                                             hPutStrLn stderr $ globName++" has lock aquire."
                                             identify begin end
                                               (Map.insertWith mergeLocks glob
                                                (Just $ IdentifiedLock [(cur,callEnd)] [] [])
                                                locks) is
                                           else if checkVal==1 && newVal==0
                                                then do
                                                  globName <- getNameString glob
                                                  hPutStrLn stderr $ globName++" has lock release."
                                                  identify begin end
                                                    (Map.insertWith mergeLocks glob
                                                     (Just $ IdentifiedLock [] [(cur,callEnd)] [])
                                                     locks) is
                                                else abort)
                                     else abort
                                Nothing -> abort
                            Nothing -> abort
                          else abort
                        else abort
                      else abort
              _ -> abort
          where
            abort = identify begin end locks is

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
  pthreadJoin <- threadJoinFun mod
  moduleGetFunctionList mod >>= ipListToLazyList >>=
    foldlM (\mp fun -> do
                getBasicBlockList fun >>= ipListToLazyList >>=
                  foldlM (\mp blk -> do
                              getInstList blk >>= ipListToLazyList >>=
                                foldlM (\mp i -> case castDown i of
                                          Nothing -> return mp
                                          Just call -> fixCall pthreadCreate pthreadJoin mp call
                                       ) mp
                         ) mp
           ) Map.empty
  return ()
  where
    fixRef :: Map (Ptr Value) (Ptr Value) -> Ptr Value
           -> IO (Ptr Value,Map (Ptr Value) (Ptr Value))
    fixRef mp val = case Map.lookup val mp of
      Just nval -> return (nval,mp)
      Nothing -> case castDown val of
        Just (allocRef::Ptr AllocaInst) -> do
          ctx <- moduleGetContext mod
          tp <- threadIdType mod
          name <- newTwineEmpty
          sz <- mallocAPInt (APInt 32 1) >>= createConstantInt ctx
          nalloc <- newAllocaInst tp sz 0 name
          instructionInsertAfter nalloc allocRef
          return (castUp nalloc,Map.insert val (castUp nalloc) mp)
        Nothing -> case castDown val of
          Just load -> do
            ptr <- loadInstGetPointerOperand load
            fixRef mp ptr
        
    fixCall :: Ptr Function -> Ptr Function
            -> Map (Ptr Value) (Ptr Value) -> Ptr CallInst
            -> IO (Map (Ptr Value) (Ptr Value))
    fixCall create join mp call = do
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
          (nref,nmp) <- fixRef mp ref
          hPutStrLn stderr $ "New reference:"
          valueDump nref
          --instructionInsertBefore nref call
          thr <- callInstGetArgOperand call 2
          arg <- callInstGetArgOperand call 3
          ncall <- withArrayRef [nref,thr,arg] $ \arr -> newCallInst create arr noName
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
          return nmp
        "pthread_join" -> do
          hPutStrLn stderr $ "Replacing call:"
          valueDump call
          noName <- newTwineEmpty
          ref <- callInstGetArgOperand call 0
          (nref,nmp) <- fixRef mp ref
          hPutStrLn stderr $ "New reference:"
          valueDump nref
          ret <- callInstGetArgOperand call 1
          ncall <- withArrayRef [nref,ret] $ \arr -> newCallInst join arr noName
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
          return nmp
        _ -> return mp

inlineAll :: Ptr Module -> IO ()
inlineAll mod = do
  pm <- newPassManager
  internalize <- withCString "main" $ \str -> withArrayRef [str] $ \arr -> createInternalizePass arr
  inline <- createFunctionInliningPass 100000
  passManagerAdd pm internalize
  passManagerAdd pm inline
  passManagerRun pm mod
  deletePassManager pm

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

data Transformation
  = MakeAtomicBlocks
  | MakeFiniteThreads Int
  | MakePThreadLocks
  | Inline

data Options = Options { showHelp :: Bool
                       , transformation :: [Transformation]
                       , verbose :: Int
                       }

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , transformation = []
                         , verbose = 0 }

options :: [OptDescr (Options -> Options)]
options = [Option ['h'] ["help"] (NoArg $ \opt -> opt { showHelp = True }) "Show this help."
          ,Option ['v'] ["verbose"] (OptArg (\v opt -> case v of
                                               Just v' -> opt { verbose = read v' }
                                               Nothing -> opt { verbose = 1 }) "level"
                                    ) "Output more information while running (higher level = more info)"
          ]

getOptions :: IO Options
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
    (xs,transf,[]) -> do
       let opts = foldl (flip id) defaultOptions xs
       when (showHelp opts) $ do
         putStrLn $
           usageInfo
           (unlines ["USAGE: vvt-svcomp [TRANS...] < <file>"
                    ,"       where <file> is an llvm file."
                    ,""
                    ,"  TRANS can be one of the following transformations:"
                    ,"    atomic        - Generate atomic blocks for atomic functions."
                    ,"    threads[=p]   - Restrict infinite thread creation loops."
                    ,"    locks         - Identify locks in the program."
                    ,"    inline        - Inline all inlineable functions."
                    ]
           ) options
         exitSuccess
       transf' <- mapM (\t -> case parseTransformation t of
                          Nothing -> do
                            hPutStrLn stderr $ "Failed to parse transformation: "++t
                            exitFailure
                          Just t' -> return t'
                       ) transf
       return (opts { transformation = transf' })
    (_,_,errs) -> do
      hPutStrLn stderr "vvt-svcomp: Error while parsing command-line options:"
      mapM (\err -> hPutStrLn stderr $ "  "++err) errs
      exitFailure

applyTransformation :: Int -> Ptr Module -> Transformation -> IO ()
applyTransformation _ mod MakeAtomicBlocks = makeAtomic mod
applyTransformation _ mod (MakeFiniteThreads n) = makeFiniteThreads n mod -- >> fixPThreadCalls mod
applyTransformation _ mod MakePThreadLocks = insertLocks mod
applyTransformation _ mod Inline = inlineAll mod

parseTransformation :: String -> Maybe Transformation
parseTransformation "atomic" = Just MakeAtomicBlocks
parseTransformation "locks" = Just MakePThreadLocks
parseTransformation "inline" = Just Inline
parseTransformation (stripPrefix "threads" -> Just rest) = case rest of
  '=':n -> Just $ MakeFiniteThreads (read n)
  "" -> Just $ MakeFiniteThreads 2
  _ -> Nothing
parseTransformation _  = Nothing

main :: IO ()
main = do
  opts <- getOptions
  mod <- getProgram
  mapM_ (applyTransformation (verbose opts) mod) (transformation opts)
  writeBitCodeToFile mod "/dev/stdout"
  return ()
