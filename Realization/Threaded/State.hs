{-# LANGUAGE DeriveDataTypeable,TypeFamilies #-}
module Realization.Threaded.State where

import Realization.Threaded.Value

import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)
import LLVM.FFI
import Foreign.Ptr (Ptr)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable
import Text.Show
import System.IO.Unsafe

data ThreadState = ThreadState { latchBlocks :: Map (Ptr BasicBlock,Int) (SMTExpr Bool)
                               , latchValues :: Map (Ptr Instruction) SymVal
                               , threadArgument :: Maybe (Ptr Argument,SymVal)
                               } deriving (Typeable,Eq,Ord,Show)

data ThreadStateDesc = ThreadStateDesc { latchBlockDesc :: Map (Ptr BasicBlock,Int) ()
                                       , latchValueDesc :: Map (Ptr Instruction) SymType
                                       , threadArgumentDesc :: Maybe (Ptr Argument,SymType)
                                       } deriving (Typeable,Eq,Ord,Show)

data ProgramState = ProgramState { mainState :: ThreadState
                                 , threadState :: Map (Ptr CallInst) (SMTExpr Bool,ThreadState)
                                 , memory :: Map MemoryLoc AllocVal
                                 } deriving (Typeable,Eq,Ord,Show)

data ProgramStateDesc = ProgramStateDesc { mainStateDesc :: ThreadStateDesc
                                         , threadStateDesc :: Map (Ptr CallInst) ThreadStateDesc
                                         , memoryDesc :: Map MemoryLoc AllocType
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
getThreadState (Just th) st = case Map.lookup th (threadState st) of
  Just (_,ts) -> ts
  Nothing -> error $ "getThreadState: Couldn't get thread state for "++show th

getThreadStateDesc :: Maybe (Ptr CallInst) -> ProgramStateDesc -> ThreadStateDesc
getThreadStateDesc Nothing ps = mainStateDesc ps
getThreadStateDesc (Just th) st = case Map.lookup th (threadStateDesc st) of
  Just desc -> desc
  Nothing -> error $ "getThreadStateDesc: Couldn't get thread state description for "++show th

getThreadInput :: Maybe (Ptr CallInst) -> ProgramInput -> ThreadInput
getThreadInput Nothing inp = mainInput inp
getThreadInput (Just th) inp = case Map.lookup th (threadInput inp) of
  Just inp -> inp
  Nothing -> error $ "getThreadInput: Couldn't get input for thread "++show th

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
    (s3,arg) <- case threadArgumentDesc ann of
      Nothing -> return (s2,Nothing)
      Just (val,tp) -> do
        (ns,res) <- foldExprs f s2 (case threadArgument ts of
                                     Just l -> snd l) tp
        return (ns,Just (val,res))
    return (s3,ThreadState blk instrs arg)
  foldsExprs f s lst ann = do
    (s1,blks,blk) <- foldsExprs f s [ (latchBlocks ts,b) | (ts,b) <- lst ]
                     (latchBlockDesc ann)
    (s2,instrs,instr) <- foldsExprs f s1 [ (latchValues ts,b) | (ts,b) <- lst ]
                         (latchValueDesc ann)
    (s3,args,arg) <- case threadArgumentDesc ann of
      Nothing -> return (s2,fmap (const Nothing) lst,Nothing)
      Just (val,tp) -> do
        (ns,args,arg) <- foldsExprs f s2 [ (case threadArgument ts of
                                             Just v -> snd v,b) | (ts,b) <- lst ] tp
        return (ns,fmap (\v -> Just (val,v)) args,Just (val,arg))
    return (s3,zipWith3 ThreadState blks instrs args,ThreadState blk instr arg)
  extractArgAnnotation ts = ThreadStateDesc
                            (extractArgAnnotation (latchBlocks ts))
                            (extractArgAnnotation (latchValues ts))
                            (case threadArgument ts of
                              Nothing -> Nothing
                              Just (val,v) -> Just (val,extractArgAnnotation v))
  toArgs ann exprs = do
    (blk,es1) <- toArgs (latchBlockDesc ann) exprs
    (instr,es2) <- toArgs (latchValueDesc ann) es1
    (arg,es3) <- case threadArgumentDesc ann of
      Nothing -> return (Nothing,es2)
      Just (val,tp) -> do
        (v,nes) <- toArgs tp es2
        return (Just (val,v),nes)
    return (ThreadState blk instr arg,es3)
  fromArgs ts = fromArgs (latchBlocks ts) ++
                fromArgs (latchValues ts) ++
                (case threadArgument ts of
                  Nothing -> []
                  Just (_,v) -> fromArgs v)
  getTypes ts ann = getTypes (latchBlocks ts) (latchBlockDesc ann) ++
                    getTypes (latchValues ts) (latchValueDesc ann) ++
                    (case threadArgumentDesc ann of
                      Nothing -> []
                      Just (_,tp) -> getTypes (case threadArgument ts of
                                                Just (_,v) -> v) tp)

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

showMemoryDesc :: Map MemoryLoc AllocType -> ShowS
showMemoryDesc desc
  = showListWith (\(loc,tp) -> showMemoryLoc loc .
                               showString " ~> " .
                               showsPrec 0 tp
                 ) (Map.toList desc)

data RevVar = LatchBlock (Maybe (Ptr CallInst)) (Ptr BasicBlock) Int
            | LatchValue (Maybe (Ptr CallInst)) (Ptr Instruction) RevValue
            | InputValue (Maybe (Ptr CallInst)) (Ptr Instruction) RevValue
            | ThreadArgument (Maybe (Ptr CallInst)) (Ptr Argument) RevValue
            | ThreadActivation (Ptr CallInst)
            | ThreadStep (Maybe (Ptr CallInst))
            | MemoryValue MemoryLoc RevAlloc
            | SizeValue MemoryLoc
            deriving (Typeable,Eq,Ord)

data RevValue = RevInt
              | RevBool
              | PtrCond MemoryPtr
              | PtrIdx MemoryPtr Int
              | ThreadIdCond (Ptr CallInst)
              deriving (Typeable,Eq,Ord)

data RevAlloc = RevStatic Integer [Integer] RevValue
              | RevDynamic [Integer] RevValue
              | RevSize
              deriving (Typeable,Eq,Ord)

instance Show RevVar where
  show (LatchBlock th blk sblk) = unsafePerformIO $ do
    blkName <- getNameString blk
    return $ "latch("++(case th of
                         Nothing -> "main-"
                         Just _ -> "thread-")++blkName++
      (if sblk==0
       then ""
       else "."++show sblk)++")"
  show (LatchValue th inst rev) = unsafePerformIO $ do
    iName <- getNameString inst
    return $ "latchv("++(case th of
                          Nothing -> "main-"
                          Just _ -> "thread-")++iName++" ~> "++show rev++")"
  show (InputValue th inst rev) = unsafePerformIO $ do
    iName <- getNameString inst
    return $ "inputv("++(case th of
                          Nothing -> "main-"
                          Just _ -> "thread-")++iName++" ~> "++show rev++")"
  show (ThreadArgument th arg rev) = unsafePerformIO $ do
    argName <- getNameString arg
    return $ "arg("++argName++" ~> "++show rev++")"
  show (ThreadActivation th) = "thread-act()"
  show (ThreadStep th) = "thread-step()"
  show (MemoryValue loc rev) = "mem("++showMemoryLoc loc ""++" ~> "++show rev++")"
  show (SizeValue loc) = "size("++showMemoryLoc loc ""++")"

instance Show RevValue where
  show RevInt = "int"
  show RevBool = "bool"
  show (PtrCond loc) = "ptrcond"
  show (PtrIdx loc i) = "ptridx"
  show (ThreadIdCond th) = "threadid"

instance Show RevAlloc where
  show (RevStatic top idx val)
    = "static"++(if top==0 then "" else "@"++show top)++
      (if null idx then "" else show idx)++"{"++show val++"}"
  show (RevDynamic idx val)
    = "dynamic"++(if null idx then "" else show idx)++"{"++show val++"}"
  show RevSize = "size"

debugInputs :: ProgramStateDesc
            -> ProgramInputDesc
            -> (ProgramState,ProgramInput)
debugInputs psd isd = (ps,is)
  where
    ps = ProgramState { mainState = ms
                      , threadState = ts
                      , memory = mem
                      }
    is = ProgramInput { mainInput = mi
                      , threadInput = ti
                      }
    ms = debugThreadState Nothing (mainStateDesc psd)
    ts = Map.mapWithKey (\th tsd -> (InternalObj (ThreadActivation th) (),
                                     debugThreadState (Just th) tsd)
                        ) (threadStateDesc psd)
    mi = debugThreadInput Nothing (mainInputDesc isd)
    ti = Map.mapWithKey (\th tsd -> debugThreadInput (Just th) tsd
                        ) (threadInputDesc isd)
    mem = Map.mapWithKey debugAllocVal (memoryDesc psd)
    debugThreadState th tsd
      = ThreadState { latchBlocks = lb
                    , latchValues = lv
                    , threadArgument = ta
                    }
      where
        lb = Map.mapWithKey (\(blk,sblk) _ -> InternalObj (LatchBlock th blk sblk) ()
                            ) (latchBlockDesc tsd)
        lv = Map.mapWithKey (\instr tp -> debugValue (LatchValue th instr) tp
                            ) (latchValueDesc tsd)
        ta = case threadArgumentDesc tsd of
          Nothing -> Nothing
          Just (arg,tp) -> Just (arg,debugValue (ThreadArgument th arg) tp)
    debugThreadInput th tsd
      = ThreadInput { step = InternalObj (ThreadStep th) ()
                    , nondets = Map.mapWithKey
                                (\instr tp -> debugValue (InputValue th instr) tp
                                ) (nondetTypes tsd)
                    }
    debugValue f TpBool = ValBool (InternalObj (f RevBool) ())
    debugValue f TpInt  = ValInt  (InternalObj (f RevInt) ())
    debugValue f (TpPtr trgs stp)
      = ValPtr { valPtr = Map.mapWithKey (\loc _ -> (InternalObj (f (PtrCond loc)) (),
                                                     [ InternalObj (f (PtrIdx loc n)) ()
                                                     | (n,_) <- zip [0..] [ () | DynamicAccess <- offsetPattern loc ] ])
                                         ) trgs
               , valPtrType = stp }
    debugValue f (TpThreadId ths)
      = ValThreadId (Map.mapWithKey (\th _ -> InternalObj (f (ThreadIdCond th)) ()
                                    ) ths)

    debugArr f TpBool = ArrBool (InternalObj (f RevBool) ((),()))
    debugArr f TpInt = ArrInt (InternalObj (f RevInt) ((),()))
    debugArr f (TpPtr trgs stp)
      = ArrPtr { arrPtr = Map.mapWithKey (\loc _ -> (InternalObj (f (PtrCond loc)) ((),()),
                                                     [ InternalObj (f (PtrIdx loc n)) ((),())
                                                     | (n,_) <- zip [0..]
                                                                [ () | DynamicAccess <- offsetPattern loc ] ])
                                         ) trgs
               , arrPtrType = stp }
    debugArr f (TpThreadId ths)
      = ArrThreadId (Map.mapWithKey (\th _ -> InternalObj (f (ThreadIdCond th)) ((),())
                                    ) ths)
    debugStruct f idx (Singleton tp) = Singleton (f idx tp)
    debugStruct f idx (Struct tps) = Struct [ debugStruct f (idx++[n]) tp
                                            | (n,tp) <- zip [0..] tps ]
    debugAllocVal loc (TpStatic n tp)
      = ValStatic [ debugStruct (\idx tp -> debugValue
                                            (\rev -> MemoryValue loc (RevStatic i idx rev)) tp
                                ) [] tp | i <- [0..n-1]]
    debugAllocVal loc (TpDynamic tp)
      = ValDynamic (debugStruct (\idx tp -> debugArr
                                            (\rev -> MemoryValue loc (RevDynamic idx rev)) tp
                                ) [] tp)
        (InternalObj (SizeValue loc) ())
