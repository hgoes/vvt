{-# LANGUAGE DeriveDataTypeable,TypeFamilies #-}
module Realization.Threaded.State where

import Args
import Realization.Threaded.Value

import Language.SMTLib2
import LLVM.FFI hiding (GetType,getType)
import Foreign.Ptr (Ptr)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable
import Text.Show
import Data.GADT.Show
import Data.GADT.Compare

data ThreadState e
  = ThreadState { latchBlocks :: Map (Ptr BasicBlock,Int) (e BoolType)
                , latchValues :: Map (Ptr Instruction) (SymVal e)
                , threadArgument :: Maybe (Ptr Argument,SymVal e)
                , threadGlobals :: Map (Ptr GlobalVariable) (AllocVal e)
                , threadReturn :: Maybe (SymVal e)
                } deriving (Typeable)

data RevThreadState tp where
  LatchBlock :: Ptr BasicBlock -> Int -> RevThreadState BoolType
  LatchValue :: Ptr Instruction -> RevValue tp -> RevThreadState tp
  ThreadArgument :: RevValue tp -> RevThreadState tp
  LocalMemory :: Ptr GlobalVariable -> RevAlloc tp -> RevThreadState tp
  ThreadReturn :: RevValue tp -> RevThreadState tp

data ThreadStateDesc = ThreadStateDesc { latchBlockDesc :: Map (Ptr BasicBlock,Int) ()
                                       , latchValueDesc :: Map (Ptr Instruction) SymType
                                       , threadArgumentDesc :: Maybe (Ptr Argument,SymType)
                                       , threadGlobalDesc :: Map (Ptr GlobalVariable) AllocType
                                       , threadReturnDesc :: Maybe SymType
                                       } deriving (Typeable,Eq,Ord,Show)

data ProgramState e
  = ProgramState { mainState :: ThreadState e
                 , threadState :: Map (Ptr CallInst) (e BoolType,ThreadState e)
                 , memory :: Map MemoryLoc (AllocVal e)
                 } deriving (Typeable)

data RevProgramState tp where
  MainState :: RevThreadState tp -> RevProgramState tp
  ThreadState' :: Ptr CallInst -> RevThreadState tp -> RevProgramState tp
  ThreadActivation :: Ptr CallInst -> RevProgramState BoolType
  GlobalMemory :: MemoryLoc -> RevAlloc tp -> RevProgramState tp

data ProgramStateDesc = ProgramStateDesc { mainStateDesc :: ThreadStateDesc
                                         , threadStateDesc :: Map (Ptr CallInst) ThreadStateDesc
                                         , memoryDesc :: Map MemoryLoc AllocType
                                         } deriving (Typeable,Eq,Ord)

data ThreadInput e
  = ThreadInput { step :: e BoolType
                , nondets :: Map (Ptr Instruction) (SymVal e)
                } deriving (Typeable)

data RevThreadInput tp where
  Step :: RevThreadInput BoolType
  Nondet :: Ptr Instruction -> RevValue tp -> RevThreadInput tp

newtype ThreadInputDesc = ThreadInputDesc { nondetTypes :: Map (Ptr Instruction) SymType }
                        deriving (Typeable,Eq,Ord,Show)

data ProgramInput e
  = ProgramInput { mainInput :: ThreadInput e
                 , threadInput :: Map (Ptr CallInst) (ThreadInput e)
                 } deriving (Typeable)

data RevProgramInput tp where
  MainInput :: RevThreadInput tp -> RevProgramInput tp
  ThreadInput' :: Ptr CallInst -> RevThreadInput tp -> RevProgramInput tp

data ProgramInputDesc = ProgramInputDesc { mainInputDesc :: ThreadInputDesc
                                         , threadInputDesc :: Map (Ptr CallInst) ThreadInputDesc
                                         } deriving (Typeable,Eq,Ord,Show)

instance GetType RevThreadState where
  getType (LatchBlock _ _) = bool
  getType (LatchValue _ rev) = getType rev
  getType (ThreadArgument rev) = getType rev
  getType (LocalMemory _ rev) = getType rev
  getType (ThreadReturn rev) = getType rev

instance Composite ThreadState where
  type CompDescr ThreadState = ThreadStateDesc
  type RevComp ThreadState = RevThreadState
  compositeType ts = ThreadState { latchBlocks = fmap (const BoolRepr) (latchBlockDesc ts)
                                 , latchValues = fmap compositeType (latchValueDesc ts)
                                 , threadArgument = fmap (\(arg,tp) -> (arg,compositeType tp)
                                                         ) (threadArgumentDesc ts)
                                 , threadGlobals = fmap compositeType (threadGlobalDesc ts)
                                 , threadReturn = fmap compositeType (threadReturnDesc ts) }
  foldExprs f ts = do
    nblks <- sequence $ Map.mapWithKey
             (\(blk,sblk) -> f (LatchBlock blk sblk))
             (latchBlocks ts)
    nvals <- sequence $ Map.mapWithKey
             (\i -> foldExprs (\rev -> f (LatchValue i rev)))
             (latchValues ts)
    narg <- mapM (\(arg,val) -> do
                     nval <- foldExprs (\rev -> f (ThreadArgument rev)) val
                     return (arg,nval)
                 ) (threadArgument ts)
    nglob <- sequence $ Map.mapWithKey
             (\g -> foldExprs (\rev -> f (LocalMemory g rev)))
             (threadGlobals ts)
    nret <- mapM (foldExprs (\rev -> f (ThreadReturn rev))) (threadReturn ts)
    return $ ThreadState { latchBlocks = nblks
                         , latchValues = nvals
                         , threadArgument = narg
                         , threadGlobals = nglob
                         , threadReturn = nret }
  accessComposite (LatchBlock blk sblk) ts = case Map.lookup (blk,sblk) (latchBlocks ts) of
    Just e -> e
    Nothing -> error $ "Failed to find block "++showBlock (blk,sblk) ""++" in state. Available: "++
               showListWith showBlock (Map.keys $ latchBlocks ts) ""
  accessComposite (LatchValue i rev) ts = case Map.lookup i (latchValues ts) of
    Just v -> accessComposite rev v
  accessComposite (ThreadArgument rev) ts = case threadArgument ts of
    Just (_,v) -> accessComposite rev v
  accessComposite (LocalMemory g rev) ts = case Map.lookup g (threadGlobals ts) of
    Just v -> accessComposite rev v
  accessComposite (ThreadReturn rev) ts = case threadReturn ts of
    Just ret -> accessComposite rev ret

instance GetType RevProgramState where
  getType (MainState rev) = getType rev
  getType (ThreadState' _ rev) = getType rev
  getType (ThreadActivation _) = bool
  getType (GlobalMemory _ rev) = getType rev

instance Composite ProgramState where
  type CompDescr ProgramState = ProgramStateDesc
  type RevComp ProgramState = RevProgramState
  compositeType ps = ProgramState { mainState = compositeType (mainStateDesc ps)
                                  , threadState = fmap (\d -> (BoolRepr,compositeType d))
                                                  (threadStateDesc ps)
                                  , memory = fmap compositeType (memoryDesc ps) }
  foldExprs f ps = do
    nmain <- foldExprs (\rev -> f (MainState rev)) (mainState ps)
    nths <- sequence $ Map.mapWithKey
            (\th (act,ts) -> do
                nact <- f (ThreadActivation th) act
                nts <- foldExprs (\rev -> f (ThreadState' th rev)) ts
                return (nact,nts)) (threadState ps)
    nmem <- sequence $ Map.mapWithKey
            (\loc val -> foldExprs (\rev -> f (GlobalMemory loc rev)) val)
            (memory ps)
    return $ ProgramState { mainState = nmain
                          , threadState = nths
                          , memory = nmem }
  accessComposite (MainState rev) ps = accessComposite rev (mainState ps)
  accessComposite (ThreadState' th rev) ps = case Map.lookup th (threadState ps) of
    Just (_,st) -> accessComposite rev st
  accessComposite (ThreadActivation th) ps = case Map.lookup th (threadState ps) of
    Just (act,_) -> act
  accessComposite (GlobalMemory g rev) ps = case Map.lookup g (memory ps) of
    Just val -> accessComposite rev val

instance GetType RevThreadInput where
  getType Step = bool
  getType (Nondet _ rev) = getType rev

instance Composite ThreadInput where
  type CompDescr ThreadInput = ThreadInputDesc
  type RevComp ThreadInput = RevThreadInput
  compositeType ti = ThreadInput { step = BoolRepr
                                 , nondets = fmap compositeType (nondetTypes ti) }
  foldExprs f ti = do
    nstep <- f Step (step ti)
    nnd <- sequence $ Map.mapWithKey
           (\i -> foldExprs (\rev -> f (Nondet i rev)))
           (nondets ti)
    return ThreadInput { step = nstep
                       , nondets = nnd }
  accessComposite Step ti = step ti
  accessComposite (Nondet i rev) ti = case Map.lookup i (nondets ti) of
    Just val -> accessComposite rev val

instance GetType RevProgramInput where
  getType (MainInput rev) = getType rev
  getType (ThreadInput' _ rev) = getType rev

instance Composite ProgramInput where
  type CompDescr ProgramInput = ProgramInputDesc
  type RevComp ProgramInput = RevProgramInput
  compositeType pi = ProgramInput { mainInput = compositeType (mainInputDesc pi)
                                  , threadInput = fmap compositeType (threadInputDesc pi) }
  foldExprs f pi = do
    nmain <- foldExprs (\rev -> f (MainInput rev)) (mainInput pi)
    nths <- sequence $ Map.mapWithKey
            (\th -> foldExprs (\rev -> f (ThreadInput' th rev)))
            (threadInput pi)
    return ProgramInput { mainInput = nmain
                        , threadInput = nths }
  accessComposite (MainInput rev) pi
    = accessComposite rev (mainInput pi)
  accessComposite (ThreadInput' th rev) pi = case Map.lookup th (threadInput pi) of
    Just inp -> accessComposite rev inp

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

getThreadState :: Maybe (Ptr CallInst) -> ProgramState e -> ThreadState e
getThreadState Nothing st = mainState st
getThreadState (Just th) st = case Map.lookup th (threadState st) of
  Just (_,ts) -> ts
  Nothing -> error $ "getThreadState: Couldn't get thread state for "++show th

getThreadStateDesc :: Maybe (Ptr CallInst) -> ProgramStateDesc -> ThreadStateDesc
getThreadStateDesc Nothing ps = mainStateDesc ps
getThreadStateDesc (Just th) st = case Map.lookup th (threadStateDesc st) of
  Just desc -> desc
  Nothing -> error $ "getThreadStateDesc: Couldn't get thread state description for "++show th

getThreadInput :: Maybe (Ptr CallInst) -> ProgramInput e -> ThreadInput e
getThreadInput Nothing inp = mainInput inp
getThreadInput (Just th) inp = case Map.lookup th (threadInput inp) of
  Just inp -> inp
  Nothing -> error $ "getThreadInput: Couldn't get input for thread "++show th

{-debugInputs :: ProgramStateDesc
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
                    , threadGlobals = tm
                    , threadReturn = tr
                    }
      where
        lb = Map.mapWithKey (\(blk,sblk) _ -> InternalObj (LatchBlock th blk sblk) ()
                            ) (latchBlockDesc tsd)
        lv = Map.mapWithKey (\instr tp -> debugValue (LatchValue th instr) tp
                            ) (latchValueDesc tsd)
        ta = case threadArgumentDesc tsd of
          Nothing -> Nothing
          Just (arg,tp) -> Just (arg,debugValue (ThreadArgument th arg) tp)
        tm = Map.mapWithKey (debugLocalAllocVal th) (threadGlobalDesc tsd)
        tr = case threadReturnDesc tsd of
          Nothing -> Nothing
          Just tp -> Just $ debugValue (ThreadReturn th) tp
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
    debugLocalAllocVal th loc (TpStatic n tp)
      = ValStatic [ debugStruct (\idx tp -> debugValue
                                            (\rev -> LocalMemoryValue th loc
                                                     (RevStatic i idx rev)) tp
                                ) [] tp | i <- [0..n-1]]
    debugLocalAllocVal th loc (TpDynamic tp)
      = ValDynamic (debugStruct (\idx tp -> debugArr
                                            (\rev -> LocalMemoryValue th loc
                                                     (RevDynamic idx rev)) tp
                                ) [] tp)
        (InternalObj (SizeValue (Right loc)) ())
-}

instance GShow e => Show (ThreadState e) where
  showsPrec p ts = showString "ThreadState {latchBlocks = " .
                   showAssoc showBlock (gshowsPrec 9) (latchBlocks ts) .
                   showString ", latchValues = " .
                   showAssoc showValue (showsPrec 9) (latchValues ts) .
                   showString ", threadArgument = " .
                   (case threadArgument ts of
                     Nothing -> showString "_|_"
                     Just (arg,val) -> showsPrec 0 val) .
                   showString ", threadGlobals = " .
                   showAssoc showValue (showsPrec 9) (threadGlobals ts) .
                   showString ", threadReturn = " .
                   (case threadReturn ts of
                     Nothing -> showString "_|_"
                     Just val -> showsPrec 0 val) .
                   showChar '}'

{-instance GShow e => Show (ProgramState e) where
  showsPrec p ps = showString "ProgramState {mainState = " .
                   showsPrec 1 (mainState ps) .
                   showString ", threadState = " .
                   showAssoc showValue (\(c,ts) -> showChar '(' .
                                                   gshowsPrec 0 c .
                                                   showChar ',' .
                                                   showsPrec 0 ts .
                                                   showChar ')'
                                       ) (threadState ps) .
                   showString ", memory = " .
                   showAssoc (showsPrec 9) (showsPrec 9) (memory ps) .
                   showChar '}'-}

instance GShow e => Show (ThreadInput e) where
  showsPrec p ti = showString "ThreadInput {step = " .
                   gshowsPrec 1 (step ti) .
                   showString ", nondets = " .
                   showAssoc showValue (showsPrec 9) (nondets ti) .
                   showChar '}'

deriving instance GShow e => Show (ProgramInput e)
                   
instance GEq RevThreadState where
  geq (LatchBlock b1 s1) (LatchBlock b2 s2)
    = if b1==b2 && s1==s2
      then Just Refl
      else Nothing
  geq (LatchValue i1 rev1) (LatchValue i2 rev2)
    = if i1==i2
      then case geq rev1 rev2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq (ThreadArgument rev1) (ThreadArgument rev2)
    = case geq rev1 rev2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (LocalMemory g1 rev1) (LocalMemory g2 rev2)
    = if g1==g2
      then case geq rev1 rev2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq (ThreadReturn rev1) (ThreadReturn rev2)
    = case geq rev1 rev2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq _ _ = Nothing

instance GCompare RevThreadState where
  gcompare (LatchBlock b1 s1) (LatchBlock b2 s2) = case compare (b1,s1) (b2,s2) of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (LatchBlock _ _) _ = GLT
  gcompare _ (LatchBlock _ _) = GGT
  gcompare (LatchValue i1 r1) (LatchValue i2 r2) = case compare i1 i2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (LatchValue _ _) _ = GLT
  gcompare _ (LatchValue _ _) = GGT
  gcompare (ThreadArgument r1) (ThreadArgument r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (ThreadArgument _) _ = GLT
  gcompare _ (ThreadArgument _) = GGT
  gcompare (LocalMemory g1 r1) (LocalMemory g2 r2) = case compare g1 g2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (LocalMemory _ _) _ = GLT
  gcompare _ (LocalMemory _ _) = GGT
  gcompare (ThreadReturn r1) (ThreadReturn r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance Show (RevThreadState tp) where
  showsPrec p (LatchBlock blk sblk) = showParen (p>10) $
                                      showString "blk " .
                                      showBlock (blk,sblk)
  showsPrec p (LatchValue i rev) = showParen (p>10) $
                                   showString "instr " .
                                   showValue i .
                                   showChar ' ' .
                                   showsPrec 11 rev
  showsPrec p (ThreadArgument rev) = showParen (p>10) $
                                     showString "arg " .
                                     showsPrec 11 rev
  showsPrec p (LocalMemory g rev) = showParen (p>10) $
                                    showString "local " .
                                    showValue g .
                                    showChar ' ' .
                                    showsPrec 11 rev
  showsPrec p (ThreadReturn rev) = showParen (p>10) $
                                   showString "return " .
                                   showsPrec 11 rev

instance GShow RevThreadState where
  gshowsPrec = showsPrec

instance GEq RevProgramState where
  geq (MainState s1) (MainState s2) = case geq s1 s2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (ThreadState' t1 s1) (ThreadState' t2 s2)
    = if t1==t2
      then case geq s1 s2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq (ThreadActivation t1) (ThreadActivation t2)
    = if t1==t2
      then Just Refl
      else Nothing
  geq (GlobalMemory l1 r1) (GlobalMemory l2 r2)
    = if l1==l2
      then case geq r1 r2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq _ _ = Nothing

instance GCompare RevProgramState where
  gcompare (MainState s1) (MainState s2) = case gcompare s1 s2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (MainState _) _ = GLT
  gcompare _ (MainState _) = GGT
  gcompare (ThreadState' t1 s1) (ThreadState' t2 s2) = case compare t1 t2 of
    EQ -> case gcompare s1 s2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (ThreadState' _ _) _ = GLT
  gcompare _ (ThreadState' _ _) = GGT
  gcompare (ThreadActivation t1) (ThreadActivation t2) = case compare t1 t2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (ThreadActivation _) _ = GLT
  gcompare _ (ThreadActivation _) = GGT
  gcompare (GlobalMemory g1 r1) (GlobalMemory g2 r2) = case compare g1 g2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT

instance Show (RevProgramState tp) where
  showsPrec p (MainState rev) = showParen (p>10) $
                                showString "main " .
                                showsPrec 11 rev
  showsPrec p (ThreadState' t rev) = showParen (p>10) $
                                     showString "thread " .
                                     showsPrec 11 t .
                                     showChar ' ' .
                                     showsPrec 11 rev
  showsPrec p (ThreadActivation t) = showParen (p>10) $
                                     showString "act " .
                                     showsPrec 11 t
  showsPrec p (GlobalMemory g rev) = showParen (p>10) $
                                     showString "global " .
                                     (case g of
                                       Left i -> showString "alloc-" .
                                                 showValue i
                                       Right g -> showString "global-" .
                                                  showValue g) .
                                     showChar ' ' .
                                     showsPrec 11 rev

instance GShow RevProgramState where
  gshowsPrec = showsPrec

instance GEq RevThreadInput where
  geq Step Step = Just Refl
  geq (Nondet i1 r1) (Nondet i2 r2)
    = if i1==i2
      then case geq r1 r2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq _ _ = Nothing

instance GCompare RevThreadInput where
  gcompare Step Step = GEQ
  gcompare Step _ = GLT
  gcompare _ Step = GGT
  gcompare (Nondet i1 r1) (Nondet i2 r2) = case compare i1 i2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT

instance Show (RevThreadInput tp) where
  showsPrec p Step = showString "step"
  showsPrec p (Nondet i rev) = showParen (p>10) $
                               showString "nondet " .
                               showValue i .
                               showChar ' ' .
                               showsPrec 11 rev

instance GShow RevThreadInput where
  gshowsPrec = showsPrec

instance GEq RevProgramInput where
  geq (MainInput r1) (MainInput r2) = case geq r1 r2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (ThreadInput' t1 r1) (ThreadInput' t2 r2)
    = if t1==t2
      then case geq r1 r2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq _ _ = Nothing

instance GCompare RevProgramInput where
  gcompare (MainInput r1) (MainInput r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (MainInput _) _ = GLT
  gcompare _ (MainInput _) = GGT
  gcompare (ThreadInput' t1 r1) (ThreadInput' t2 r2) = case compare t1 t2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT

instance Show (RevProgramInput tp) where
  showsPrec p (MainInput rev) = showParen (p>10) $
                                showString "main " .
                                showsPrec 11 rev
  showsPrec p (ThreadInput' t rev) = showParen (p>10) $
                                     showString "thread " .
                                     showsPrec 11 t .
                                     showChar ' ' .
                                     showsPrec 11 rev

instance GShow RevProgramInput where
  gshowsPrec = showsPrec

instance Show ProgramStateDesc where
  showsPrec p pd = showString "{ main = " .
                   showThreadStateDesc mp (mainStateDesc pd) .
                   showString ", threads = " .
                   showListWith
                   (\(n,ts) -> showString "thread" .
                               showsPrec 0 n .
                               showString " ~> " .
                               showThreadStateDesc mp ts)
                   (zip [1..] (Map.elems $ threadStateDesc pd)) .
                   showString ", mem = " .
                   showListWith
                   (\(loc,tp) -> (case loc of
                                   Left i -> showString "alloc-" .
                                             showValue i
                                   Right g -> showString "global-" .
                                              showValue g) .
                                 showString " : " .
                                 showAllocType mp tp)
                   (Map.toList (memoryDesc pd)) .
                   showChar '}'
    where
      mp = Map.fromList [ (th,"thread"++show n)
                        | (n,th) <- zip [1..] (Map.keys $ threadStateDesc pd) ]

instance GShow e => Show (ProgramState e) where
  showsPrec p ps
    = showString "{ main = " .
      showThreadState mp (mainState ps) .
      showString ", threads = " .
      showListWith
      (\(n,(act,ts)) -> showString "thread" .
                  showsPrec 0 n .
                  showString " ~> (" .
                  gshowsPrec 0 act .
                  showChar ',' .
                  showThreadState mp ts .
                  showChar ')')
      (zip [1..] (Map.elems $ threadState ps)) .
      showString ", mem = " .
      showListWith
      (\(loc,val) -> (case loc of
                       Left i -> showString "alloc-" .
                                 showValue i
                       Right g -> showString "global-" .
                                  showValue g) .
                     showString " ~> " .
                     showAllocVal mp val) (Map.toList $ memory ps) .
      showChar '}'
    where
      mp = Map.fromList [ (th,"thread"++show n)
                        | (n,th) <- zip [1..] (Map.keys $ threadState ps) ]

showThreadState :: GShow e => Map (Ptr CallInst) String -> ThreadState e -> ShowS
showThreadState mp ts
  = showString "{ blocks = " .
    showListWith (\(blk,def) -> showBlock blk .
                                showString " ~> " .
                                gshowsPrec 0 def) (Map.toList $ latchBlocks ts) .
    showString ", values = " .
    showListWith (\(i,val) -> showValue i .
                              showString " ~> " .
                              showSymValue mp val) (Map.toList $ latchValues ts) .
    (case threadArgument ts of
      Nothing -> showString ", no arg"
      Just (_,arg) -> showString ", arg = " . showSymValue mp arg) .
    (case threadReturn ts of
      Nothing -> showString ", no return"
      Just ret -> showString ", return = " . showSymValue mp ret) .
    showString ", globals = " .
    showListWith (\(g,def) -> showValue g .
                              showString " ~> " .
                              showAllocVal mp def) (Map.toList $ threadGlobals ts) .
    showChar '}'

showThreadStateDesc :: Map (Ptr CallInst) String -> ThreadStateDesc -> ShowS
showThreadStateDesc mp td
  = showString "{ blocks = " .
    showListWith showBlock (Map.keys $ latchBlockDesc td) .
    showString ", values = " .
    showListWith
    (\(i,tp) -> showValue i .
                showString " : " .
                showSymType mp tp)
    (Map.toList $ latchValueDesc td) .
    (case threadArgumentDesc td of
      Nothing -> showString ", no arg"
      Just (arg,tp) -> showString ", arg : " .
                       showSymType mp tp) .
    (case threadReturnDesc td of
      Nothing -> showString ", no return"
      Just tp -> showString ", return : " .
                 showSymType mp tp) .
    showString ", globals = " .
    showListWith
    (\(g,tp) -> showValue g .
                showString " : " .
                showAllocType mp tp)
    (Map.toList $ threadGlobalDesc td) .
    showChar '}'
