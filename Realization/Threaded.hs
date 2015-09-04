{-# LANGUAGE ViewPatterns,ScopedTypeVariables,TypeFamilies,DeriveDataTypeable,
             PackageImports #-}
module Realization.Threaded where

import Realization.Threaded.ProgramInfo (ProgramInfo(..),ThreadInfo(..),
                                         AllocInfo(..),
                                         getProgramInfo)
import Realization.Threaded.ThreadFinder (Quantity(..))
import Realization.Threaded.Value
import Realization.Threaded.State
import Realization.Common (getFunctionName)
import Gates

import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)

import LLVM.FFI
import Foreign.Ptr (Ptr,nullPtr)
import Foreign.Storable (peek)
import Foreign.Marshal.Array (peekArray)
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import "mtl" Control.Monad.State (StateT,runStateT,get,put,lift,liftIO,MonadIO)
import Data.Foldable
import Data.Traversable
import Data.List (genericReplicate,genericIndex)
import Prelude hiding (foldl,sequence,mapM,mapM_,concat)
import Control.Exception
import System.IO.Unsafe

import Debug.Trace

data DefinitionState inp = AlwaysDefined (inp -> SMTExpr Bool)
                         | SometimesDefined (inp -> SMTExpr Bool)
                         | NeverDefined

data AlternativeRepresentation inp = IntConst Integer
                                   | OrList [inp -> SymVal]
                                   | ExtBool (inp -> SMTExpr Bool)

data InstructionValue inp = InstructionValue { symbolicType :: SymType
                                             , symbolicValue :: inp -> SymVal
                                             , alternative :: Maybe (AlternativeRepresentation inp)
                                             }

data Edge inp = Edge { edgeValues :: Map (Maybe (Ptr CallInst),Ptr Instruction)
                                     (DefinitionState inp)
                     , edgeConditions :: [EdgeCondition inp]
                     , observedEvents :: Map Int ()
                     }

data EdgeCondition inp = EdgeCondition { edgeActivation :: inp -> SMTExpr Bool
                                       , edgePhis :: Map (Maybe (Ptr CallInst),Ptr Instruction)
                                                     (InstructionValue inp)
                                       }

data Event inp = WriteEvent { target :: Map MemoryPtr (inp -> (SMTExpr Bool,[SMTExpr Integer]))
                            , writeContent :: InstructionValue inp
                            , eventOrigin :: Ptr Instruction -- For debugging
                            }

data Realization inp = Realization { edges :: Map (Maybe (Ptr CallInst),Ptr BasicBlock,Int)
                                              (Edge inp)
                                   , yieldEdges :: Map (Maybe (Ptr CallInst),Ptr BasicBlock,Int)
                                                   (Edge inp)
                                   , internalYieldEdges :: Map (Maybe (Ptr CallInst),Ptr BasicBlock,Int)
                                                           (Edge inp)
                                   , instructions :: Map (Maybe (Ptr CallInst),Ptr Instruction)
                                                     (InstructionValue inp)
                                   , stateAnnotation :: ProgramStateDesc
                                   , inputAnnotation :: ProgramInputDesc
                                   , gateMp :: GateMap inp
                                   , events :: Map Int (Event inp)
                                   , spawnEvents :: Map (Ptr CallInst) [(inp -> SMTExpr Bool,
                                                                         Maybe (InstructionValue inp))]
                                   , termEvents :: Map (Ptr CallInst) [inp -> SMTExpr Bool]
                                   , assertions :: [inp -> SMTExpr Bool]
                                   , memoryInit :: Map (Ptr GlobalVariable) AllocVal
                                   , mainBlock :: Ptr BasicBlock
                                   , threadBlocks :: Map (Ptr CallInst) (Ptr BasicBlock)
                                   , programInfo :: ProgramInfo
                                   }

mkAnd :: [SMTExpr Bool] -> SMTExpr Bool
mkAnd [] = constant True
mkAnd [x] = x
mkAnd xs = app and' xs

mkOr :: [SMTExpr Bool] -> SMTExpr Bool
mkOr [] = constant False
mkOr [x] = x
mkOr xs = app or' xs

constantIntValue :: Integer -> InstructionValue inp
constantIntValue n = InstructionValue { symbolicType = TpInt
                                      , symbolicValue = \_ -> ValInt (constant n)
                                      , alternative = Just $ IntConst n }

constantBoolValue :: Bool -> InstructionValue inp
constantBoolValue n = InstructionValue { symbolicType = TpBool
                                       , symbolicValue = \_ -> ValBool (constant n)
                                       , alternative = Nothing }

realizeProgram :: Ptr Module -> Ptr Function -> IO (Realization (ProgramState,ProgramInput))
realizeProgram mod fun = do
  info <- getProgramInfo mod fun
  globals <- moduleGetGlobalList mod >>= ipListToList
  globSig <- foldlM (\mp glob -> do
                        ptrTp <- getType glob
                        tp <- sequentialTypeGetElementType ptrTp
                        symTp <- translateType0 tp
                        return $ Map.insert (Right glob) (TpStatic 1 symTp) mp
                    ) Map.empty globals
  globInit <- foldlM (\mp glob -> do
                         init <- globalVariableGetInitializer glob
                         val <- getConstant init
                         return $ Map.insert glob (ValStatic [val]) mp -- XXX: What about array initializations?
                     ) Map.empty globals
  allocSig <- sequence $ Map.mapWithKey
              (\alloc info -> do
                  tp <- translateType0 (allocType info)
                  case allocSize info of
                   Nothing -> return $ case allocQuantity info of
                     Finite n -> TpStatic n tp
                     Infinite -> TpDynamic tp
                   Just sz -> case allocQuantity info of
                     Finite 1 -> return $ TpDynamic tp
                     _ -> error $ "Dynamic allocations in a loop not yet supported."
              ) (allocations info)
  let allocSig' = Map.mapKeysMonotonic Left allocSig
      sigs = typeBasedReachability (Map.union globSig allocSig')
  let th0 tinfo = do
        arg <- case threadArg tinfo of
          Nothing -> return Nothing
          Just (val,rtp) -> do
            tp <- translateType0 rtp
            return (Just (val,TpPtr (allPtrsOfType tp sigs) tp))
        return $ ThreadStateDesc { latchBlockDesc = entryPoints tinfo
                                 , latchValueDesc = Map.empty
                                 , threadArgumentDesc = arg }
      th_inp = ThreadInputDesc Map.empty
  mainBlk <- getEntryBlock fun
  thBlks <- sequence $ Map.mapWithKey
            (\th _ -> do
                threadVal <- callInstGetArgOperand th 2
                case castDown threadVal of
                 Just threadFun -> getEntryBlock threadFun
            ) (threads info)
  mainDesc <- th0 (mainThread info)
  thDesc <- fmap (typeBasedArgumentReachability sigs) $ mapM th0 (threads info)
  let sigs' = threadBasedReachability (fmap (const ()) (threads info)) sigs
      real0 = Realization { edges = Map.empty
                          , yieldEdges = Map.empty
                          , internalYieldEdges = Map.empty
                          , instructions = Map.empty
                          , stateAnnotation = ProgramStateDesc { mainStateDesc = mainDesc
                                                               , threadStateDesc = thDesc
                                                               , memoryDesc = sigs' }
                          , inputAnnotation = ProgramInputDesc { mainInputDesc = th_inp
                                                               , threadInputDesc = fmap (const th_inp)
                                                                                   (threads info) }
                          , gateMp = Map.empty
                          , events = Map.empty
                          , spawnEvents = Map.empty
                          , termEvents = Map.empty
                          , assertions = []
                          , memoryInit = globInit
                          , mainBlock = mainBlk
                          , threadBlocks = thBlks
                          , programInfo = info
                          }
  --putStrLn $ "Memory description: "++showMemoryDesc sigs' ""
  --putStrLn $ "Thread description: "++show (fmap (\ts -> do
  --                                                  (_,tp) <- threadArgumentDesc ts
  --                                                  return tp)
  --                                         thDesc)
  real1 <- realizeThread info Nothing (mainThread info) real0
  foldlM (\creal (call,th) -> realizeThread info (Just call) th creal
         ) real1 (Map.toList (threads info))
  where
    realizeThread info th tinfo real
      = foldlM (\creal (blk,sblk) -> realizeBlock th blk sblk info creal) real
        (blockOrder tinfo)

realizeInstructions :: Maybe (Ptr CallInst)
                    -> Ptr BasicBlock
                    -> Int
                    -> ((ProgramState,ProgramInput) -> SMTExpr Bool)
                    -> [Ptr Instruction]
                    -> Edge (ProgramState,ProgramInput)
                    -> Realization (ProgramState,ProgramInput)
                    -> IO (Realization (ProgramState,ProgramInput))
realizeInstructions thread blk sblk act (i:is) edge real = do
  --iStr <- valueToString i
  --putStrLn $ "Realizing "++iStr
  (res,nact,nreal) <- realizeInstruction thread blk sblk act i edge real
  case res of
   Nothing -> return nreal
   Just nedge -> realizeInstructions thread blk sblk nact is nedge nreal

realizeInstruction :: Maybe (Ptr CallInst)
                   -> Ptr BasicBlock
                   -> Int
                   -> ((ProgramState,ProgramInput) -> SMTExpr Bool)
                   -> Ptr Instruction
                   -> Edge (ProgramState,ProgramInput)
                   -> Realization (ProgramState,ProgramInput)
                   -> IO (Maybe (Edge (ProgramState,ProgramInput)),
                          (ProgramState,ProgramInput) -> SMTExpr Bool,
                          Realization (ProgramState,ProgramInput))
realizeInstruction thread blk sblk act i@(castDown -> Just call) edge real0 = do
  fname <- getFunctionName call
  case fname of
   "pthread_create" -> do
     thId <- getOperand call 0
     -- Get the pointer to the thread id
     (thId',real1) <- realizeValue thread thId edge real0
     -- Write to the thread id
     (arg,real2) <- case threadArgumentDesc $ getThreadStateDesc (Just call) (stateAnnotation real1) of
       Nothing -> return (Nothing,real1)
       Just _ -> do
         arg <- getOperand call 3
         (arg',nreal) <- realizeValue thread arg edge real1
         return (Just arg',nreal)
     return (Just edge { observedEvents = Map.insert (Map.size (events real2)) ()
                                          (observedEvents edge)
                       , edgeValues = Map.insert (thread,i) (AlwaysDefined act) (edgeValues edge) },
             act,
             real2 { events = Map.insert (Map.size (events real2))
                              (WriteEvent { target = Map.mapWithKey
                                                     (\loc _ inp
                                                      -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue thId' inp) of
                                                                            Just r -> r
                                                         in ((act inp) .&&. cond,idx)
                                                     ) (tpPtr $ symbolicType thId')
                                          , writeContent = InstructionValue { symbolicType = TpThreadId (Map.singleton call ())
                                                                            , symbolicValue = \_ -> ValThreadId $ Map.singleton call (constant True)
                                                                            , alternative = Nothing }
                                          , eventOrigin = castUp call
                                          }) (events real2)
                   , spawnEvents = Map.insertWith (++) call [(act,arg)] (spawnEvents real2)
                   , instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real2) })
   "pthread_join" -> do
     thId <- getOperand call 0
     (thId',real1) <- realizeValue thread thId edge real0
     let rthId = memoryRead i thId' edge real1
         gt inp = mkOr [ cact .&&. (not' $ fst $ case Map.lookup call' (threadState $ fst inp) of
                                                   Just r -> r)
                       | (call',cact) <- Map.toList $ valThreadId $
                                         symbolicValue rthId inp ]
         (cond,ngates) = addGate (gateMp real1)
                         (Gate { gateTransfer = gt
                               , gateAnnotation = ()
                               , gateName = Just "blocking"
                               })
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act) (edgeValues edge) },
             \inp -> (act inp) .&&. cond,
             real1 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real1)
                   , gateMp = ngates
                   })
   "assert" -> do
     val <- getOperand call 0
     (val',real1) <- realizeValue thread val edge real0
     let dontStep = Map.null (threadStateDesc $ stateAnnotation real1)
     return (Just edge,
             act,
             real1 { assertions = (\inp -> (if dontStep
                                            then act inp
                                            else act inp .&&. (step $ getThreadInput thread (snd inp)))
                                           .=>. (valBool $ symbolicValue val' inp)):
                                  (assertions real1)
                   })
   "pthread_mutex_init" -> do
     -- Ignore this call for now...
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge) },
             act,
             real0 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real0) })
   "pthread_mutex_destroy" -> do
     -- Ignore this call for now...
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge) },
             act,
             real0 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real0) })
   "pthread_mutex_lock" -> do
     ptr <- getOperand call 0
     (ptr',real1) <- realizeValue thread ptr edge real0
     let lock = memoryRead i ptr' edge real1
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge)
                       , observedEvents = Map.insert (Map.size (events real1)) ()
                                          (observedEvents edge) },
             \inp -> (act inp) .&&. (not' $ valBool $ symbolicValue lock inp),
             real1 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real1)
                   , events = Map.insert (Map.size (events real1))
                              (WriteEvent { target = Map.mapWithKey
                                                     (\loc _ inp
                                                      -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr' inp) of
                                                                            Just r -> r
                                                         in ((act inp) .&&. cond,idx))
                                                     (tpPtr $ symbolicType ptr')
                                          , writeContent = constantBoolValue True
                                          , eventOrigin = castUp call
                                          }) (events real1) })
   "pthread_mutex_unlock" -> do
     ptr <- getOperand call 0
     (ptr',real1) <- realizeValue thread ptr edge real0
     let lock = memoryRead i ptr' edge real1
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge)
                       , observedEvents = Map.insert (Map.size (events real1)) ()
                                          (observedEvents edge) },
             act,
             real1 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real1)
                   , events = Map.insert (Map.size (events real1))
                              (WriteEvent { target = Map.mapWithKey
                                                     (\loc _ inp
                                                      -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr' inp) of
                                                                            Just r -> r
                                                         in ((act inp) .&&. cond,idx))
                                                     (tpPtr $ symbolicType ptr')
                                          , writeContent = constantBoolValue False
                                          , eventOrigin = castUp call
                                          }) (events real1) })
   "pthread_rwlock_init" -> do
     -- Ignore this call for now
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge) },
             act,
             real0 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real0) })
   "pthread_rwlock_destroy" -> do
     -- Ignore this call for now...
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge) },
             act,
             real0 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real0) })
   "pthread_rwlock_rdlock" -> do
     ptr <- getOperand call 0
     (ptr',real1) <- realizeValue thread ptr edge real0
     let lock = memoryRead i ptr' edge real1
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge)
                       , observedEvents = Map.insert (Map.size (events real1)) ()
                                          (observedEvents edge) },
             \inp -> (act inp) .&&. (not' $ valBool $ head $ valVector $ symbolicValue lock inp),
             real1 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real1)
                   , events = Map.insert (Map.size (events real1))
                              (WriteEvent { target = Map.mapWithKey
                                                     (\loc _ inp
                                                      -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr' inp) of
                                                                            Just r -> r
                                                         in ((act inp) .&&. cond,idx))
                                                     (tpPtr $ symbolicType ptr')
                                          , writeContent = InstructionValue { symbolicType = TpVector [TpBool,TpInt]
                                                                            , symbolicValue = \inp -> case symbolicValue lock inp of
                                                                               ValVector [wr,ValInt rd] -> ValVector [wr,ValInt (rd+1)]
                                                                            , alternative = Nothing }
                                          , eventOrigin = castUp call
                                          }) (events real1) })
   "pthread_rwlock_wrlock" -> do
     ptr <- getOperand call 0
     (ptr',real1) <- realizeValue thread ptr edge real0
     let lock = memoryRead i ptr' edge real1
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge)
                       , observedEvents = Map.insert (Map.size (events real1)) ()
                                          (observedEvents edge) },
             \inp -> (act inp) .&&.
                     (not' $ valBool $ head $ valVector $ symbolicValue lock inp) .&&.
                     ((valInt $ (valVector $ symbolicValue lock inp)!!1) .==. 0),
             real1 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real1)
                   , events = Map.insert (Map.size (events real1))
                              (WriteEvent { target = Map.mapWithKey
                                                     (\loc _ inp
                                                      -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr' inp) of
                                                                            Just r -> r
                                                         in ((act inp) .&&. cond,idx))
                                                     (tpPtr $ symbolicType ptr')
                                          , writeContent = InstructionValue { symbolicType = TpVector [TpBool,TpInt]
                                                                            , symbolicValue = \inp -> ValVector [ValBool (constant True),ValInt 0]
                                                                            , alternative = Nothing }
                                          , eventOrigin = castUp call
                                          }) (events real1) })
   "pthread_rwlock_unlock" -> do
     ptr <- getOperand call 0
     (ptr',real1) <- realizeValue thread ptr edge real0
     let lock = memoryRead i ptr' edge real1
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act)
                                      (edgeValues edge)
                       , observedEvents = Map.insert (Map.size (events real1)) ()
                                          (observedEvents edge) },
             act,
             real1 { instructions = Map.insert (thread,i)
                                    (constantIntValue 0)
                                    (instructions real1)
                   , events = Map.insert (Map.size (events real1))
                              (WriteEvent { target = Map.mapWithKey
                                                     (\loc _ inp
                                                      -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr' inp) of
                                                                            Just r -> r
                                                         in ((act inp) .&&. cond,idx))
                                                     (tpPtr $ symbolicType ptr')
                                          , writeContent = InstructionValue { symbolicType = TpVector [TpBool,TpInt]
                                                                            , symbolicValue = \inp -> case symbolicValue lock inp of
                                                                                                       ValVector [ValBool wr,ValInt rd]
                                                                                                         -> ValVector [ValBool (constant False)
                                                                                                                      ,ValInt (ite (rd.==.0) 0 (rd-1))]
                                                                            , alternative = Nothing }
                                          , eventOrigin = castUp call
                                          }) (events real1) })
   "pthread_yield"
     -> return (Nothing,
                act,
                real0 { yieldEdges = Map.insert (thread,blk,sblk+1)
                                     (edge { edgeConditions = [EdgeCondition act Map.empty] })
                                     (yieldEdges real0) })
   "__yield"
     -> return (Nothing,
                act,
                real0 { yieldEdges = Map.insert (thread,blk,sblk+1)
                                     (edge { edgeConditions = [EdgeCondition act Map.empty] })
                                     (yieldEdges real0) })
   "__yield_local"
     -> return (Nothing,act,
                real0 { internalYieldEdges = Map.insert (thread,blk,sblk+1)
                                             (edge { edgeConditions = [EdgeCondition act Map.empty] })
                                             (internalYieldEdges real0) })
   "assume" -> do
     cond <- getOperand call 0
     (cond',real1) <- realizeValue thread cond edge real0
     return (Just edge,\inp -> (valBool $ symbolicValue cond' inp) .&&. (act inp),real1)
   "pthread_exit" -> case thread of
     Nothing -> return (Nothing,act,real0)
     Just th -> return (Nothing,act,
                        real0 { termEvents = Map.insertWith (++) th [act] (termEvents real0) })
   -- Ignore atomic block denotions
   -- Only important for inserting yield instructions
   "__atomic_begin" -> return (Just edge,act,real0)
   "__atomic_end" -> return (Just edge,act,real0)
   -- Ignore llvm annotations
   "llvm.lifetime.start" -> return (Just edge,act,real0)
   "llvm.lifetime.end" -> return (Just edge,act,real0)
   _ -> do
     (val,nreal) <- realizeDefInstruction thread i edge real0
     return (Just edge { edgeValues = Map.insert (thread,i) (AlwaysDefined act) (edgeValues edge) },
             act,
             nreal { instructions = Map.insert (thread,i) val (instructions nreal) })
realizeInstruction thread blk sblk act (castDown -> Just store) edge real0 = do
  ptr <- storeInstGetPointerOperand store
  val <- storeInstGetValueOperand store
  (ptr',real1) <- realizeValue thread ptr edge real0
  (val',real2) <- realizeValue thread val edge real1
  let (nedge,real3) = memoryWrite (castUp store) act ptr' val' edge real2
  return (Just nedge,act,real3)
realizeInstruction thread blk sblk act (castDown -> Just br) edge real0 = do
  srcBlk <- instructionGetParent br
  isCond <- branchInstIsConditional br
  if isCond
    then do
    cond <- branchInstGetCondition br
    (cond',real1) <- realizeValue thread cond edge real0
    let cond'' = valBool . symbolicValue cond'
        condT inp = (act inp) .&&. (cond'' inp)
        condF inp = (act inp) .&&. (not' $ cond'' inp)
    ifT <- terminatorInstGetSuccessor br 0
    ifF <- terminatorInstGetSuccessor br 1
    (phisT,real2) <- realizePhis thread srcBlk ifT edge real1
    (phisF,real3) <- realizePhis thread srcBlk ifF edge real2
    return (Nothing,
            act,
            real3 { edges = Map.insertWith mappend (thread,ifT,0)
                            (edge { edgeConditions = [EdgeCondition { edgeActivation = condT
                                                                    , edgePhis = phisT }]
                                  }) $
                            Map.insertWith mappend (thread,ifF,0)
                            (edge { edgeConditions = [EdgeCondition { edgeActivation = condF
                                                                    , edgePhis = phisF }]
                                  }) (edges real3) })
    else do
    nxt <- terminatorInstGetSuccessor br 0
    (phis,real1) <- realizePhis thread srcBlk nxt edge real0
    return (Nothing,
            act,
            real1 { edges = Map.insertWith mappend (thread,nxt,0)
                            (edge { edgeConditions = [EdgeCondition { edgeActivation = act
                                                                    , edgePhis = phis }]
                                  }) (edges real1) })
realizeInstruction thread blk sblk act (castDown -> Just sw) edge real0 = do
  srcBlk <- instructionGetParent sw
  cond <- switchInstGetCondition sw
  defBlk <- switchInstGetDefaultDest sw
  trgs <- switchInstGetCases sw
  (cond',real1) <- realizeValue thread cond edge real0
  mkSwitch (valInt . symbolicValue cond') trgs srcBlk defBlk [] real1
  where
    mkSwitch _ [] srcBlk defBlk conds real = do
      (phis,nreal) <- realizePhis thread srcBlk defBlk edge real
      return (Nothing,act,nreal { edges = Map.insertWith mappend (thread,defBlk,0)
                                          (edge { edgeConditions = [EdgeCondition { edgeActivation = \inp -> mkAnd [ not' (c inp)
                                                                                                                      | c <- conds ]
                                                                                  , edgePhis = phis }]
                                                }) (edges nreal) })
    mkSwitch cond ((cint,blk):trgs) srcBlk defBlk conds real = do
      APInt _ rval <- constantIntGetValue cint >>= peek
      (phis,real1) <- realizePhis thread srcBlk blk edge real
      let rcond inp = cond inp .==. constant rval
          real2 = real1 { edges = Map.insertWith mappend (thread,blk,0)
                                  (edge { edgeConditions = [EdgeCondition { edgeActivation = rcond
                                                                          , edgePhis = phis }]
                                        }) (edges real1) }
      mkSwitch cond trgs srcBlk defBlk (rcond:conds) real2
realizeInstruction thread blk sblk act (castDown -> Just (_::Ptr PHINode)) edge real
  = return (Just edge,act,real)
realizeInstruction thread blk sblk act (castDown -> Just (_::Ptr ReturnInst)) edge real
  = case thread of
     Nothing -> return (Nothing,act,real)
     Just th -> return (Nothing,act,
                        real { termEvents = Map.insertWith (++) th [act] (termEvents real) })
realizeInstruction thread blk sblk act instr@(castDown -> Just cmpxchg) edge real0 = do
  ptr <- atomicCmpXchgInstGetPointerOperand cmpxchg
  cmp <- atomicCmpXchgInstGetCompareOperand cmpxchg
  new <- atomicCmpXchgInstGetNewValOperand  cmpxchg
  (ptr',real1) <- realizeValue thread ptr edge real0
  (cmp',real2) <- realizeValue thread cmp edge real1
  (new',real3) <- realizeValue thread new edge real2
  let oldval = memoryRead instr ptr' edge real3
      (oldval',gates1) = addSymGate (gateMp real3) (symbolicType oldval)
                         (symbolicValue oldval) (Just "atomic-read")
      isEq inp = valEq (symbolicValue oldval inp) (symbolicValue cmp' inp)
      (isEq',gates2) = addGate gates1 (Gate { gateTransfer = isEq
                                            , gateAnnotation = ()
                                            , gateName = Just "atomic-cmp" })
      real4 = real3 { gateMp = gates2 }
      (nedge,real5) = memoryWrite instr act ptr'
                      (InstructionValue { symbolicType = symbolicType oldval
                                        , symbolicValue = \inp -> argITE (isEq inp)
                                                                  (symbolicValue new' inp)
                                                                  oldval'
                                        , alternative = Nothing }) edge real4
      res = InstructionValue { symbolicType = TpVector [symbolicType oldval
                                                       ,TpBool]
                             , symbolicValue = \inp -> ValVector
                                                       [symbolicValue oldval inp
                                                       ,ValBool isEq']
                             , alternative = Nothing }
  return (Just nedge { edgeValues = Map.insert (thread,instr)
                                    (AlwaysDefined act)
                                    (edgeValues nedge) },
          act,
          real5 { instructions = Map.insert (thread,instr) res (instructions real5) })
realizeInstruction thread blk sblk act instr@(castDown -> Just atomic) edge real0 = do
  name <- getNameString atomic
  op <- atomicRMWInstGetOperation atomic
  ptr <- atomicRMWInstGetPointerOperand atomic
  val <- atomicRMWInstGetValOperand atomic
  (ptr',real1) <- realizeValue thread ptr edge real0
  (val',real2) <- realizeValue thread val edge real1
  let oldval = memoryRead instr ptr' edge real2
      newval = case op of
        RMWXchg -> val'
        RMWAdd -> InstructionValue { symbolicType = TpInt
                                   , symbolicValue =
                                     \inp -> ValInt (valInt (symbolicValue oldval inp) +
                                                     valInt (symbolicValue val' inp))
                                   , alternative = Nothing }
        RMWSub -> InstructionValue { symbolicType = TpInt
                                   , symbolicValue =
                                     \inp -> ValInt (valInt (symbolicValue oldval inp) -
                                                     valInt (symbolicValue val' inp))
                                   , alternative = Nothing }
      (nedge,real3) = memoryWrite instr act ptr' newval edge real2
      (oldval',ngates) = addSymGate (gateMp real3) (symbolicType oldval)
                         (symbolicValue oldval) (Just name)
  return (Just nedge { edgeValues = Map.insert (thread,instr) (AlwaysDefined act) (edgeValues nedge) },
          act,
          real3 { instructions = Map.insert (thread,instr)
                                 (oldval { symbolicValue = const oldval' })
                                 (instructions real3)
                , gateMp = ngates })
realizeInstruction thread blk sblk act instr edge real = do
  name <- getNameString instr
  (val,nreal) <- realizeDefInstruction thread instr edge real
  let (val',ngates) = addSymGate (gateMp nreal) (symbolicType val)
                      (symbolicValue val) (Just name)
  return (Just edge { edgeValues = Map.insert (thread,instr) (AlwaysDefined act) (edgeValues edge) },
          act,
          nreal { instructions = Map.insert (thread,instr)
                                 (val { symbolicValue = const val' }) (instructions nreal)
                , gateMp = ngates })

realizePhis :: Maybe (Ptr CallInst)
            -> Ptr BasicBlock
            -> Ptr BasicBlock
            -> Edge (ProgramState,ProgramInput)
            -> Realization (ProgramState,ProgramInput)
            -> IO (Map (Maybe (Ptr CallInst),Ptr Instruction)
                   (InstructionValue (ProgramState,ProgramInput)),
                   Realization (ProgramState,ProgramInput))
realizePhis thread src trg edge real = do
  phis <- allPhis src trg
  foldlM (\(mp,creal) (val,phi) -> do
             (val',nreal) <- realizeValue thread val edge creal
             return (Map.insert (thread,castUp phi) val' mp,nreal)
         ) (Map.empty,real) phis

realizeDefInstruction :: Maybe (Ptr CallInst)
                      -> Ptr Instruction
                      -> Edge (ProgramState,ProgramInput)
                      -> Realization (ProgramState,ProgramInput)
                      -> IO (InstructionValue (ProgramState,ProgramInput),
                             Realization (ProgramState,ProgramInput))
realizeDefInstruction thread (castDown -> Just opInst) edge real0 = do
  lhs <- getOperand opInst 0
  rhs <- getOperand opInst 1
  op <- binOpGetOpCode opInst
  (valL,real1) <- realizeValue thread lhs edge real0
  (valR,real2) <- realizeValue thread rhs edge real1
  let (tp,res) = case op of
        Add -> (TpInt,\inp -> let ValInt v1 = symbolicValue valL inp
                                  ValInt v2 = symbolicValue valR inp
                              in ValInt (v1 + v2))
        Sub -> (TpInt,\inp -> let ValInt v1 = symbolicValue valL inp
                                  ValInt v2 = symbolicValue valR inp
                              in ValInt (v1 - v2))
        Mul -> (TpInt,\inp -> let ValInt v1 = symbolicValue valL inp
                                  ValInt v2 = symbolicValue valR inp
                              in ValInt (v1 * v2))
        And -> (TpBool,\inp -> let ValBool v1 = symbolicValue valL inp
                                   ValBool v2 = symbolicValue valR inp
                               in ValBool (v1 .&&. v2))
        Or -> (TpBool,\inp -> let ValBool v1 = symbolicValue valL inp
                                  ValBool v2 = symbolicValue valR inp
                              in ValBool (v1 .||. v2))
        Xor -> (TpBool,\inp -> let ValBool v1 = symbolicValue valL inp
                                   ValBool v2 = symbolicValue valR inp
                               in ValBool (app xor [v1,v2]))
        SRem -> (TpInt,\inp -> let ValInt v1 = symbolicValue valL inp
                                   ValInt v2 = symbolicValue valR inp
                               in ValInt (rem' v1 v2))
        _ -> error $ "Unknown operator: "++show op
  return (InstructionValue { symbolicType = tp
                           , symbolicValue = res
                           , alternative = Nothing
                           },real2)
realizeDefInstruction thread i@(castDown -> Just call) edge real0 = do
  fname <- getFunctionName call
  case fname of
   '_':'_':'n':'o':'n':'d':'e':'t':_ -> do
     Singleton tp <- getType i >>= translateType real0
     return (InstructionValue { symbolicType = tp
                              , symbolicValue = \(_,pi) -> case Map.lookup i (nondets $ getThreadInput thread pi) of
                                                             Just r -> r
                              , alternative = Nothing },
             real0 { inputAnnotation = updateThreadInputDesc thread
                                       (\ti -> ti { nondetTypes = Map.insert i tp
                                                                  (nondetTypes ti) })
                                       (inputAnnotation real0) })
   "malloc" -> case Map.lookup i (allocations $ programInfo real0) of
     Just info -> do
       tp <- translateType real0 (allocType info)
       return (InstructionValue { symbolicType = TpPtr (Map.singleton ptrLoc ()) tp
                                , symbolicValue = \_ -> ValPtr (Map.singleton ptrLoc (constant True,[])) tp
                                , alternative = Nothing
                                },real0)
   "calloc" -> case Map.lookup i (allocations $ programInfo real0) of
     Just info -> do
       tp <- translateType real0 (allocType info)
       return (InstructionValue { symbolicType = TpPtr (Map.singleton ptrLocDyn ()) tp
                                , symbolicValue = \_ -> ValPtr (Map.singleton ptrLocDyn (constant True,[constant 0])) tp
                                , alternative = Nothing
                                },real0)
   "__act" -> do
     acts <- parseActArgs call
     let res (st,_) = case [ act
                           | (fun,is) <- acts
                           , (thId,thread) <- (Nothing,mainThread (programInfo real0)):
                                              [ (Just thId,th)
                                              | (thId,th) <- Map.toList
                                                             (threads $ programInfo real0) ]
                           , threadFunction thread==fun
                           , i <- is
                           , act <- case Map.lookup i (threadSliceMapping thread) of
                              Just blk -> case Map.lookup blk (latchBlocks $
                                                               getThreadState thId st) of
                                           Just act' -> [act']
                                           Nothing -> []
                              Nothing -> []
                           ] of
                       [] -> constant True
                       xs -> mkOr xs
     return (InstructionValue { symbolicType = TpBool
                              , symbolicValue = ValBool . res
                              , alternative = Nothing
                              },real0)
   "pthread_mutex_locked" -> do
     ptr <- getOperand call 0
     (ptr',real1) <- realizeValue thread ptr edge real0
     let lock = memoryRead i ptr' edge real1
     return (lock,real1)
   _ -> error $ "Unknown function call: "++fname
  where
    ptrLoc = MemoryPtr { memoryLoc = Left i
                       , offsetPattern = [StaticAccess 0] }
    ptrLocDyn = MemoryPtr { memoryLoc = Left i
                          , offsetPattern = [DynamicAccess] }
    parseActArgs :: Ptr CallInst -> IO [(Ptr Function,[Integer])]
    parseActArgs call = do
      nargs <- callInstGetNumArgOperands call
      parseActArgsFun call 0 nargs
    parseActArgsFun :: Ptr CallInst -> Integer -> Integer -> IO [(Ptr Function,[Integer])]
    parseActArgsFun call n nargs
      | n==nargs = return []
      | otherwise = do
          fun <- callInstGetArgOperand call n >>= removeCasts
          case castDown fun of
           Just rfun -> do
             (nums,rest) <- parseActArgsNums call (n+1) nargs
             return $ (rfun,nums):rest
           Nothing -> do
             valStr <- valueToString fun
             error $ "Unknown argument to __act function: "++valStr++" (expecting function)"
    parseActArgsNums :: Ptr CallInst -> Integer -> Integer -> IO ([Integer],[(Ptr Function,[Integer])])
    parseActArgsNums call n nargs
      | n==nargs = return ([],[])
      | otherwise = do
          num <- callInstGetArgOperand call n >>= removeCasts
          case castDown num of
           Just cint -> do
             APInt _ rval <- constantIntGetValue cint >>= peek
             (nums,rest) <- parseActArgsNums call (n+1) nargs
             return (rval:nums,rest)
           Nothing -> do
             rest <- parseActArgsFun call n nargs
             return ([],rest)
    removeCasts (castDown -> Just cexpr) = do
      arg <- getOperand (cexpr::Ptr ConstantExpr) 0
      removeCasts arg
    removeCasts arg = return arg
realizeDefInstruction thread i@(castDown -> Just icmp) edge real0 = do
  op <- getICmpOp icmp
  lhs <- getOperand icmp 0
  rhs <- getOperand icmp 1
  (lhsV,real1) <- realizeValue thread lhs edge real0
  (rhsV,real2) <- realizeValue thread rhs edge real1
  return (InstructionValue { symbolicType = TpBool
                           , symbolicValue = \inp -> ValBool $ cmp op lhsV rhsV inp
                           , alternative = Nothing },real2)
  where
    cmp I_EQ (alternative -> Just (OrList xs)) (alternative -> Just (IntConst 0)) inp
      = mkAnd [ valInt (x inp) .==. 0 | x <- xs ]
    cmp I_EQ (alternative -> Just (IntConst 0)) (alternative -> Just (OrList xs)) inp
      = mkAnd [ valInt (x inp) .==. 0 | x <- xs ]
    cmp I_EQ x@(symbolicType -> TpBool) y@(symbolicType -> TpBool) inp
      = (valBool (symbolicValue x inp)) .==. (valBool (symbolicValue y inp))
    cmp I_EQ x@(symbolicType -> TpInt) y@(symbolicType -> TpInt) inp
      = (valInt (symbolicValue x inp)) .==. (valInt (symbolicValue y inp))
    cmp I_EQ x@(symbolicType -> TpPtr locx _) y@(symbolicType -> TpPtr locy _) inp
      = mkOr (Map.elems $ Map.intersectionWith
              (\(c1,i1) (c2,i2) -> case zip i1 i2 of
                 [] -> c1 .==. c2
                 xs -> mkAnd $ (c1.==.c2):[ (j1.==.j2) | (j1,j2) <- xs ]
              )
              (valPtr $ symbolicValue x inp)
              (valPtr $ symbolicValue y inp))
    cmp I_NE x y inp = not' $ cmp I_EQ x y inp
    cmp I_SGE x y inp = (valInt $ symbolicValue x inp) .>=.
                        (valInt $ symbolicValue y inp)
    cmp I_UGE x y inp = (valInt $ symbolicValue x inp) .>=.
                        (valInt $ symbolicValue y inp)
    cmp I_SGT x y inp = (valInt $ symbolicValue x inp) .>.
                        (valInt $ symbolicValue y inp)
    cmp I_UGT x y inp = (valInt $ symbolicValue x inp) .>.
                        (valInt $ symbolicValue y inp)
    cmp I_SLE x y inp = (valInt $ symbolicValue x inp) .<=.
                        (valInt $ symbolicValue y inp)
    cmp I_ULE x y inp = (valInt $ symbolicValue x inp) .<=.
                        (valInt $ symbolicValue y inp)
    cmp I_SLT x y inp = (valInt $ symbolicValue x inp) .<.
                        (valInt $ symbolicValue y inp)
    cmp I_ULT x y inp = (valInt $ symbolicValue x inp) .<.
                        (valInt $ symbolicValue y inp)
realizeDefInstruction thread i@(castDown -> Just (zext::Ptr ZExtInst)) edge real0 = do
  op <- getOperand zext 0
  tp <- valueGetType op >>= translateType real0
  (fop,real1) <- realizeValue thread op edge real0
  return (if tp==Singleton TpBool
          then InstructionValue { symbolicType = TpInt
                                , symbolicValue = \inp -> ValInt $ ite
                                                          (valBool $ symbolicValue fop inp)
                                                          (constant 1)
                                                          (constant 0)
                                , alternative = Just $ ExtBool (valBool . symbolicValue fop)
                                }
          else fop,real1)
realizeDefInstruction thread i@(castDown -> Just select) edge real0 = do
  cond <- selectInstGetCondition select
  (cond',real1) <- realizeValue thread cond edge real0
  tVal <- selectInstGetTrueValue select
  (tVal',real2) <- realizeValue thread tVal edge real1
  fVal <- selectInstGetFalseValue select
  (fVal',real3) <- realizeValue thread fVal edge real2
  return (InstructionValue { symbolicType = symbolicType tVal'
                           , symbolicValue = \inp -> symITE (valBool $ symbolicValue cond' inp)
                                                     (symbolicValue tVal' inp)
                                                     (symbolicValue fVal' inp)
                           , alternative = Nothing },real3)
realizeDefInstruction thread i@(castDown -> Just (phi::Ptr PHINode)) edge real0
  = getInstructionValue thread i edge real0
realizeDefInstruction thread i@(castDown -> Just alloc) edge real0 = do
  tp <- getType (alloc :: Ptr AllocaInst) >>= sequentialTypeGetElementType >>= translateType real0
  return (InstructionValue { symbolicType = TpPtr (Map.singleton ptrLoc ()) tp
                           , symbolicValue = \_ -> ValPtr (Map.singleton ptrLoc
                                                           (constant True,[])) tp
                           , alternative = Nothing },real0)
  where
    ptrLoc = MemoryPtr { memoryLoc = Left i
                       , offsetPattern = [StaticAccess 0] }
realizeDefInstruction thread i@(castDown -> Just (trunc::Ptr TruncInst)) edge real0 = do
  val <- getOperand trunc 0
  (rval,real1) <- realizeValue thread val edge real0
  tp <- getType trunc
  let tp' = case castDown tp of
        Just t -> t
  bw <- getBitWidth tp'
  if bw==1
    then case alternative rval of
          Just (ExtBool c) -> return (InstructionValue { symbolicType = TpBool
                                                       , symbolicValue = \inp -> ValBool (c inp)
                                                       , alternative = Nothing
                                                       },real1)
          _ -> return (InstructionValue { symbolicType = TpBool
                                        , symbolicValue = \inp -> ValBool ((valInt $ symbolicValue rval inp).==.1)
                                        , alternative = Nothing },real1)
    else return (rval,real1)
realizeDefInstruction thread (castDown -> Just gep) edge real = do
  ptr <- getElementPtrInstGetPointerOperand gep
  (ptr',real1) <- realizeValue thread ptr edge real
  num <- getNumOperands gep
  args <- mapM (getOperand gep) [1..num-1]
  (args',real2) <- realizeValues thread args edge real1
  let rpat = fmap (\val -> case alternative val of
                    Just (IntConst n) -> Just n
                    _ -> Nothing
                  ) args'
      ridx inp = fmap (\val -> case alternative val of
                        Just (IntConst n) -> Left n
                        Nothing -> case symbolicValue val inp of
                          ValInt i -> Right i
                      ) args'
      (trgs,tp) = case symbolicType ptr' of
        TpPtr trgs tp -> (trgs,tp)
      ntp = offsetStruct (tail $ derefPattern rpat []) tp
      res_tp = TpPtr (Map.fromList
                      [ (trg { offsetPattern = derefPattern rpat
                                               (offsetPattern trg)
                             },())
                      | trg <- Map.keys trgs ])
               ntp
  name <- getNameString gep
  --putStrLn $ "GEP@"++name++": "++show (symbolicType ptr')++" ~> "++show res_tp
  return (InstructionValue { symbolicType = res_tp
                           , symbolicValue = \inp -> case symbolicValue ptr' inp of
                              ValPtr trgs _ -> ValPtr (derefPointer (ridx inp) trgs) ntp
                           , alternative = Nothing },real2)
realizeDefInstruction thread instr@(castDown -> Just load) edge real0 = do
  name <- getNameString load
  ptr <- loadInstGetPointerOperand load
  (ptr',real1) <- realizeValue thread ptr edge real0
  return (memoryRead instr ptr' edge real1,real1)
realizeDefInstruction thread (castDown -> Just bitcast) edge real = do
  -- Ignore bitcasts for now, just assume that everything will work out
  arg <- getOperand (bitcast :: Ptr BitCastInst) 0
  realizeValue thread arg edge real
realizeDefInstruction thread (castDown -> Just sext) edge real = do
  -- Again, ignore sign extensions
  arg <- getOperand (sext :: Ptr SExtInst) 0
  realizeValue thread arg edge real
realizeDefInstruction thread (castDown -> Just extr) edge real = do
  begin <- extractValueInstIdxBegin extr
  len <- extractValueInstGetNumIndices extr
  idx <- peekArray (fromIntegral len) begin
  arg <- getOperand extr 0
  (arg',real1) <- realizeValue thread arg edge real
  return (InstructionValue { symbolicType = indexType (symbolicType arg') idx
                           , symbolicValue = \inp -> indexValue (symbolicValue arg' inp) idx
                           , alternative = Nothing },real1)
  where
    indexType :: Integral a => SymType -> [a] -> SymType
    indexType tp [] = tp
    indexType (TpVector tps) (i:is) = indexType (tps `genericIndex` i) is

    indexValue :: Integral a => SymVal -> [a] -> SymVal
    indexValue val [] = val
    indexValue (ValVector vals) (i:is) = indexValue (vals `genericIndex` i) is
realizeDefInstruction _ i _ _ = do
  str <- valueToString i
  error $ "Unknown instruction: "++str
     
memoryRead :: Ptr Instruction
           -> InstructionValue (ProgramState,ProgramInput)
           -> Edge (ProgramState,ProgramInput)
           -> Realization (ProgramState,ProgramInput)
           -> InstructionValue (ProgramState,ProgramInput)
memoryRead origin (InstructionValue { symbolicType = TpPtr locs (Singleton tp)
                                    , symbolicValue = f
                                    }) edge real
  = InstructionValue { symbolicType = tp
                     , symbolicValue = val
                     , alternative = Nothing
                     }
  where
    allEvents = Map.intersection (events real) (observedEvents edge)
    startVal inp@(ps,_)
      = let ValPtr trgs _ = f inp
            condMp = Map.mapWithKey (\trg (cond,dyn)
                                     -> let idx = idxList (offsetPattern trg) dyn
                                            (res,_,_) = accessAllocTyped tp symITEs
                                                        (\val _ -> (val,val,()))
                                                        idx
                                                        (case Map.lookup (memoryLoc trg) (memory ps) of
                                                          Just r -> r
                                                          Nothing -> error $ "Memory location "++show (memoryLoc trg)++" not defined.") ()
                                        in (res,cond)
                                    ) trgs
        in case Map.elems condMp of
            [] -> error $ "Pointer has zero targets."
            xs -> symITEs xs
    val inp = let ValPtr trgs _ = f inp
              in foldl (\cval ev -> case ev of
                         WriteEvent trg cont writeOrigin
                           -> case [ mkAnd (cond1:cond2:match)
                                   | (ptr1,(cond1,idx1)) <- Map.toList trgs
                                   , (ptr2,info2) <- Map.toList trg
                                   , memoryLoc ptr1 == memoryLoc ptr2
                                   , let (cond2,idx2) = info2 inp
                                   , match <- case patternMatch
                                                   (offsetPattern ptr1)
                                                   (offsetPattern ptr2)
                                                   idx1 idx2 of
                                               Nothing -> []
                                               Just conds -> [conds] ] of
                              [] -> cval
                              [cond] -> mkVal cond
                              conds -> mkVal (mkOr conds)
                           where
                                  mkVal c = if symbolicType cont==tp
                                            then symITE c (symbolicValue cont inp) cval
                                            else cval {-error $ "While realizing read to "++
                                                 (unsafePerformIO $ getNameString origin)++
                                                 " from "++show trgs++
                                                 ": Write at "++
                                                 (unsafePerformIO $ valueToString writeOrigin)++
                                                 " to "++show (fmap (\x -> x inp) trg)++
                                                 " has wrong type "++
                                                 (show $ (symbolicType cont))++
                                                 " (Expected: "++show tp++")."-}
                         _ -> cval
                       ) (startVal inp) (fmap snd $ Map.toAscList allEvents)
    {-tp = case Map.keys locs of
      l:_ -> case Map.lookup (memoryLoc l) (memoryDesc $ stateAnnotation real) of
        Just t -> trace ("offsetAlloc "++show (offsetPattern l)++" "++show t) $
                  firstType $ offsetAlloc (offsetPattern l) t-}

memoryWrite :: Ptr Instruction
            -> (inp -> SMTExpr Bool)
            -> InstructionValue inp
            -> InstructionValue inp
            -> Edge inp
            -> Realization inp
            -> (Edge inp,Realization inp)
memoryWrite origin act ptr val edge real
  = (edge { observedEvents = Map.insert (Map.size (events real)) ()
                             (observedEvents edge) },
     real { events = Map.insert (Map.size (events real))
                     (WriteEvent { target = Map.mapWithKey
                                            (\loc _ inp
                                             -> let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr inp) of
                                                                   Just r -> r
                                                in ((act inp) .&&. cond,idx)
                                            ) (tpPtr $ symbolicType ptr)
                                 , writeContent = val
                                 , eventOrigin = origin })
                     (events real) })

getInstructionValue :: Maybe (Ptr CallInst) -> Ptr Instruction
                    -> Edge (ProgramState,ProgramInput)
                    -> Realization (ProgramState,ProgramInput)
                    -> IO (InstructionValue (ProgramState,ProgramInput),
                           Realization (ProgramState,ProgramInput))
getInstructionValue thread instr edge real
  = case Map.lookup (thread,instr) (edgeValues edge) of
  Just (AlwaysDefined _) -> case Map.lookup (thread,instr) (instructions real) of
    Just val -> return (val,real)
  Just (SometimesDefined act) -> case Map.lookup (thread,instr) (instructions real) of
    Just val -> return (InstructionValue { symbolicType = symbolicType val
                                         , symbolicValue = \inp -> symITE (act inp)
                                                                   (symbolicValue val inp)
                                                                   (case Map.lookup instr
                                                                         (latchValues $ getThreadState thread $ fst inp) of
                                                                     Just r -> r
                                                                     Nothing -> error $ "getInstructionValue: Cannot get latch value of "++showValue instr "")
                                         , alternative = Nothing
                                         },
                        real { stateAnnotation = updateThreadStateDesc thread
                                                 (\ts -> ts { latchValueDesc = Map.insert instr
                                                                               (symbolicType val)
                                                                               (latchValueDesc ts)
                                                            }) (stateAnnotation real) })
  _ -> do
    Singleton tp <- getType instr >>= translateType real
    return (InstructionValue { symbolicType = tp
                             , symbolicValue = \(st,_) -> case Map.lookup instr
                                                               (latchValues $ getThreadState thread st) of
                                                           Just r -> r
                                                           Nothing -> error $ "getInstructionValue: Cannot get latch value of "++showValue instr ""
                             , alternative = Nothing
                             },
            real { stateAnnotation = updateThreadStateDesc thread
                                     (\ts -> ts { latchValueDesc = Map.insert instr tp
                                                                   (latchValueDesc ts) })
                                     (stateAnnotation real) })

realizeValues :: Maybe (Ptr CallInst) -> [Ptr Value]
              -> Edge (ProgramState,ProgramInput)
              -> Realization (ProgramState,ProgramInput)
              -> IO ([InstructionValue (ProgramState,ProgramInput)],
                     Realization (ProgramState,ProgramInput))
realizeValues _ [] _ real = return ([],real)
realizeValues thread (val:vals) edge real = do
  (x,real1) <- realizeValue thread val edge real
  (xs,real2) <- realizeValues thread vals edge real1
  return (x:xs,real2)

realizeValue :: Maybe (Ptr CallInst) -> Ptr Value
             -> Edge (ProgramState,ProgramInput)
             -> Realization (ProgramState,ProgramInput)
             -> IO (InstructionValue (ProgramState,ProgramInput),
                    Realization (ProgramState,ProgramInput))
realizeValue thread (castDown -> Just instr) edge real
  = getInstructionValue thread instr edge real
realizeValue thread (castDown -> Just i) edge real = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return (InstructionValue { symbolicType = TpBool
                                  , symbolicValue = const $ ValBool $ constant $ rv/=0
                                  , alternative = Just (IntConst $ fromIntegral rv) },real)
    else return (InstructionValue { symbolicType = TpInt
                                  , symbolicValue = const $ ValInt $ constant $ fromIntegral rv
                                  , alternative = Just (IntConst $ fromIntegral rv)
                                  },real)
realizeValue thread (castDown -> Just undef) edge real = do
  tp <- getType (undef::Ptr UndefValue)
  res <- defaultValue tp
  return (res,real)
  where
    defaultValue :: Ptr Type -> IO (InstructionValue (ProgramState,ProgramInput))
    defaultValue (castDown -> Just itp) = do
      bw <- getBitWidth itp
      return InstructionValue { symbolicType = if bw==1 then TpBool else TpInt
                              , symbolicValue = if bw==1
                                                then const $ ValBool $ constant False
                                                else const $ ValInt $ constant 0
                              , alternative = Just (IntConst 0) }
realizeValue thread (castDown -> Just glob) edge real
  = return (InstructionValue { symbolicType = TpPtr (Map.singleton ptr ()) tp
                             , symbolicValue = \_ -> ValPtr (Map.singleton ptr (constant True,[])) tp
                             , alternative = Nothing
                             },real)
  where
    ptr = MemoryPtr { memoryLoc = Right glob
                    , offsetPattern = [] }
    tp = case Map.lookup (Right glob) (memoryDesc $ stateAnnotation real) of
      Just (TpStatic _ t) -> t
      Just (TpDynamic t) -> t
realizeValue thread (castDown -> Just cexpr) edge real = do
  instr <- constantExprAsInstruction (cexpr::Ptr ConstantExpr)
  realizeDefInstruction thread instr edge real
realizeValue thread (castDown -> Just arg) edge real = do
  let thSt = getThreadStateDesc thread (stateAnnotation real)
  case threadArgumentDesc thSt of
   Just (arg',tp)
     -> if arg==arg'
        then return (InstructionValue { symbolicType = tp
                                      , symbolicValue = \(ps,_) -> case threadArgument (getThreadState thread ps) of
                                                                    Just (_,val) -> val
                                      , alternative = Nothing },real)
        else error $ "Function arguments (other than thread arguments) not supported."
   Nothing -> do
     name <- getNameString arg
     error $ "Function arguments (other than thread arguments) not supported: "++name
realizeValue thread val edge real = do
  str <- valueToString val
  error $ "Cannot realize value: "++str

translateType :: Realization inp -> Ptr Type -> IO (Struct SymType)
translateType _ (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return $ Singleton TpBool
    _ -> return $ Singleton TpInt
translateType real (castDown -> Just ptp) = do
  subType <- sequentialTypeGetElementType (ptp::Ptr PointerType) >>= translateType real
  return $ Singleton $ TpPtr (allPtrsOfType subType (memoryDesc $ stateAnnotation real)) subType
translateType real (castDown -> Just struct) = do
  name <- structTypeGetName struct >>= stringRefData
  case name of
   "struct.pthread_t" -> return $ Singleton $ TpThreadId (fmap (const ())
                                                          (threadStateDesc $ stateAnnotation real))
   "struct.pthread_mutex_t" -> return $ Singleton TpBool
   "struct.pthread_rwlock_t" -> return $ Singleton $ TpVector [TpBool,TpInt]
   _ -> do
     num <- structTypeGetNumElements struct
     tps <- mapM (\i -> structTypeGetElementType struct i >>= translateType real) [0..num-1]
     return $ Struct tps
translateType real (castDown -> Just arr) = do
  subt <- sequentialTypeGetElementType arr >>= translateType real
  num <- arrayTypeGetNumElements arr
  return $ Struct $ genericReplicate num subt
translateType _ tp = do
  typeDump tp
  error "Can't translate type"

translateType0 :: Ptr Type -> IO (Struct SymType)
translateType0 (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return $ Singleton TpBool
    _ -> return $ Singleton TpInt
translateType0 (castDown -> Just ptr) = do
  subType <- sequentialTypeGetElementType (ptr::Ptr PointerType) >>= translateType0
  return $ Singleton $ TpPtr Map.empty subType
translateType0 (castDown -> Just struct) = do
  name <- structTypeGetName struct >>= stringRefData
  case name of
   "struct.pthread_t" -> return $ Singleton $ TpThreadId Map.empty
   "struct.pthread_mutex_t" -> return $ Singleton TpBool
   "struct.pthread_rwlock_t" -> return $ Singleton $
                                TpVector [TpBool,TpInt]
   _ -> do
     num <- structTypeGetNumElements struct
     tps <- mapM (\i -> structTypeGetElementType struct i >>= translateType0) [0..num-1]
     return $ Struct tps
translateType0 (castDown -> Just arr) = do
  subt <- sequentialTypeGetElementType arr >>= translateType0
  num <- arrayTypeGetNumElements arr
  return $ Struct $ genericReplicate num subt
translateType0 tp = do
  typeDump tp
  error "Cannot translate type"

typeBasedReachability :: Map MemoryLoc AllocType -> Map MemoryLoc AllocType
typeBasedReachability mem
  = Map.mapWithKey
    (\loc tp -> mapTypes (mapPointer (\stp _ -> allPtrsOfType stp mem)) tp
    ) mem  

typeBasedArgumentReachability :: Map MemoryLoc AllocType
                              -> Map (Ptr CallInst) ThreadStateDesc
                              -> Map (Ptr CallInst) ThreadStateDesc
typeBasedArgumentReachability mem
  = fmap (\ts -> case threadArgumentDesc ts of
           Just (arg,tp)
             -> ts { threadArgumentDesc = Just (arg,mapPointer (\stp _ -> allPtrsOfType stp mem) tp) }
           _ -> ts)

threadBasedReachability :: Map (Ptr CallInst) ()
                        -> Map MemoryLoc AllocType
                        -> Map MemoryLoc AllocType
threadBasedReachability threads
  = fmap (mapTypes (\tp -> case tp of
                     TpThreadId _ -> TpThreadId threads
                     _ -> tp))

instance Monoid (Edge inp) where
  mempty = Edge { edgeValues = Map.empty
                , edgeConditions = []
                , observedEvents = Map.empty
                }
  mappend e1 e2 = Edge { edgeValues = Map.mergeWithKey combine only only
                                      (edgeValues e1) (edgeValues e2)
                       , edgeConditions = (edgeConditions e1)++
                                          (edgeConditions e2)
                       , observedEvents = Map.union (observedEvents e1) (observedEvents e2)
                       }
    where
      combine _ NeverDefined NeverDefined = Just NeverDefined
      combine _ (SometimesDefined act) _ = Just (SometimesDefined act)
      combine _ _ (SometimesDefined act) = Just (SometimesDefined act)
      combine _ (AlwaysDefined act) (AlwaysDefined _) = Just (AlwaysDefined act)
      only = fmap (\ev -> case ev of
                    AlwaysDefined act -> SometimesDefined act
                    _ -> ev)

realizeBlock :: Maybe (Ptr CallInst) -> Ptr BasicBlock -> Int
             -> ProgramInfo
             -> Realization (ProgramState,ProgramInput)
             -> IO (Realization (ProgramState,ProgramInput))
realizeBlock thread blk sblk info real = do
  name <- subBlockName blk sblk
  instrs <- getSubBlockInstructions blk sblk
  let dontStep = Map.null $ threadStateDesc $ stateAnnotation real
      latchCond = \(st,inp)
                  -> let blkAct = case Map.lookup (blk,sblk)
                                       (latchBlocks $ getThreadState thread st) of
                                   Just act -> act
                                   Nothing -> error $ "realizeBlock: Cannot get activation variable for "++show (blk,sblk)
                         stepAct = step $ getThreadInput thread inp
                         runAct = case thread of
                           Nothing -> []
                           Just th -> case Map.lookup th (threadState st) of
                                       Just (act,_) -> [act]
                                       Nothing -> error $ "realizeBlock: Cannot find run variable for thread "++show th
                     in mkAnd $ runAct++(if dontStep
                                         then []
                                         else [stepAct])++[blkAct]
      allConds = (if isEntryBlock
                  then [latchCond]
                  else [])++
                 [ edgeActivation cond | cond <- edgeConditions edge ]
      (act,gates1) = addGate (gateMp real)
                     (Gate { gateTransfer = case allConds of
                              [] -> \_ -> constant False
                              [f] -> f
                              _ -> \st -> mkOr [ f st | f <- allConds ]
                           , gateAnnotation = ()
                           , gateName = Just name })
      edgePhi = foldl (\cmp cond
                       -> Map.unionWith
                          (\v1 v2
                           -> InstructionValue { symbolicType = symbolicType v1
                                               , symbolicValue = \inp -> symITE (edgeActivation cond inp)
                                                                         (symbolicValue v1 inp)
                                                                         (symbolicValue v2 inp)
                                               , alternative = Nothing }
                          ) (edgePhis cond) cmp
                      ) Map.empty (edgeConditions edge)
  (edgePhiGates,gates2) <- runStateT (Map.traverseWithKey
                                      (\(_,i) val -> do
                                          name <- lift $ getNameString i
                                          gates <- get
                                          let (nval,ngates) = addSymGate gates (symbolicType val)
                                                              (symbolicValue val)
                                                              (Just name)
                                          put ngates
                                          return val { symbolicValue = const nval }
                                      ) edgePhi
                                     ) gates1
  let instrs1 = Map.union (instructions real) edgePhiGates
      edge1 = edge { edgeValues = Map.union (fmap (\_ -> if isEntryBlock
                                                         then SometimesDefined (\inp -> mkOr
                                                                                        [ edgeActivation cond inp
                                                                                        | cond <- edgeConditions edge ]
                                                                               )
                                                         else AlwaysDefined (const act)
                                                  ) edgePhiGates)
                                  (if isEntryBlock
                                   then fmap (\def -> case def of
                                               AlwaysDefined act -> SometimesDefined act
                                               _ -> def) (edgeValues edge)
                                   else edgeValues edge)
                   }
      real1 = real { gateMp = gates2
                   , instructions = instrs1
                   , edges = Map.delete (thread,blk,sblk) (edges real) }
  realizeInstructions thread blk sblk (const act) instrs edge1 real1
  where
    edge = case Map.lookup (thread,blk,sblk) (edges real) of
      Nothing -> mempty
      Just e -> e
    threadInfo = case thread of
      Nothing -> mainThread info
      Just t -> case Map.lookup t (threads info) of
        Just i -> i
    isEntryBlock = Map.member (blk,sblk) (entryPoints threadInfo)

getSubBlockInstructions :: Ptr BasicBlock -> Int -> IO [Ptr Instruction]
getSubBlockInstructions blk sub = do
  instrs <- getInstList blk >>= ipListToList
  dropInstrs sub instrs
  where
    dropInstrs :: Int -> [Ptr Instruction] -> IO [Ptr Instruction]
    dropInstrs 0 is = return is
    dropInstrs n (i:is) = case castDown i of
      Just call -> do
        cv <- callInstGetCalledValue call
        case castDown cv of
         Just (fun::Ptr Function) -> do
           name <- getNameString fun
           case name of
            "pthread_yield" -> dropInstrs (n-1) is
            "__yield" -> dropInstrs (n-1) is
            "__yield_local" -> dropInstrs (n-1) is
            _ -> dropInstrs n is
         Nothing -> dropInstrs n is
      Nothing -> dropInstrs n is

subBlockName :: Ptr BasicBlock -> Int -> IO String
subBlockName blk sblk = do
  blkName <- getNameString blk
  if sblk==0
    then return blkName
    else return $ blkName++"."++show sblk

allPhis :: Ptr BasicBlock -> Ptr BasicBlock -> IO [(Ptr Value,Ptr PHINode)]
allPhis src trg = do
  instrs <- getInstList trg
  it <- ipListBegin instrs
  allPhis' it
  where
    allPhis' it = do
      instr <- iListIteratorDeref it
      case castDown instr of
       Nothing -> return []
       Just phi -> do
         x <- findPhi phi 0
         nxt_it <- iListIteratorNext it
         xs <- allPhis' nxt_it
         return ((x,phi):xs)
    findPhi phi n = do
      blk <- phiNodeGetIncomingBlock phi n
      if blk==src
        then phiNodeGetIncomingValue phi n
        else findPhi phi (n+1)

outputValues :: Realization (ProgramState,ProgramInput)
             -> Map (Maybe (Ptr CallInst),Ptr Instruction)
                ((ProgramState,ProgramInput) -> SymVal)
outputValues real = mp2
  where
    dontStep = Map.null (threadStateDesc $ stateAnnotation real)
    mp1 = Map.foldlWithKey (\mp instr _
                            -> Map.insert (Nothing,instr)
                               (getExpr Nothing instr) mp
                           ) Map.empty
          (latchValueDesc $ mainStateDesc $ stateAnnotation real)
    mp2 = Map.foldlWithKey
          (\mp th thSt
           -> Map.foldlWithKey
              (\mp instr _
                -> Map.insert (Just th,instr)
                   (getExpr (Just th) instr) mp
              ) mp (latchValueDesc thSt)
          ) mp1 (threadStateDesc $ stateAnnotation real)
    finEdge = foldl mappend (foldl mappend mempty (edges real)) (Map.union (yieldEdges real) (internalYieldEdges real))
    phis0 = foldl (\mp cond
                   -> Map.union mp
                      (Map.mapWithKey (\(th,instr) _ inp@(st,_)
                                       -> let ts = getThreadState th st
                                              old = case Map.lookup instr (latchValues ts) of
                                                Just r -> r
                                                Nothing -> error $ "outputValues: Cannot get latch value of "++show instr
                                              def = symbolicValue (case Map.lookup (th,instr) (instructions real) of
                                                                    Just r -> r
                                                                    Nothing -> error $ "outputValues: Cannot get instruction value of "++show (th,instr)
                                                                  ) inp
                                          in case Map.lookup (th,instr) (edgeValues finEdge) of
                                              Just (AlwaysDefined _) -> def
                                              Just (SometimesDefined act)
                                                -> symITE (act inp) def old
                                              Just NeverDefined -> old
                                              Nothing -> error $ "outputValues: Cannot find edge value of "++show (th,instr)
                                      ) (edgePhis cond))
                  ) Map.empty (edgeConditions finEdge)
    phis = foldl (\mp cond
                  -> Map.unionWith
                     (\v1 v2 inp -> symITE (edgeActivation cond inp)
                                    (v1 inp) (v2 inp))
                     (fmap symbolicValue (edgePhis cond)) mp
                 ) phis0 (edgeConditions finEdge)
    getExpr thread instr inp = if dontStep
                               then body
                               else symITE stepCond body old
      where
        stepCond = step $ getThreadInput thread (snd inp)
        body = case Map.lookup (thread,instr) phis of
          Just sym -> sym inp
          Nothing -> case Map.lookup (thread,instr) (edgeValues finEdge) of
            Just (AlwaysDefined _) -> case Map.lookup (thread,instr) (instructions real) of
              Just val -> symbolicValue val inp
            Just (SometimesDefined act) -> case Map.lookup (thread,instr) (instructions real) of
              Just val -> symITE (act inp) (symbolicValue val inp) old
            _ -> old
        old = case Map.lookup instr (latchValues $ getThreadState thread $ fst inp) of
          Just r -> r
          Nothing -> error $ "outputValues: Cannot find old value of "++show instr

outputMem :: Realization (ProgramState,ProgramInput) -> (ProgramState,ProgramInput)
          -> (Map MemoryLoc AllocVal,Realization (ProgramState,ProgramInput))
outputMem real inp
  = Map.foldlWithKey
    (\(mem,real) n ev -> case ev of
      WriteEvent trgs cont _
        -> Map.foldlWithKey
           (\(mem,real) trg cond
            -> let (cond',dyn) = cond inp
                   idx = idxList (offsetPattern trg) dyn
                   val = case Map.lookup (memoryLoc trg) mem of
                          Just v -> v
                   (_,nval,ngates) = accessAllocTyped (symbolicType cont) (const ())
                                     (\old gates -> let (new,ngates) = addSymGate gates
                                                                       (symbolicType cont)
                                                                       (\inp -> symITE cond'
                                                                                (symbolicValue cont inp)
                                                                                old)
                                                                       (Just $ "write"++show n)
                                                    in ((),new,ngates)
                                     ) idx val (gateMp real)
               in (Map.insert (memoryLoc trg) nval mem,
                   real { gateMp = ngates })
           ) (mem,real) trgs
    ) (memory (fst inp),real) (events real)

{-outputMem :: Realization (ProgramState,ProgramInput) -> (ProgramState,ProgramInput) -> Map MemoryLoc AllocVal
outputMem real inp
  = foldl (\mem ev -> case ev of
            WriteEvent trgs cont _
              -> Map.foldlWithKey
                 (\mem trg cond
                  -> let (cond',dyn) = cond inp
                         idx = idxList (offsetPattern trg) dyn
                     in Map.adjust
                        (\val -> snd $ accessAllocTyped (symbolicType cont) (const ())
                                 (\old -> ((),symITE cond' (symbolicValue cont inp) old))
                                 idx val)
                        (memoryLoc trg) mem
                 ) mem trgs
          ) mem0 (events real)
  where
    mem0 = memory (fst inp)-}

getConstant :: Ptr Constant -> IO (Struct SymVal)
getConstant (castDown -> Just cint) = do
  tp <- getType cint
  bw <- getBitWidth tp
  v <- constantIntGetValue cint
  rv <- apIntGetSExtValue v
  if bw==1
    then return $ Singleton $ ValBool $ constant $ rv/=0
    else return $ Singleton $ ValInt $ constant $ fromIntegral rv
getConstant (castDown -> Just czero) = do
  tp <- getType (czero::Ptr ConstantAggregateZero)
  zeroInit tp
  where
     zeroInit (castDown -> Just itp) = do
       bw <- getBitWidth itp
       if bw==1
         then return $ Singleton $ ValBool $ constant False
         else return $ Singleton $ ValInt $ constant 0
     zeroInit (castDown -> Just struct) = do
       specialInit <- do
         hasName <- structTypeHasName struct
         if hasName
           then do
           name <- structTypeGetName struct >>= stringRefData
           case name of
            "struct.pthread_mutex_t" -> return $ Just $ Singleton $
                                        ValBool $ constant False
            "struct.pthread_rwlock_t" -> return $ Just $ Singleton $
                                         ValVector [ValBool $ constant False
                                                   ,ValInt $ constant 0]
            _ -> return Nothing
           else return Nothing
       case specialInit of
        Just init -> return init
        Nothing -> do
          num <- structTypeGetNumElements struct
          subs <- mapM (\i -> do
                           stp <- structTypeGetElementType struct i
                           zeroInit stp
                       ) [0..num-1]
          return (Struct subs)
     zeroInit (castDown -> Just arrTp) = do
       stp <- sequentialTypeGetElementType arrTp
       num <- arrayTypeGetNumElements arrTp
       zeroEl <- zeroInit stp
       return (Struct $ genericReplicate num zeroEl)

getConstant (castDown -> Just cstruct) = do
  tp <- getType (cstruct::Ptr ConstantStruct)
  num <- structTypeGetNumElements tp
  vals <- mapM (\i -> constantGetAggregateElement cstruct i >>= getConstant
               ) [0..num-1]
  return $ Struct vals
{-getConstant (castDown -> Just cstruct) = do
  tp <- getType (cstruct::Ptr ConstantStruct)
  name <- structTypeGetName tp >>= stringRefData
  case name of
   "struct.pthread_mutex_t" -> return $ ValBool (constant False)-}
getConstant c = do
  str <- valueToString c
  error $ "getConstant: "++str

allPtrsOfType :: Struct SymType -> Map MemoryLoc AllocType -> Map MemoryPtr ()
allPtrsOfType tp mem
  = Map.fromList [ (MemoryPtr loc idx,())
                 | (loc,tp') <- Map.toList mem
                 , idx <- allAllocPtrs tp' ]
  where
    allAllocPtrs (TpStatic n tp')
      = [ StaticAccess i:idx
        | idx <- allStructPtrs tp'
        , i <- [0..n-1] ]
    allAllocPtrs (TpDynamic tp')
      = [ DynamicAccess:idx
        | idx <- allStructPtrs tp' ]
    allStructPtrs tp' = if sameStructType tp tp'
                        then [[]]
                        else (case tp' of
                               Struct tps -> [ StaticAccess n:idx
                                             | (n,tp') <- zip [0..] tps
                                             , idx <- allStructPtrs tp' ]
                               _ -> [])

      
