{-# LANGUAGE ViewPatterns,ScopedTypeVariables,TypeFamilies,DeriveDataTypeable,
             PackageImports #-}
module Realization.Threaded where

import Realization.Threaded.ProgramInfo (ProgramInfo(..),ThreadInfo(..),
                                         AllocInfo(..),
                                         getProgramInfo)
import Realization.Threaded.ThreadFinder as TF (Quantity(..),AllocKind(..))
import Realization.Threaded.Value
import Realization.Threaded.State
import Realization.Threaded.Options
import Realization.Common (getFunctionName)
import Args

import Language.SMTLib2 hiding (define,constant)
import Language.SMTLib2.Internals.Expression (Expression)
import qualified Language.SMTLib2.Internals.Expression as E
import Language.SMTLib2.Internals.Interface as I
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type

import LLVM.FFI hiding (GetType,getType,And)
import qualified LLVM.FFI as LLVM
import Foreign.Ptr (Ptr)
import Foreign.Storable (peek)
import Foreign.Marshal.Array (peekArray)
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Reader
import Data.Foldable
import Data.List (genericReplicate,genericIndex)
import Prelude hiding (foldl,sequence,mapM,mapM_,concat)
import Control.Exception
import System.IO.Unsafe
import System.IO
import Data.GADT.Compare
import Data.GADT.Show
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.Maybe (catMaybes)
import Text.Show

import Debug.Trace

data RExpr inp st tp = RExpr (Expression E.NoVar E.NoVar E.NoFun E.NoCon E.NoField E.NoVar E.NoVar (RExpr inp st) tp)
                     | RInput (RevComp inp tp)
                     | RState (RevComp st tp)
                     | RRef (DefExpr tp)

data DefExpr tp = DefExpr Int (Repr tp)

data Definition inp st tp = Definition { defExpr :: RExpr inp st tp
                                       , defName :: String }

data DefinitionState = AlwaysDefined
                     | SometimesDefined
                     | NeverDefined

data AlternativeRepresentation inp st
  = IntConst Integer
  | OrList [SymVal (RExpr inp st)]
  | ExtBool (RExpr inp st BoolType)
  | NullPtr

data InstructionValue inp st
  = InstructionValue { symbolicType :: SymType
                     , symbolicValue :: SymVal (RExpr inp st)
                     , alternative :: Maybe (AlternativeRepresentation inp st)
                     }

data Edge inp st = Edge { edgeValues :: Map (Maybe (Ptr CallInst),Ptr Instruction)
                                        DefinitionState
                        , edgeConditions :: [EdgeCondition inp st]
                        , observedEvents :: Map Int ()
                        }

data EdgeCondition inp st = EdgeCondition { edgeActivation :: RExpr inp st BoolType
                                          , edgePhis :: Map (Maybe (Ptr CallInst),Ptr Instruction)
                                                        (InstructionValue inp st)
                                          }

data Event inp st = WriteEvent { target :: Map MemoryPtr (RExpr inp st BoolType,[RExpr inp st IntType])
                               , writeContent :: InstructionValue inp st
                               , eventThread :: Maybe (Ptr CallInst)
                               , eventOrigin :: Ptr Instruction -- For debugging
                               }

data RealizationState inp st
  = RealizationSt { inputAnnotation :: CompDescr inp
                  , stateAnnotation :: CompDescr st
                  , edges :: Map (Maybe (Ptr CallInst),Ptr BasicBlock,Int)
                             (Edge inp st)
                  , yieldEdges :: Map (Maybe (Ptr CallInst),Ptr BasicBlock,Int)
                                  (Edge inp st)
                  , internalYieldEdges :: Map (Maybe (Ptr CallInst),Ptr BasicBlock,Int)
                                          (Edge inp st)
                  , instructions :: Map (Maybe (Ptr CallInst),Ptr Instruction)
                                    (RExpr inp st BoolType,
                                     InstructionValue inp st)
                  , definitions :: DMap DefExpr (Definition inp st)
                  , names :: Map String Int
                  , events :: Map Int (Event inp st)
                  , spawnEvents :: Map (Ptr CallInst) [(Maybe (Ptr CallInst),
                                                        RExpr inp st BoolType,
                                                        Maybe (InstructionValue inp st))]
                  , termEvents :: Map (Ptr CallInst) [(RExpr inp st BoolType,
                                                       Maybe (InstructionValue inp st))]
                  , assertions :: [(Maybe (Ptr CallInst),RExpr inp st BoolType)]
                  , memoryInit :: Map (Ptr GlobalVariable) (AllocVal (RExpr inp st))
                  , mainBlock :: Ptr BasicBlock
                  , threadBlocks :: Map (Ptr CallInst) (Ptr BasicBlock)
                  , programInfo :: ProgramInfo
                  }

type Realization inp st r = ReaderT TranslationOptions (StateT (RealizationState inp st) IO) r

data RealizationException = RealizationException String SomeException deriving Typeable

type LLVMState = ProgramState (RExpr ProgramInput ProgramState)
type LLVMInput = ProgramInput (RExpr ProgramInput ProgramState)
type LLVMExpr tp = RExpr ProgramInput ProgramState tp
type LLVMRealization r = Realization ProgramInput ProgramState r
type LLVMVal = SymVal (RExpr ProgramInput ProgramState)

data LLVMTransRel = LLVMTransRel { llvmInputDesc :: ProgramInputDesc
                                 , llvmStateDesc :: ProgramStateDesc
                                 , llvmDefinitions :: DMap DefExpr (Definition ProgramInput ProgramState)
                                 , llvmNext :: ProgramState (RExpr ProgramInput ProgramState)
                                 , llvmInit :: ProgramState LLVMInit
                                 , llvmAssertions :: [LLVMExpr BoolType]
                                 , llvmInternalYields :: [(Maybe (Ptr CallInst),Ptr BasicBlock,Int)]}

data LLVMInit tp = NoInit (Repr tp)
                 | Init (RExpr ProgramInput ProgramState tp)

instance GetType LLVMInit where
  getType (NoInit tp) = tp
  getType (Init e) = getType e

instance (Composite inp,Composite st)
         => Embed (ReaderT TranslationOptions (StateT (RealizationState inp st) IO))
                  (RExpr inp st) where
  type EmVar (ReaderT TranslationOptions
              (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoVar
  type EmQVar (ReaderT TranslationOptions
               (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoVar
  type EmFun (ReaderT TranslationOptions
              (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoFun
  type EmConstr (ReaderT TranslationOptions
                 (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoCon
  type EmField (ReaderT TranslationOptions
                (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoField
  type EmFunArg (ReaderT TranslationOptions
                 (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoVar
  type EmLVar (ReaderT TranslationOptions
               (StateT (RealizationState inp st) IO)) (RExpr inp st) = E.NoVar
  embed e = return (RExpr e)
  embedQuantifier = error "Cannot embed quantifier into RExpr."
  embedGetField = error "Cannot embed datatypes into RExpr."
  embedConstrTest = error "Cannot embed datatypes into RExpr."
  embedConst c = do
    val <- valueFromConcrete
           (error "Cannot embed datatypes into RExpr.")
           c
    return (RExpr (E.Const val))
  embedTypeOf (RExpr e) = E.expressionType (return.getType) (return.getType) (return.getFunType)
                          (return.getConType) (return.getFieldType) (return.getType) (return.getType)
                          embedTypeOf e
  embedTypeOf (RRef (DefExpr _ tp)) = return tp
  embedTypeOf (RInput rev :: RExpr inp st tp) = do
    inp <- gets inputAnnotation
    return $ revType (Proxy::Proxy inp) inp rev
  embedTypeOf (RState rev :: RExpr inp st tp) = do
    st <- gets stateAnnotation
    return $ revType (Proxy::Proxy st) st rev

uniqueName :: String -> Realization inp st String
uniqueName name = do
  st <- get
  let idx = Map.findWithDefault 0 name (names st)
  put (st { names = Map.insert name (idx+1) (names st) })
  if idx==0
    then return name
    else return $ name++"$"++show idx

addEvent :: Event inp st -> Edge inp st
         -> Realization inp st (Edge inp st)
addEvent ev edge = do
  s <- get
  let evs = events s
      evId = Map.size evs
  put s { events = Map.insert evId ev evs }
  return edge { observedEvents = Map.insert evId () (observedEvents edge) }

addInstruction :: Maybe (Ptr CallInst) -> Ptr Instruction
               -> LLVMExpr BoolType
               -> InstructionValue ProgramInput ProgramState
               -> Edge ProgramInput ProgramState
               -> LLVMRealization (Edge ProgramInput ProgramState)
addInstruction th i act val edge = do
  modify $ \s -> s { instructions = Map.insert (th,i) (act,val) (instructions s) }
  return edge { edgeValues = Map.insert (th,i) AlwaysDefined (edgeValues edge) }

define :: (Composite inp,Composite st) => String -> RExpr inp st tp
       -> Realization inp st (RExpr inp st tp)
define name expr = do
  name' <- uniqueName name
  tp <- embedTypeOf expr
  s <- get
  let defs = definitions s
      sz = DMap.size defs
      def = Definition expr name'
      key = DefExpr sz tp
  put s { definitions = DMap.insert key def defs }
  return (RRef key)

defineSym :: (GetType (RExpr inp st),Composite inp,Composite st)
          => String -> InstructionValue inp st
          -> Realization inp st (InstructionValue inp st)
defineSym name val = do
  nsym <- foldExprs (\_ e -> define name e) (symbolicValue val)
  return $ val { symbolicValue = nsym }

mkLatchInstr :: Maybe (Ptr CallInst) -- ^ The current thread
             -> Ptr Instruction -- ^ The latch instruction
             -> LLVMRealization LLVMVal
mkLatchInstr th i = do
  psD <- gets stateAnnotation
  let thD = getThreadStateDesc th psD
  tp <- case Map.lookup i (latchValueDesc thD) of
    Nothing -> do
      liftIO $ hPutStrLn stderr ("Unknown latch value: "++showValue i "")
      opts <- ask
      stp <- liftIO (LLVM.getType i >>= translateType0 opts)
      let rtp = structToVector stp
      modify $ \s -> s { stateAnnotation = updateThreadStateDesc th
                                           (\ts -> ts { latchValueDesc = Map.insert i rtp
                                                                         (latchValueDesc ts)
                                                      }) (stateAnnotation s) }
      return rtp
    Just tp -> return tp
  createComposite (\_ rev -> do
                      let thRev = LatchValue i rev
                          pRev = case th of
                            Nothing -> MainState thRev
                            Just th' -> ThreadState' th' thRev
                      return $ RState pRev) tp

mkThreadArgument :: Maybe (Ptr CallInst)
                 -> Ptr Argument
                 -> LLVMRealization LLVMVal
mkThreadArgument th arg = do
  thSt <- gets $ getThreadStateDesc th . stateAnnotation
  case threadArgumentDesc thSt of
    Just (arg',tp)
      -> if arg==arg'
         then createComposite (\_ rev -> do
                                  let argRev = ThreadArgument rev
                                      pRev = case th of
                                        Nothing -> MainState argRev
                                        Just th' -> ThreadState' th' argRev
                                  return $ RState pRev
                              ) tp
         else error $ "Function arguments (other than thread arguments) not supported."
    Nothing -> do
      name <- liftIO $ getNameString arg
      error $ "Function arguments (other than thread arguments) not supported: "++name

mkMemoryRef :: Maybe (Ptr CallInst) -> MemoryTrg
            -> LLVMRealization (AllocVal (RExpr ProgramInput ProgramState))
mkMemoryRef _ (AllocTrg i) = do
  memDesc <- gets $ memoryDesc . stateAnnotation
  case Map.lookup (Left i) memDesc of
    Just tp -> createComposite (\_ rev -> return $ RState $ GlobalMemory (Left i) rev) tp
mkMemoryRef _ (GlobalTrg g) = do
  memDesc <- gets $ memoryDesc . stateAnnotation
  case Map.lookup (Right g) memDesc of
    Just tp -> createComposite (\_ rev -> return $ RState $ GlobalMemory (Right g) rev) tp
mkMemoryRef th (LocalTrg l) = do
  memDesc <- gets $ threadGlobalDesc . getThreadStateDesc th . stateAnnotation
  case Map.lookup l memDesc of
    Just tp -> createComposite
               (\_ rev -> do
                   let thRev = LocalMemory l rev
                       pRev = case th of
                         Nothing -> MainState thRev
                         Just th' -> ThreadState' th' thRev
                   return $ RState pRev) tp

stepVar :: Maybe (Ptr CallInst) -> LLVMExpr BoolType
stepVar Nothing = RInput $ MainInput Step
stepVar (Just th) = RInput $ ThreadInput' th Step

instance GEq DefExpr where
  geq (DefExpr i1 tp1) (DefExpr i2 tp2)
    = if i1==i2
      then case geq tp1 tp2 of
      Just Refl -> Just Refl
      else Nothing

instance GCompare DefExpr where
  gcompare (DefExpr i1 tp1) (DefExpr i2 tp2) = case compare i1 i2 of
    EQ -> case geq tp1 tp2 of
      Just Refl -> GEQ
    LT -> GLT
    GT -> GGT

instance (GShow (RevComp inp),GShow (RevComp st)) => Show (RExpr inp st tp) where
  showsPrec p (RExpr e) = showsPrec p e
  showsPrec p (RInput rev) = showParen (p>10) $
                             showString "input " .
                             gshowsPrec 11 rev
  showsPrec p (RState rev) = showParen (p>10) $
                             showString "state " .
                             gshowsPrec 11 rev
  showsPrec p (RRef (DefExpr n _)) = showParen (p>10) $
                                     showString "gate " .
                                     showsPrec 11 n

instance (GShow (RevComp inp),GShow (RevComp st)) => GShow (RExpr inp st) where
  gshowsPrec = showsPrec

writeBasedAliasAnalysis :: RealizationState inp st
                        -> ProgramStateDesc
                        -> ProgramStateDesc
writeBasedAliasAnalysis real start = foldl processEvent start (events real)
  where
    processEvent st ev = let trgs = Map.keys (target ev)
                             tp = symbolicType (writeContent ev)
                             th = eventThread ev
                         in foldl (processWrite th tp) st trgs
    processWrite th tp st trg = case memoryLoc trg of
      AllocTrg instr -> st { memoryDesc = Map.adjust (insertType tp (offsetPattern trg))
                                          (Left instr)
                                          (memoryDesc st)
                           }
      GlobalTrg glob -> st { memoryDesc = Map.adjust (insertType tp (offsetPattern trg))
                                          (Right glob)
                                          (memoryDesc st)
                           }
      LocalTrg glob -> updateThreadStateDesc th
                       (\st' -> st' { threadGlobalDesc = Map.adjust
                                                         (insertType tp (offsetPattern trg))
                                                         glob
                                                         (threadGlobalDesc st')
                                    }) st
    insertType tp (_:is) (TpStatic sz str) = TpStatic sz (insertTypeStruct tp is str)
    insertType tp (_:is) (TpDynamic str) = TpDynamic (insertTypeStruct tp is str)
    insertType tp [] (TpStatic sz str) = TpStatic sz (insertTypeStruct tp [] str)
    insertTypeStruct tp [] (Singleton tp') = case typeUnion tp tp' of
      Just rtp -> Singleton rtp
      Nothing -> trace ("insertTypeStruct: Warning, type error") $ Singleton tp'
    insertTypeStruct tp (StaticAccess i:is) (Struct tps) = Struct (insert' i tps)
      where
        insert' 0 (tp':tps) = (insertTypeStruct tp is tp'):tps
        insert' n (tp':tps) = tp':(insert' (n-1) tps)
    insertTypeStruct tp (DynamicAccess:is) (Struct tps)
      = Struct (fmap (insertTypeStruct tp is) tps)

updateLatchTypes :: RealizationState inp ProgramState
                 -> ProgramStateDesc
                 -> ProgramStateDesc
updateLatchTypes real start
  = start { mainStateDesc = update Nothing (mainStateDesc start)
          , threadStateDesc = Map.mapWithKey
                              (\th st -> update (Just th) st)
                              (threadStateDesc start)
          }
  where
    update th st = st { latchValueDesc = Map.mapWithKey
                                         (\instr tp
                                          -> case Map.lookup (th,instr) (instructions real) of
                                          Just (_,val) -> case typeUnion tp (symbolicType val) of
                                            Just rtp -> rtp
                                            Nothing -> trace ("Warning: Type error, cannot union "++show tp++" and "++show (symbolicType val)) tp
                                          Nothing -> tp
                                         ) (latchValueDesc st)
                      }

updateThreadArguments :: RealizationState inp ProgramState
                      -> ProgramStateDesc
                      -> ProgramStateDesc
updateThreadArguments real st = foldl processSpawns st (Map.toList $ spawnEvents real)
  where
    processSpawns st (th,xs) = foldl (processSpawn th) st xs
    processSpawn th st (_,_,Nothing) = st
    processSpawn th st (_,_,Just val)
      = updateThreadStateDesc (Just th)
        (\st' -> st' { threadArgumentDesc = case threadArgumentDesc st' of
                         Just (arg,tp) -> case typeUnion tp (symbolicType val) of
                           Just rtp -> Just (arg,rtp)
                     }) st

updateThreadReturns :: RealizationState inp ProgramState
                    -> ProgramStateDesc
                    -> ProgramStateDesc
updateThreadReturns real st = foldl processTerms st (Map.toList $ termEvents real)
  where
    processTerms st (th,xs) = foldl (processTerm th) st xs
    processTerm th st (_,Nothing) = st
    processTerm th st (_,Just val)
      = updateThreadStateDesc (Just th)
        (\st' -> st' { threadReturnDesc = case threadReturnDesc st' of
                         Just tp -> case typeUnion tp (symbolicType val) of
                           Just rtp -> Just rtp
                     }) st

{-withAliasAnalysis :: Ptr Module -> (Ptr AliasAnalysis -> IO a) -> IO a
withAliasAnalysis mod act = do
  aaPass <- createBasicAliasAnalysisPass
  aaEvalPass <- createAAEvalPass
  pm <- newPassManager
  passManagerAdd pm aaPass
  passManagerAdd pm aaEvalPass
  passManagerRun pm mod
  aa <- passGetAnalysis aaPass
  res <- act aa
  deletePassManager pm
  return res
-}

mkAnd :: (Composite inp,Composite st) => [RExpr inp st BoolType] -> Realization inp st (RExpr inp st BoolType)
mkAnd [] = true
mkAnd [x] = return x
mkAnd xs = and' xs

mkOr :: (Composite inp,Composite st) => [RExpr inp st BoolType] -> Realization inp st (RExpr inp st BoolType)
mkOr [] = false
mkOr [x] = return x
mkOr xs = or' xs

constantIntValue :: (Composite inp,Composite st) => Integer -> Realization inp st (InstructionValue inp st)
constantIntValue n = do
  useBW <- asks bitPrecise
  if useBW
    then error "constantIntValue unimplemented for bitvectors"
    else do
      c <- embedConst (IntValueC n)
      return $ InstructionValue { symbolicType = TpInt
                                , symbolicValue = ValInt c
                                , alternative = Just $ IntConst n }

constantBoolValue :: (Composite inp,Composite st) => Bool -> Realization inp st (InstructionValue inp st)
constantBoolValue n = do
  c <- embedConst (BoolValueC n)
  return $ InstructionValue { symbolicType = TpBool
                            , symbolicValue = ValBool c
                            , alternative = Nothing }

initialStateDesc :: TranslationOptions
                 -> ProgramInfo -> Ptr Module
                 -> IO ProgramStateDesc
initialStateDesc opts info mod = do
  hPutStrLn stderr $ "Program info: "++show info
  let threads' = Map.insert Nothing () $
                 fmap (const ()) $
                 Map.mapKeysMonotonic Just (threads info)
  globals <- moduleGetGlobalList mod >>= ipListToList
  (globSig,locSig) <- foldlM (\(gmp,lmp) glob -> do
                                  ptrTp <- LLVM.getType glob
                                  tp <- sequentialTypeGetElementType ptrTp
                                  symTp <- translateType0 opts tp
                                  isLocal <- globalVariableIsThreadLocal glob
                                  if isLocal
                                    then return $ (gmp,Map.insert glob (TpStatic 1 symTp) lmp)
                                    else return (Map.insert (Right glob) (TpStatic 1 symTp) gmp,lmp)
                             ) (Map.empty,Map.empty) globals
  allocSig <- sequence $ Map.mapWithKey
              (\alloc info -> do
                   tp <- translateAllocType0 opts (allocType info)
                   case allocSize info of
                     Nothing -> return $ case allocQuantity info of
                       Finite n -> TpStatic (fromInteger n) tp
                       Infinite -> TpDynamic tp
                     Just sz -> case allocQuantity info of
                       _ -> return $ TpDynamic tp
                       Finite 1 -> return $ TpDynamic tp
                       _ -> error $ "Dynamic allocations in a loop not yet supported."
              ) (allocations info)
  let allocSig' = Map.mapKeysMonotonic Left allocSig
  mainDesc <- th0 locSig Nothing (mainThread info)
  thDesc <- Map.traverseWithKey (\th -> th0 locSig (Just th)) (threads info)
  return ProgramStateDesc { mainStateDesc = mainDesc
                          , threadStateDesc = thDesc
                          , memoryDesc = Map.union globSig allocSig'
                          }
  where
    th0 loc th tinfo = do
      arg <- case threadArg tinfo of
        Nothing -> return Nothing
        Just (val,rtp) -> do
          tp <- case rtp of
            Left ptp -> do
              rtp' <- translateType0 opts ptp
              return $ TpPtr Map.empty rtp'
            Right itp -> do
              Singleton tp' <- translateType0 opts (castUp itp)
              return tp'
          return (Just (val,tp))
      ret <- case Map.lookup (threadFunction tinfo) (functionReturns info) of
        Nothing -> return Nothing
        Just rtp -> do
          Singleton tp <- translateType0 opts rtp
          return (Just tp)
      return $ ThreadStateDesc { latchBlockDesc = entryPoints tinfo
                               , latchValueDesc = Map.empty
                               , threadArgumentDesc = arg
                               , threadGlobalDesc = loc
                               , threadReturnDesc = ret }

realizeProgramFix :: TranslationOptions
                  -> Ptr Module -> Ptr LLVM.Function
                  -> IO LLVMTransRel
realizeProgramFix opts mod fun = do
  hPutStrLn stderr $ "Main function: "++showValue fun ""
  info <- getProgramInfo mod fun
  start <- initialStateDesc opts info mod
  runRealization opts info start mod fun (realizeProgram info)

runRealization :: TranslationOptions
               -> ProgramInfo
               -> ProgramStateDesc
               -> Ptr Module -> Ptr LLVM.Function
               -> LLVMRealization ()
               -> IO LLVMTransRel
runRealization opts info st mod fun act = do
  globals <- moduleGetGlobalList mod >>= ipListToList
  globInit <- foldlM (\mp glob -> do
                         init <- globalVariableGetInitializer glob
                         val <- getConstant opts init
                         return (Map.insert glob (ValStatic [val]) mp)
                     ) Map.empty globals
  mainBlk <- getEntryBlock fun
  thBlks <- sequence $ Map.mapWithKey
            (\th _ -> do
                threadVal <- callInstGetArgOperand th 1
                case castDown threadVal of
                 Just threadFun -> getEntryBlock threadFun
            ) (threads info)
  let th_inp = ThreadInputDesc Map.empty
      real0 = RealizationSt { edges = Map.empty
                            , yieldEdges = Map.empty
                            , internalYieldEdges = Map.empty
                            , instructions = Map.empty
                            , stateAnnotation = st
                            , inputAnnotation = ProgramInputDesc { mainInputDesc = th_inp
                                                                 , threadInputDesc = fmap (const th_inp)
                                                                                     (threads info) }
                            , definitions = DMap.empty
                            , names = Map.empty
                            , events = Map.empty
                            , spawnEvents = Map.empty
                            , termEvents = Map.empty
                            , assertions = []
                            , memoryInit = globInit
                            , mainBlock = mainBlk
                            , threadBlocks = thBlks
                            , programInfo = info
                            }
  hPutStrLn stderr $ "Aliasing: "++show st
  (res,nreal) <- runStateT
                   (runReaderT
                    (do
                        initEdges
                        act
                        nst <- get
                        let nxt0 = writeBasedAliasAnalysis nst (stateAnnotation nst)
                            nxt1 = updateLatchTypes nst nxt0
                            nxt2 = updateThreadArguments nst nxt1
                            nxt3 = updateThreadReturns nst nxt2
                        if nxt3==st
                          then do
                          trans <- computeTransitionRelation
                          return (Right trans)
                          else return (Left nxt3)) opts) real0
  case res of
    Right trans -> do
      hPutStrLn stderr $ "Next: "++show (llvmNext trans)
      hPutStrLn stderr $ "Definitions: "++
        showListWith (\((DefExpr n _) :=> (Definition e name))
                       -> showsPrec 0 n .
                          showChar '[' .
                          showString name .
                          showString "] ~> " .
                          gshowsPrec 0 e
                     ) (DMap.toList $ llvmDefinitions trans) ""
      return trans
    Left nst -> runRealization opts info nst mod fun act

initEdges :: Realization ProgramInput ProgramState ()
initEdges = do
  info <- gets programInfo
  edges' <- fmap Map.fromList $ sequence
            [ do
                phis <- if sblk==0
                        then liftIO $ allPhiNodes blk
                        else return []
                phis' <- mapM (\phi -> do
                                  val <- mkLatchInstr th (castUp phi)
                                  return ((th,castUp phi),
                                          InstructionValue (symType val) val Nothing)
                              ) phis
                return ((th,blk,sblk),
                        Edge { edgeValues = Map.empty
                             , edgeConditions = [EdgeCondition { edgeActivation = act
                                                               , edgePhis = Map.fromList phis' }]
                             , observedEvents = Map.empty })
            | (th,thInfo) <- (Nothing,mainThread info):
                             [(Just th',thInfo') | (th',thInfo') <- Map.toList (threads info)]
            , (blk,sblk) <- Map.keys (entryPoints thInfo)
            , let revAct = LatchBlock blk sblk
                  act = RState $ case th of
                    Nothing -> MainState revAct
                    Just th' -> ThreadState' th' revAct ]
  modify $ \s -> s { edges = edges' }

realizeProgram :: ProgramInfo
               -> LLVMRealization ()
realizeProgram info = do
  realizeThread info Nothing (mainThread info)
  mapM_ (\(call,th) -> realizeThread info (Just call) th
        ) (Map.toList (threads info))
  where
    realizeThread info th tinfo
      = mapM (\(blk,sblk) -> realizeBlock th blk sblk info)
        (blockOrder tinfo)

realizeInstructions :: Maybe (Ptr CallInst)
                    -> Ptr BasicBlock
                    -> Int
                    -> LLVMExpr BoolType
                    -> [Ptr Instruction]
                    -> Edge ProgramInput ProgramState
                    -> LLVMRealization ()
realizeInstructions thread blk sblk act (i:is) edge = do
  iStr <- liftIO $ valueToString i
  --putStrLn $ "Realizing "++iStr
  (res,nact) <- while ("Realizing "++iStr++": ") $
                realizeInstruction thread blk sblk act i edge
  case res of
   Nothing -> return ()
   Just nedge -> realizeInstructions thread blk sblk nact is nedge

realizeInstruction :: Maybe (Ptr CallInst)
                   -> Ptr BasicBlock
                   -> Int
                   -> LLVMExpr BoolType
                   -> Ptr Instruction
                   -> Edge ProgramInput ProgramState
                   -> LLVMRealization
                      (Maybe (Edge ProgramInput ProgramState),
                       LLVMExpr BoolType)
realizeInstruction thread blk sblk act i@(castDown -> Just call) edge = do
  fname <- liftIO $ getFunctionName call
  case fname of
   "__thread_spawn" -> do
     thId <- liftIO $ getOperand call 0
     -- Get the pointer to the thread id
     thId' <- realizeValue thread thId edge
     -- Write to the thread id
     thArg <- gets $ threadArgumentDesc . getThreadStateDesc (Just call) . stateAnnotation
     arg <- case thArg of
       Nothing -> return Nothing
       Just _ -> do
         arg <- liftIO $ getOperand call 2
         arg' <- realizeValue thread arg edge
         return (Just arg')
     cTrue <- true
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue thId') of
                          Just r -> r
                    ncond <- act .&. cond
                    return (ncond,idx)) (tpPtr $ symbolicType thId')
     nedge <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = InstructionValue { symbolicType = TpThreadId (Map.singleton call ())
                                                                     , symbolicValue = ValThreadId $ Map.singleton call cTrue
                                                                     , alternative = Nothing }
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge
     modify $ \s -> s { spawnEvents = Map.insertWith (++) call [(thread,act,arg)] (spawnEvents s) }
     return (Just nedge,act)
   "__thread_join" -> do
     thId <- liftIO $ getOperand call 0
     retTrg <- liftIO $ getOperand call 1
     thId' <- realizeValue thread thId edge
     liftIO $ hPutStrLn stderr $ "join reads id from: "++show (symbolicValue thId')
     retTrg' <- realizeValue thread retTrg edge
     rthId <- memoryRead thread i thId' edge
     liftIO $ hPutStrLn stderr $ "join: "++show (symbolicValue rthId)
     gt <- sequence [ embed (Not $ RState $ ThreadActivation call') >>=
                      embed.(cact :&:)
                    | (call',cact) <- Map.toList $ valThreadId $
                                      symbolicValue rthId
                    ] >>= mkOr
     cond <- define "blocking" gt
     let mkResults _ [] = return Nothing
         mkResults ptr (th:ths) = do
           thDescr <- gets $ threadStateDesc . stateAnnotation
           case Map.lookup th thDescr of
             Just tsD -> case threadReturnDesc tsD of
               Nothing -> mkResults ptr ths
               Just retTp -> do
                 rest <- mkResults ptr ths
                 case rest of
                   Nothing -> do
                     rval <- createComposite
                             (\_ rev -> return $ RState $ ThreadState' th $ ThreadReturn rev
                             ) retTp
                     return $ Just (rval,retTp)
                   Just (val',tp') -> if retTp==tp'
                                      then do
                                        val <- createComposite
                                               (\_ rev -> return $ RState $ ThreadState' th $
                                                          ThreadReturn rev
                                               ) retTp
                                        rval <- symITE cond val val'
                                        return $ Just (rval,retTp)
                                      else error "Different thread return types, need better alias analysis."
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue retTrg') of
                          Just r -> r
                    ncond <- embed $ act :&: cond
                    return (ncond,idx)
                ) (tpPtr $ symbolicType retTrg')
     joinReturn <- mkResults (symbolicValue rthId) (Map.keys $ tpThreadId $ symbolicType rthId)
     nedge <- case joinReturn of
       Nothing -> return edge
       Just (ret,tp) -> addEvent (WriteEvent { target = ntarget
                                             , writeContent = InstructionValue { symbolicType = tp
                                                                               , symbolicValue = ret
                                                                               , alternative = Nothing }
                                             , eventThread = thread
                                             , eventOrigin = castUp call
                                             }) edge
     nact <- embed $ act :&: cond
     return (Just nedge,nact)
   "__thread_kill" -> do
     thId <- liftIO $ getOperand call 0
     thId' <- realizeValue thread thId edge
     rthId <- memoryRead thread i thId' edge
     terms <- sequence $ Map.mapWithKey
              (\th _ -> do
                  ths <- gets $ threads . programInfo
                  returns <- gets $ functionReturns . programInfo
                  case Map.lookup th ths of
                    Just info -> do
                      ret <- case Map.lookup (threadFunction info) returns of
                        Just tp -> fmap Just $ defaultSymValue tp
                        Nothing -> return Nothing
                      case Map.lookup th (valThreadId $ symbolicValue rthId) of
                        Just cond -> do
                          rcond <- embed $ act :&: cond
                          return [(rcond,ret)]
              ) (tpThreadId $ symbolicType rthId)
     modify $ \s -> s { termEvents = Map.unionWith (++) (termEvents s) terms }
     return (Just edge,act)
   "assert" -> do
     val <- liftIO $ getOperand call 0
     val' <- realizeValue thread val edge
     branch <- asks dedicatedErrorState
     nact <- if branch
             then embed $ act :&: (valBool $ symbolicValue val')
             else return act
     assertion <- embed $ act :=>: (valBool $ symbolicValue val')
     modify $ \s -> s { assertions = (thread,assertion):(assertions s) }
     return (Just edge,nact)
   "__error" -> do
     dontStep <- gets $ Map.null . threadStateDesc . stateAnnotation
     assertion <- embed $ Not act
     modify $ \s -> s { assertions = (thread,assertion):(assertions s) }
     return (Nothing,act)
   "pthread_mutex_init" -> do
     -- Ignore this call for now...
     ret <- constantIntValue 0
     nedge <- addInstruction thread i act ret edge
     return (Just nedge,act)
   "pthread_mutex_destroy" -> do
     -- Ignore this call for now...
     ret <- constantIntValue 0
     nedge <- addInstruction thread i act ret edge
     return (Just nedge,act)
   "pthread_mutex_lock" -> do
     ptr <- liftIO $ getOperand call 0
     ptr' <- realizeValue thread ptr edge
     lock <- memoryRead thread i ptr' edge
     ret <- constantIntValue 0
     edge1 <- addInstruction thread i act ret edge
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr') of
                          Just r -> r
                    ncond <- embed $ act :&: cond
                    return (ncond,idx)
                ) (tpPtr $ symbolicType ptr')
     writeValue <- constantBoolValue True
     edge2 <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = writeValue
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge1
     nact <- embed (Not $ valBool $ symbolicValue lock) >>=
             embed.(act :&:)
     return (Just edge2,nact)
   "pthread_mutex_unlock" -> do
     ptr <- liftIO $ getOperand call 0
     ptr' <- realizeValue thread ptr edge
     lock <- memoryRead thread i ptr' edge
     ret <- constantIntValue 0
     edge1 <- addInstruction thread i act ret edge
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr') of
                          Just r -> r
                    ncond <- embed $ act :&: cond
                    return (ncond,idx)
                ) (tpPtr $ symbolicType ptr')
     writeValue <- constantBoolValue False
     edge2 <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = writeValue
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge1
     return (Just edge2,act)
   "pthread_rwlock_init" -> do
     -- Ignore this call for now
     ret <- constantIntValue 0
     nedge <- addInstruction thread i act ret edge
     return (Just nedge,act)
   "pthread_rwlock_destroy" -> do
     -- Ignore this call for now...
     ret <- constantIntValue 0
     nedge <- addInstruction thread i act ret edge
     return (Just nedge,act)
   "pthread_rwlock_rdlock" -> do
     ptr <- liftIO $ getOperand call 0
     ptr' <- realizeValue thread ptr edge
     lock <- memoryRead thread i ptr' edge
     ret <- constantIntValue 0
     edge1 <- addInstruction thread i act ret edge
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr') of
                          Just r -> r
                    ncond <- embed $ act :&: cond
                    return (ncond,idx)) (tpPtr $ symbolicType ptr')
     writeValue <- case symbolicValue lock of
       ValVector [wr,ValInt rd] -> do
         nrd <- rd .+. (cint 1)
         return $ ValVector [wr,ValInt nrd]
     edge2 <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = InstructionValue { symbolicType = TpVector [TpBool,TpInt]
                                                                     , symbolicValue = writeValue
                                                                     , alternative = Nothing }
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge1
     nact <- act .&. (not' $ valBool $ head $ valVector $ symbolicValue lock)
     return (Just edge2,nact)
   "pthread_rwlock_wrlock" -> do
     ptr <- liftIO $ getOperand call 0
     ptr' <- realizeValue thread ptr edge
     lock <- memoryRead thread i ptr' edge
     ret <- constantIntValue 0
     edge1 <- addInstruction thread i act ret edge
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr') of
                          Just r -> r
                    ncond <- act .&. cond
                    return (ncond,idx)) (tpPtr $ symbolicType ptr')
     writeValue <- do
       wrLock <- true
       rdLock <- 0
       return $ ValVector [ValBool wrLock,ValInt rdLock]
     edge2 <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = InstructionValue { symbolicType = TpVector [TpBool,TpInt]
                                                                     , symbolicValue = writeValue
                                                                     , alternative = Nothing }
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge1
     nact <- act .&. (not' $ valBool $ head $ valVector $ symbolicValue lock)
     return (Just edge2,nact)
   "pthread_rwlock_unlock" -> do
     ptr <- liftIO $ getOperand call 0
     ptr' <- realizeValue thread ptr edge
     lock <- memoryRead thread i ptr' edge
     ret <- constantIntValue 0
     edge1 <- addInstruction thread i act ret edge
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue ptr') of
                          Just r -> r
                    ncond <- act .&. cond
                    return (ncond,idx)) (tpPtr $ symbolicType ptr')
     writeValue <- case symbolicValue lock of
       ValVector [ValBool wr,ValInt rd] -> do
         wrLock <- false
         rdLock <- ite (rd .==. (cint 0)) (cint 0) (rd .-. (cint 1))
         return $ ValVector [ValBool wrLock
                            ,ValInt rdLock]
     edge2 <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = InstructionValue { symbolicType = TpVector [TpBool,TpInt]
                                                                     , symbolicValue = writeValue
                                                                     , alternative = Nothing }
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge1
     return (Just edge2,act)
   "__cond_register" -> do
     cond <- liftIO $ getOperand call 0
     mutex <- liftIO $ getOperand call 1
     cond' <- realizeValue thread cond edge
     mutex' <- realizeValue thread mutex edge
     --hPutStrLn stderr $ "Condition pointer: "++show (tpPtr $ symbolicType cond')
     rcond <- memoryRead thread i cond' edge
     rmutex <- memoryRead thread i mutex' edge
     mutexTrg <- sequence $ Map.mapWithKey
                 (\loc _ -> do
                     let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue mutex') of
                           Just r -> r
                     ncond <- act .&. cond
                     return (ncond,idx)) (tpPtr $ symbolicType mutex')
     mutexCont <- constantBoolValue False
     edge1 <- addEvent (WriteEvent { target = mutexTrg
                                   , writeContent = mutexCont
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge
     let waiting = case Map.lookup thread $ valCondition (symbolicValue rcond) of
           Just b -> b
         locked = valBool $ symbolicValue rmutex
     condTrg <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue cond') of
                          Just r -> r
                    ncond <- embed $ act :&: cond
                    return (ncond,idx)
                ) (tpPtr $ symbolicType cond')
     condCont <- do
       ctrue <- true
       return $ rcond { symbolicType = let orig = symbolicType rcond
                                       in orig { tpCondition = Map.insert thread ()
                                                               (tpCondition orig) }
                      , symbolicValue = let orig = symbolicValue rcond
                                        in orig { valCondition = Map.insert thread ctrue
                                                                 (valCondition orig) }
                      }
     edge2 <- addEvent (WriteEvent { target = condTrg
                                   , writeContent = condCont
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge1
     return (Just edge2,act)
   "__cond_wait" -> do
     cond <- liftIO $ getOperand call 0
     mutex <- liftIO $ getOperand call 1
     cond' <- realizeValue thread cond edge
     mutex' <- realizeValue thread mutex edge
     rcond <- memoryRead thread i cond' edge
     rmutex <- memoryRead thread i mutex' edge
     let waiting = case Map.lookup thread $ valCondition (symbolicValue rcond) of
           Just b -> b
         locked = valBool $ symbolicValue rmutex
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue mutex') of
                          Just r -> r
                    ncond <- act .&. cond
                    return (ncond,idx)) (tpPtr $ symbolicType mutex')
     writeCont <- constantBoolValue True
     nedge <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = writeCont
                                   , eventThread = thread
                                   , eventOrigin = castUp call
                                   }) edge
     nact <- do
       notWaiting <- embed $ Not waiting
       notLocked <- embed $ Not locked
       embed $ And (act ::: notWaiting ::: notLocked ::: Nil)
     return (Just nedge,nact)
   "__cond_signal" -> do
     -- We must select a thread at random
     cond <- liftIO $ getOperand call 0
     cond' <- realizeValue thread cond edge
     rcond <- memoryRead thread i cond' edge
     modify $ \s -> s { inputAnnotation = updateThreadInputDesc thread
                                          (\ti -> ti { nondetTypes = Map.insert i
                                                                     (symbolicType rcond)
                                                                     (nondetTypes ti) }
                                          ) (inputAnnotation s) }
     vec <- createComposite
            (\_ rev -> do
                let nRev = Nondet i rev
                    pRev = case thread of
                      Nothing -> MainInput nRev
                      Just th -> ThreadInput' th nRev
                return $ RInput pRev) (symbolicType rcond)
     nval <- fmap ValCondition $ sequence $ snd $ Map.mapAccum
             (\cont (sel,act) -> (cont .&. (not' (sel .&. act)),
                                  ite act (not' (cont .&. sel)) false)
             ) true
             (Map.intersectionWith (\x y -> (x,y))
              (valCondition vec) (valCondition $ symbolicValue rcond))
     hasSelected <- sequence [ sel .&. act
                             | (sel,act) <- Map.elems (Map.intersectionWith (\x y -> (x,y))
                                                       (valCondition vec)
                                                       (valCondition $ symbolicValue rcond)) ]
                    >>= mkOr
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue cond') of
                          Just r -> r
                    ncond <- act .&. cond
                    return (ncond,idx)) (tpPtr $ symbolicType cond')
     nedge <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = rcond { symbolicValue = nval }
                                   , eventThread = thread
                                   , eventOrigin = i
                                   }) edge
     nact <- act .&. hasSelected
     return (Just nedge,nact)
   "__cond_broadcast" -> do
     cond <- liftIO $ getOperand call 0
     cond' <- realizeValue thread cond edge
     rcond <- memoryRead thread i cond' edge
     ntarget <- sequence $ Map.mapWithKey
                (\loc _ -> do
                    let (cond,idx) = case Map.lookup loc (valPtr $ symbolicValue cond') of
                          Just r -> r
                    ncond <- act .&. cond
                    return (ncond,idx)) (tpPtr $ symbolicType cond')
     ncond <- fmap ValCondition $ sequence $ fmap (const (constant False))
              (tpCondition $ symbolicType rcond)
     nedge <- addEvent (WriteEvent { target = ntarget
                                   , writeContent = rcond { symbolicValue = ncond
                                                          }
                                   , eventThread = thread
                                   , eventOrigin = i
                                   }) edge
     return (Just nedge,act)
   "pthread_yield" -> do
     modify $ \s -> s { yieldEdges = Map.insert (thread,blk,sblk+1)
                                     (edge { edgeConditions = [EdgeCondition act Map.empty] })
                                     (yieldEdges s) }
     return (Nothing,act)
   "__yield" -> do
     modify $ \s -> s { yieldEdges = Map.insert (thread,blk,sblk+1)
                                     (edge { edgeConditions = [EdgeCondition act Map.empty] })
                                     (yieldEdges s) }
     return (Nothing,act)
   "__yield_local" -> do
     modify $ \s -> s { internalYieldEdges = Map.insert (thread,blk,sblk+1)
                                             (edge { edgeConditions = [EdgeCondition act Map.empty] })
                                             (internalYieldEdges s) }
     return (Nothing,act)
   "__assume" -> do
     cond <- liftIO $ getOperand call 0
     cond' <- realizeValue thread cond edge
     nact <- act .&. (valBool $ symbolicValue cond')
     return (Just edge,nact)
   "__builtin_assume" -> return (Just edge,act)
   '_':'_':'u':'n':'s':'i':'g':'n':'e':'d':_ -> do
     var <- liftIO $ getOperand call 0
     var' <- realizeValue thread var edge
     nact <- act .&. ((valInt $ symbolicValue var') .>=. (cint 0))
     return (Just edge,nact)
   "pthread_exit" -> case thread of
     Nothing -> return (Nothing,act)
     Just th -> do
       retVal <- liftIO (getOperand call 0) >>=
                 \ret -> realizeValue thread ret edge
       modify $ \s -> s { termEvents = Map.insertWith (++) th
                                       [(act,Just retVal)] (termEvents s) }
       return (Nothing,act)
   -- Ignore atomic block denotions
   -- Only important for inserting yield instructions
   "__atomic_begin" -> return (Just edge,act)
   "__atomic_end" -> return (Just edge,act)
   -- Ignore llvm annotations
   "llvm.lifetime.start" -> return (Just edge,act)
   "llvm.lifetime.end" -> return (Just edge,act)
   "llvm.stacksave" -> return (Just edge,act)
   "llvm.stackrestore" -> return (Just edge,act)
   "exit" -> return (Nothing,act)
   _ -> do
     val <- realizeDefInstruction thread i edge
     modify $ \s -> s { instructions = Map.insert (thread,i) (act,val) (instructions s) }
     return (Just edge { edgeValues = Map.insert (thread,i) AlwaysDefined
                                      (edgeValues edge) },
             act)
realizeInstruction thread blk sblk act (castDown -> Just store) edge = do
  ptr <- liftIO $ storeInstGetPointerOperand store
  val <- liftIO $ storeInstGetValueOperand store
  ptr' <- realizeValue thread ptr edge
  val' <- realizeValue thread val edge
  nedge <- memoryWrite thread (castUp store) act ptr' val' edge
  return (Just nedge,act)
realizeInstruction thread blk sblk act (castDown -> Just br) edge = do
  srcBlk <- liftIO $ instructionGetParent br
  isCond <- liftIO $ branchInstIsConditional br
  if isCond
    then do
    cond <- liftIO $ branchInstGetCondition br
    cond' <- realizeValue thread cond edge
    let cond'' = valBool $ symbolicValue cond'
    condT <- act .&. cond''
    condF <- act .&. (not' cond'')
    ifT <- liftIO $ terminatorInstGetSuccessor br 0
    ifF <- liftIO $ terminatorInstGetSuccessor br 1
    phisT <- realizePhis thread srcBlk ifT edge
    phisF <- realizePhis thread srcBlk ifF edge
    modify $ \s -> s { edges = Map.insertWith mappend (thread,ifT,0)
                               (edge { edgeConditions = [EdgeCondition { edgeActivation = condT
                                                                       , edgePhis = phisT }]
                                     }) $
                               Map.insertWith mappend (thread,ifF,0)
                               (edge { edgeConditions = [EdgeCondition { edgeActivation = condF
                                                                       , edgePhis = phisF }]
                                     }) (edges s) }
    return (Nothing,act)
    else do
    nxt <- liftIO $ terminatorInstGetSuccessor br 0
    phis <- realizePhis thread srcBlk nxt edge
    modify $ \s -> s { edges = Map.insertWith mappend (thread,nxt,0)
                               (edge { edgeConditions = [EdgeCondition { edgeActivation = act
                                                                       , edgePhis = phis }]
                                     }) (edges s) }
    return (Nothing,act)
realizeInstruction thread blk sblk act (castDown -> Just sw) edge = do
  srcBlk <- liftIO $ instructionGetParent sw
  cond <- liftIO $ switchInstGetCondition sw
  defBlk <- liftIO $ switchInstGetDefaultDest sw
  trgs <- liftIO $ switchInstGetCases sw
  cond' <- realizeValue thread cond edge
  mkSwitch (valInt $ symbolicValue cond') trgs srcBlk defBlk []
  where
    mkSwitch _ [] srcBlk defBlk conds = do
      phis <- realizePhis thread srcBlk defBlk edge
      nact <- sequence [ not' c | c <- conds ] >>=
              \acts -> mkAnd (act:acts)
      modify $ \s -> s { edges = Map.insertWith mappend (thread,defBlk,0)
                                 (edge { edgeConditions = [EdgeCondition { edgeActivation = nact
                                                                         , edgePhis = phis }]
                                       }) (edges s) }
      return (Nothing,act)
    mkSwitch cond ((cint,blk):trgs) srcBlk defBlk conds = do
      APInt _ rval <- liftIO $ constantIntGetValue cint >>= peek
      phis <- realizePhis thread srcBlk blk edge
      constRVal <- embedConst (IntValueC rval)
      rcond <- act .&. (cond .==. constRVal)
      modify $ \s -> s { edges = Map.insertWith mappend (thread,blk,0)
                                 (edge { edgeConditions = [EdgeCondition { edgeActivation = rcond
                                                                         , edgePhis = phis }]
                                       }) (edges s) }
      mkSwitch cond trgs srcBlk defBlk (rcond:conds)
realizeInstruction thread blk sblk act (castDown -> Just (_::Ptr PHINode)) edge
  = return (Just edge,act)
realizeInstruction thread blk sblk act (castDown -> Just (ret::Ptr ReturnInst)) edge
  = case thread of
    Nothing -> return (Nothing,act)
    Just th -> do
      retVal <- liftIO (returnInstGetReturnValue ret) >>=
                \ret' -> realizeValue thread ret' edge
      modify $ \s -> s { termEvents = Map.insertWith (++) th [(act,Just retVal)] (termEvents s) }
      return (Nothing,act)
realizeInstruction thread blk sblk act instr@(castDown -> Just cmpxchg) edge = do
  ptr <- liftIO $ atomicCmpXchgInstGetPointerOperand cmpxchg
  cmp <- liftIO $ atomicCmpXchgInstGetCompareOperand cmpxchg
  new <- liftIO $ atomicCmpXchgInstGetNewValOperand  cmpxchg
  ptr' <- realizeValue thread ptr edge
  cmp' <- realizeValue thread cmp edge
  new' <- realizeValue thread new edge
  oldval <- memoryRead thread instr ptr' edge
  oldval' <- defineSym "atomic-read" oldval
  isEq <- eqComposite (symbolicValue oldval') (symbolicValue cmp')
  isEq' <- define "atomic-cmp" isEq
  nval <- symITE isEq' (symbolicValue new') (symbolicValue oldval')
  nedge <- memoryWrite thread instr act ptr'
           (InstructionValue { symbolicType = symbolicType oldval
                             , symbolicValue = nval
                             , alternative = Nothing }) edge
  let res = InstructionValue { symbolicType = TpVector [symbolicType oldval
                                                       ,TpBool]
                             , symbolicValue = ValVector
                                               [symbolicValue oldval'
                                               ,ValBool isEq']
                             , alternative = Nothing }
  modify $ \s -> s { instructions = Map.insert (thread,instr) (act,res) (instructions s) }
  return (Just nedge { edgeValues = Map.insert (thread,instr) AlwaysDefined
                                    (edgeValues nedge) },act)
realizeInstruction thread blk sblk act instr@(castDown -> Just atomic) edge = do
  name <- liftIO $ getNameString atomic
  op <- liftIO $ atomicRMWInstGetOperation atomic
  ptr <- liftIO $ atomicRMWInstGetPointerOperand atomic
  val <- liftIO $ atomicRMWInstGetValOperand atomic
  ptr' <- realizeValue thread ptr edge
  val' <- realizeValue thread val edge
  oldval <- memoryRead thread instr ptr' edge
  oldval' <- defineSym name oldval
  newval <- case op of
    RMWXchg -> return val'
    RMWAdd -> do
      res <- (valInt $ symbolicValue oldval') .+. (valInt $ symbolicValue val')
      return InstructionValue { symbolicType = TpInt
                              , symbolicValue = ValInt res
                              , alternative = Nothing }
    RMWSub -> do
      res <- (valInt $ symbolicValue oldval') .-. (valInt $ symbolicValue val')
      return InstructionValue { symbolicType = TpInt
                              , symbolicValue = ValInt res
                              , alternative = Nothing }
  nedge <- memoryWrite thread instr act ptr' newval edge
  modify $ \s -> s { instructions = Map.insert (thread,instr) (act,oldval') (instructions s) }
  return (Just nedge { edgeValues = Map.insert (thread,instr) AlwaysDefined
                                    (edgeValues nedge) },act)
realizeInstruction thread blk sblk act (castDown -> Just (_::Ptr UnreachableInst)) edge
  = return (Nothing,act)
realizeInstruction thread blk sblk act instr edge = do
  name <- liftIO $ getNameString instr
  val <- realizeDefInstruction thread instr edge
  val' <- defineSym name val
  modify $ \s -> s { instructions = Map.insert (thread,instr)
                                    (act,val') (instructions s) }
  return (Just edge { edgeValues = Map.insert (thread,instr) AlwaysDefined
                                   (edgeValues edge) },act)

realizePhis :: Maybe (Ptr CallInst)
            -> Ptr BasicBlock
            -> Ptr BasicBlock
            -> Edge ProgramInput ProgramState
            -> LLVMRealization (Map (Maybe (Ptr CallInst),Ptr Instruction)
                                (InstructionValue ProgramInput ProgramState))
realizePhis thread src trg edge = do
  phis <- liftIO $ allPhis src trg
  foldlM (\mp (val,phi) -> do
             val' <- realizeValue thread val edge
             return (Map.insert (thread,castUp phi) val' mp)
         ) Map.empty phis

realizeDefInstruction :: Maybe (Ptr CallInst)
                      -> Ptr Instruction
                      -> Edge ProgramInput ProgramState
                      -> LLVMRealization (InstructionValue ProgramInput ProgramState)
realizeDefInstruction thread (castDown -> Just opInst) edge = do
  lhs <- liftIO $ getOperand opInst 0
  rhs <- liftIO $ getOperand opInst 1
  op <- liftIO $ binOpGetOpCode opInst
  valL <- realizeValue thread lhs edge
  valR <- realizeValue thread rhs edge
  let (tp,res) = case op of
        Add -> binInstr valL valR (.+.) bvadd
        Sub -> binInstr valL valR (.-.) bvsub
        Mul -> binInstr valL valR (.*.) bvmul
        LLVM.And -> case symbolicType valL of
          TpBool -> (TpBool,let ValBool v1 = symbolicValue valL
                                ValBool v2 = symbolicValue valR
                            in fmap ValBool (v1 .&. v2))
          TpInt -> case alternative valR of
            Just (IntConst 1) -> (TpInt,let ValInt v1 = symbolicValue valL
                                        in fmap ValInt (mod' v1 (cint 2)))
        LLVM.Or -> (TpBool,let ValBool v1 = symbolicValue valL
                               ValBool v2 = symbolicValue valR
                           in fmap ValBool (v1 .|. v2))
        Xor -> (TpBool,let ValBool v1 = symbolicValue valL
                           ValBool v2 = symbolicValue valR
                       in fmap ValBool (xor' [v1,v2]))
        SRem -> binInstr valL valR rem' bvsrem
        URem -> binInstr valL valR rem' bvurem
        Shl -> case alternative valR of
                 Nothing -> error "Left shift with non-constant not supported."
                 Just (IntConst vr)
                   -> (TpInt,let ValInt vl = symbolicValue valL
                             in do
                               c <- embedConst $ IntValueC $ 2^vr
                               e <- vl .*. c
                               return $ ValInt e)
        SDiv -> (TpInt,let ValInt v1 = symbolicValue valL
                           ValInt v2 = symbolicValue valR
                       in fmap ValInt (div' v1 v2))
        _ -> error $ "Unknown operator: "++show op
  rval <- res
  return InstructionValue { symbolicType = tp
                          , symbolicValue = rval
                          , alternative = Nothing
                          }
  where
    binInstr :: (Embed m (RExpr inp st),GetType (RExpr inp st))
             => InstructionValue inp st -> InstructionValue inp st
             -> (RExpr inp st IntType -> RExpr inp st IntType -> m (RExpr inp st IntType))
             -> (forall bw. RExpr inp st (BitVecType bw) -> RExpr inp st (BitVecType bw)
                 -> m (RExpr inp st (BitVecType bw)))
             -> (SymType,m (SymVal (RExpr inp st)))
    binInstr x y = bin (symbolicValue x) (symbolicValue y)
    
    bin :: (Embed m e,GetType e) => SymVal e -> SymVal e
        -> (e IntType -> e IntType -> m (e IntType))
        -> (forall bw. e (BitVecType bw) -> e (BitVecType bw) -> m (e (BitVecType bw)))
        -> (SymType,m (SymVal e))
    bin (ValBounded x) (ValBounded y) _ f = case (getType x,getType y) of
      (BitVecRepr bwX,BitVecRepr bwY) -> case geq bwX bwY of
        Just Refl -> (TpBounded bwX,fmap ValBounded $ f x y)
    bin (ValInt x) (ValInt y) f _ = (TpInt,fmap ValInt $ f x y)
realizeDefInstruction thread i@(castDown -> Just call) edge = do
  opts <- ask
  fname <- liftIO $ getFunctionName call
  case fname of
   '_':'_':'n':'o':'n':'d':'e':'t':_ -> do
     Singleton tp <- liftIO $ LLVM.getType i >>= translateType0 opts
     val <- createComposite (\_ rev -> do
                                let thRev = Nondet i rev
                                    pRev = case thread of
                                      Nothing -> MainInput thRev
                                      Just th' -> ThreadInput' th' thRev
                                return $ RInput pRev
                            ) tp
     modify $ \s -> s { inputAnnotation = updateThreadInputDesc thread
                                          (\ti -> ti { nondetTypes = Map.insert i tp
                                                                     (nondetTypes ti) })
                                          (inputAnnotation s) }
     return InstructionValue { symbolicType = tp
                             , symbolicValue = val
                             , alternative = Nothing }
   "malloc" -> do
     allocs <- gets $ allocations . programInfo
     mem <- gets $ memoryDesc . stateAnnotation
     case Map.lookup i allocs of
       Just info -> do
         tp <- case Map.lookup (Left i) mem of
           Just (TpStatic _ tp') -> return tp'
           Just (TpDynamic tp') -> return tp'
         cond <- constant True
         return InstructionValue { symbolicType = TpPtr (Map.singleton ptrLoc ()) tp
                                 , symbolicValue = ValPtr (Map.singleton ptrLoc (cond,[])) tp
                                 , alternative = Nothing }
   "calloc" -> do
     allocs <- gets $ allocations . programInfo
     mem <- gets $ memoryDesc . stateAnnotation
     case Map.lookup i allocs of
       Just info -> do
         tp <- case Map.lookup (Left i) mem of
           Just (TpStatic _ tp') -> return tp'
           Just (TpDynamic tp') -> return tp'
         cond <- constant True
         i0 <- 0
         return InstructionValue { symbolicType = TpPtr (Map.singleton ptrLocDyn ()) tp
                                 , symbolicValue = ValPtr (Map.singleton ptrLocDyn (cond,[i0])) tp
                                 , alternative = Nothing }
   "__act" -> do
     acts <- liftIO $ parseActArgs call
     mainTh <- gets $ mainThread . programInfo
     ths <- gets $ threads . programInfo
     res <- case [ RState rev
                 | (fun,is) <- acts
                 , (thId,thread') <- (Nothing,mainTh):
                                     [ (Just thId,th)
                                     | (thId,th) <- Map.toList ths ]
                 , threadFunction thread'==fun
                 , thId/=thread
                 , i <- is
                 , (blk,sblk) <- case Map.lookup i (threadSliceMapping thread') of
                   Nothing -> []
                   Just blks -> blks
                 , let rev = case thId of
                         Nothing -> MainState (LatchBlock blk sblk)
                         Just th' -> ThreadState' th' (LatchBlock blk sblk)
                 ] of
            [] -> constant True
            xs -> mkOr xs
     return InstructionValue { symbolicType = TpBool
                             , symbolicValue = ValBool res
                             , alternative = Nothing
                             }
   "pthread_mutex_locked" -> do
     ptr <- liftIO $ getOperand call 0
     ptr' <- realizeValue thread ptr edge
     memoryRead thread i ptr' edge
   _ -> error $ "Unknown function call: "++fname
  where
    ptrLoc = MemoryPtr { memoryLoc = AllocTrg i
                       , offsetPattern = [StaticAccess 0] }
    ptrLocDyn = MemoryPtr { memoryLoc = AllocTrg i
                          , offsetPattern = [DynamicAccess] }
    parseActArgs :: Ptr CallInst -> IO [(Ptr LLVM.Function,[Integer])]
    parseActArgs call = do
      nargs <- callInstGetNumArgOperands call
      parseActArgsFun call 0 nargs
    parseActArgsFun :: Ptr CallInst -> Integer -> Integer -> IO [(Ptr LLVM.Function,[Integer])]
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
    parseActArgsNums :: Ptr CallInst -> Integer -> Integer
                     -> IO ([Integer],[(Ptr LLVM.Function,[Integer])])
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
realizeDefInstruction thread i@(castDown -> Just icmp) edge = do
  op <- liftIO $ getICmpOp icmp
  lhs <- liftIO $ getOperand icmp 0
  rhs <- liftIO $ getOperand icmp 1
  lhsV <- realizeValue thread lhs edge
  rhsV <- realizeValue thread rhs edge
  cmpRes <- cmp op lhsV rhsV
  return InstructionValue { symbolicType = TpBool
                          , symbolicValue = ValBool cmpRes
                          , alternative = Nothing }
  where
    cmp I_EQ (alternative -> Just (OrList xs)) (alternative -> Just (IntConst 0))
      = sequence [ (valInt x) .==. (cint 0) | x <- xs ] >>= mkAnd
    cmp I_EQ (alternative -> Just (IntConst 0)) (alternative -> Just (OrList xs))
      = sequence [ (valInt x) .==. (cint 0) | x <- xs ] >>= mkAnd
    cmp I_EQ x@(symbolicType -> TpBool) y@(symbolicType -> TpBool)
      = (valBool (symbolicValue x)) .==. (valBool (symbolicValue y))
    cmp I_EQ x@(symbolicType -> TpPtr locx _) y@(symbolicType -> TpPtr locy _)
      = sequence (Map.elems $ Map.intersectionWith
                  (\(c1,i1) (c2,i2) -> do
                      nc <- c1 .==. c2
                      ncs <- sequence [ j1 .==. j2 | (j1,j2) <- zip i1 i2 ]
                      mkAnd (nc:ncs))
                  (valPtr $ symbolicValue x)
                  (valPtr $ symbolicValue y)) >>= mkOr
    cmp I_EQ (alternative -> Just NullPtr) y@(symbolicType -> TpInt)
      = (valInt (symbolicValue y)) .==. (cint 0)
    cmp I_EQ x@(symbolicType -> TpInt) (alternative -> Just NullPtr)
      = (valInt (symbolicValue x)) .==. (cint 0)
    cmp I_EQ (symbolicValue -> x) (symbolicValue -> y)
      = bin x y (.==.) (.==.)
    cmp I_NE x y = do
      res <- cmp I_EQ x y
      not' res
    cmp I_SGE x y = bin (symbolicValue x) (symbolicValue y) (.>=.) bvsge
    cmp I_UGE x y = bin (symbolicValue x) (symbolicValue y) (.>=.) bvuge
    cmp I_SGT x y = bin (symbolicValue x) (symbolicValue y) (.>.) bvsgt
    cmp I_UGT x y = bin (symbolicValue x) (symbolicValue y) (.>.) bvugt
    cmp I_SLE x y = bin (symbolicValue x) (symbolicValue y) (.<=.) bvsle
    cmp I_ULE x y = bin (symbolicValue x) (symbolicValue y) (.<=.) bvule
    cmp I_SLT x y = bin (symbolicValue x) (symbolicValue y) (.<.) bvslt
    cmp I_ULT x y = bin (symbolicValue x) (symbolicValue y) (.<.) bvult
    cmp op x y = error $ "Cannot compare "++show (symbolicType x)++" and "++show (symbolicType y)++" using "++show op

    bin :: GetType e => SymVal e -> SymVal e
        -> (e IntType -> e IntType -> a)
        -> (forall bw. e (BitVecType bw) -> e (BitVecType bw) -> a)
        -> a
    bin (ValInt x) (ValInt y) f _ = f x y
    bin (ValBounded x) (ValBounded y) _ f = case (getType x,getType y) of
      (BitVecRepr bwX,BitVecRepr bwY) -> case geq bwX bwY of
        Just Refl -> f x y
realizeDefInstruction thread i@(castDown -> Just (zext::Ptr ZExtInst)) edge = do
  opts <- ask
  op <- liftIO $ getOperand zext 0
  tp <- liftIO $ valueGetType op >>= translateType0 opts
  fop <- realizeValue thread op edge
  if tp==Singleton TpBool
    then do
    rval <- ite (valBool $ symbolicValue fop) (cint 1) (cint 0)
    return InstructionValue { symbolicType = TpInt
                            , symbolicValue = ValInt rval
                            , alternative = Just $ ExtBool (valBool $ symbolicValue fop)
                            }
    else return fop
realizeDefInstruction thread i@(castDown -> Just select) edge = do
  cond <- liftIO $ selectInstGetCondition select
  cond' <- realizeValue thread cond edge
  tVal <- liftIO $ selectInstGetTrueValue select
  tVal' <- realizeValue thread tVal edge
  fVal <- liftIO $ selectInstGetFalseValue select
  fVal' <- realizeValue thread fVal edge
  res <- symITE (valBool $ symbolicValue cond')
         (symbolicValue tVal')
         (symbolicValue fVal')
  return InstructionValue { symbolicType = case typeUnion (symbolicType tVal')
                                                (symbolicType fVal') of
                              Just ntp -> ntp
                          , symbolicValue = res
                          , alternative = Nothing }
realizeDefInstruction thread i@(castDown -> Just (phi::Ptr PHINode)) edge
  = getInstructionValue thread i edge
realizeDefInstruction thread i@(castDown -> Just (_::Ptr AllocaInst)) edge = do
  memDesc <- gets $ memoryDesc . stateAnnotation
  tp <- case Map.lookup (Left i) memDesc of
    Just (TpStatic _ tp') -> return tp'
    Just (TpDynamic tp') -> return tp'
  cond <- constant True
  return InstructionValue { symbolicType = TpPtr (Map.singleton ptrLoc ()) tp
                          , symbolicValue = ValPtr (Map.singleton ptrLoc (cond,[])) tp
                          , alternative = Nothing }
  where
    ptrLoc = MemoryPtr { memoryLoc = AllocTrg i
                       , offsetPattern = [StaticAccess 0] }
realizeDefInstruction thread i@(castDown -> Just (trunc::Ptr TruncInst)) edge = do
  val <- liftIO $ getOperand trunc 0
  rval <- realizeValue thread val edge
  tp <- liftIO $ LLVM.getType trunc
  let tp' = case castDown tp of
        Just t -> t
  bw <- liftIO $ getBitWidth tp'
  if bw==1
    then case alternative rval of
    Just (ExtBool c) -> return InstructionValue { symbolicType = TpBool
                                                , symbolicValue = ValBool c
                                                , alternative = Nothing
                                                }
    _ -> do
      res <- (valInt $ symbolicValue rval) .==. (cint 1)
      return InstructionValue { symbolicType = TpBool
                              , symbolicValue = ValBool res
                              , alternative = Nothing }
    else return rval
realizeDefInstruction thread (castDown -> Just gep) edge = do
  ptr <- liftIO $ getElementPtrInstGetPointerOperand gep
  ptr' <- realizeValue thread ptr edge
  num <- liftIO $ getNumOperands gep
  args <- liftIO $ mapM (getOperand gep) [1..num-1]
  args' <- mapM (\arg -> realizeValue thread arg edge) args
  let rpat = fmap (\val -> case alternative val of
                    Just (IntConst n) -> Just n
                    _ -> Nothing
                  ) args'
      ridx = fmap (\val -> case alternative val of
                    Just (IntConst n) -> Left n
                    Nothing -> case symbolicValue val of
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
  name <- liftIO $ getNameString gep
  --putStrLn $ "GEP@"++name++": "++show (symbolicType ptr')++" ~> "++show res_tp
  nptr <- case symbolicValue ptr' of
    ValPtr trgs _ -> derefPointer ridx trgs
  return InstructionValue { symbolicType = res_tp
                          , symbolicValue = ValPtr nptr ntp
                          , alternative = Nothing }
realizeDefInstruction thread instr@(castDown -> Just load) edge = do
  name <- liftIO $ getNameString load
  ptr <- liftIO $ loadInstGetPointerOperand load
  ptr' <- realizeValue thread ptr edge
  memoryRead thread instr ptr' edge
realizeDefInstruction thread (castDown -> Just bitcast) edge = do
  -- Ignore bitcasts for now, just assume that everything will work out
  arg <- liftIO $ getOperand (bitcast :: Ptr BitCastInst) 0
  realizeValue thread arg edge
realizeDefInstruction thread (castDown -> Just sext) edge = do
  -- Again, ignore sign extensions
  arg <- liftIO $ getOperand (sext :: Ptr SExtInst) 0
  realizeValue thread arg edge
realizeDefInstruction thread (castDown -> Just extr) edge = do
  begin <- liftIO $ extractValueInstIdxBegin extr
  len <- liftIO $ extractValueInstGetNumIndices extr
  idx <- liftIO $ peekArray (fromIntegral len) begin
  arg <- liftIO $ getOperand extr 0
  arg' <- realizeValue thread arg edge
  return InstructionValue { symbolicType = indexType (symbolicType arg') idx
                          , symbolicValue = indexValue (symbolicValue arg') idx
                          , alternative = Nothing }
  where
    indexType :: Integral a => SymType -> [a] -> SymType
    indexType tp [] = tp
    indexType (TpVector tps) (i:is) = indexType (tps `genericIndex` i) is

    indexValue :: Integral a => LLVMVal -> [a] -> LLVMVal
    indexValue val [] = val
    indexValue (ValVector vals) (i:is) = indexValue (vals `genericIndex` i) is
realizeDefInstruction thread (castDown -> Just (i2p::Ptr IntToPtrInst)) edge = do
  val <- liftIO $ getOperand i2p 0
  realizeValue thread val edge
realizeDefInstruction thread (castDown -> Just (p2i::Ptr PtrToIntInst)) edge = do
  val <- liftIO $ getOperand p2i 0
  realizeValue thread val edge
realizeDefInstruction _ i _ = do
  str <- liftIO $ valueToString i
  error $ "Unknown instruction: "++str

memoryRead :: Maybe (Ptr CallInst)
           -> Ptr Instruction
           -> InstructionValue ProgramInput ProgramState
           -> Edge ProgramInput ProgramState
           -> LLVMRealization (InstructionValue ProgramInput ProgramState)
memoryRead th origin (InstructionValue { symbolicType = TpPtr locs (Singleton tp)
                                       , symbolicValue = ValPtr trgs _
                                       }) edge = do
  startVals <- mapM (\(trg,(cond,dyn)) -> do
                        let idx = idxList (offsetPattern trg) dyn
                        val <- mkMemoryRef th (memoryLoc trg)
                        (res,_,_) <- accessAllocTypedIgnoreErrors tp
                                     (\val' _ -> return (val',())) idx val ()
                        return (res,cond)
                    ) (Map.toList trgs)
  startVal <- case startVals of
    [] -> defaultValue tp
    _ -> symITEs startVals
  allEvents <- gets $ (\evs -> Map.intersection evs (observedEvents edge)) . events
  val <- foldlM (\cval ev -> case ev of
                  WriteEvent trg cont th' writeOrigin -> do
                    allConds <- sequence [ do
                                             match <- patternMatch
                                                      (offsetPattern ptr1)
                                                      (offsetPattern ptr2)
                                                      idx1 idx2
                                             case match of
                                               Nothing -> return Nothing
                                               Just match' -> fmap Just $
                                                              mkAnd (cond1:cond2:match')
                                         | (ptr1,(cond1,idx1)) <- Map.toList trgs
                                         , (ptr2,info2) <- Map.toList trg
                                         , memoryLoc ptr1 == memoryLoc ptr2
                                         , let (cond2,idx2) = info2 ]
                    case catMaybes allConds of
                      [] -> return cval
                      [cond] -> mkVal cond
                      conds -> mkOr conds >>= mkVal
                      where
                        mkVal c = if symbolicType cont==tp
                                  then symITE c (symbolicValue cont) cval
                                  else return cval {-error $ "While realizing read to "++
                                                 (unsafePerformIO $ getNameString origin)++
                                                 " from "++show trgs++
                                                 ": Write at "++
                                                 (unsafePerformIO $ valueToString writeOrigin)++
                                                 " to "++show (fmap (\x -> x inp) trg)++
                                                 " has wrong type "++
                                                 (show $ (symbolicType cont))++
                                                 " (Expected: "++show tp++")."-}
                ) startVal allEvents
  return InstructionValue { symbolicType = tp
                          , symbolicValue = val
                          , alternative = Nothing
                          }
memoryRead _ origin val _ = unsafePerformIO $ do
  str <- valueToString origin
  error $ "memoryRead: Cannot read from "++str++" (Type: "++show (symbolicType val)++")"

memoryWrite :: Maybe (Ptr CallInst)
            -> Ptr Instruction
            -> LLVMExpr BoolType
            -> InstructionValue ProgramInput ProgramState
            -> InstructionValue ProgramInput ProgramState
            -> Edge ProgramInput ProgramState
            -> LLVMRealization (Edge ProgramInput ProgramState)
memoryWrite th origin act ptr val edge = do
  ntarget <- sequence $ Map.mapWithKey
             (\loc _ -> do
                 (cond,idx) <- case Map.lookup loc (valPtr $ symbolicValue ptr) of
                       Just r -> return r
                       Nothing -> do
                         c <- constant False
                         i <- sequence [ 0 | DynamicAccess <- offsetPattern loc ]
                         return (c,i)
                 ncond <- act .&. cond
                 return (ncond,idx)) (tpPtr $ symbolicType ptr)
  addEvent (WriteEvent { target = ntarget
                       , writeContent = val
                       , eventThread = th
                       , eventOrigin = origin }) edge

getInstructionValue :: Maybe (Ptr CallInst) -> Ptr Instruction
                    -> Edge ProgramInput ProgramState
                    -> LLVMRealization
                       (InstructionValue ProgramInput ProgramState)
getInstructionValue thread instr edge = do
  instrs <- gets instructions
  case Map.lookup (thread,instr) (edgeValues edge) of
    Just AlwaysDefined -> case Map.lookup (thread,instr) instrs of
      Just (_,val) -> return val
    Just SometimesDefined -> case Map.lookup (thread,instr) instrs of
      Just (act,val) -> do
        latchVal <- mkLatchInstr thread instr
        rval <- symITE act (symbolicValue val) latchVal
        return InstructionValue { symbolicType = symbolicType val
                                , symbolicValue = rval
                                , alternative = Nothing
                                }
    _ -> do
      latchVal <- mkLatchInstr thread instr
      return InstructionValue { symbolicType = symType latchVal
                              , symbolicValue = latchVal
                              , alternative = Nothing
                              }

structToVector :: Struct SymType -> SymType
structToVector (Singleton tp) = tp
structToVector (Struct tps) = TpVector (fmap structToVector tps)

realizeValue :: Maybe (Ptr CallInst) -> Ptr LLVM.Value
             -> Edge ProgramInput ProgramState
             -> LLVMRealization
                (InstructionValue ProgramInput ProgramState)
realizeValue thread (castDown -> Just instr) edge
  = getInstructionValue thread instr edge
realizeValue thread (castDown -> Just i) edge = do
  tp <- liftIO $ LLVM.getType i
  bw <- liftIO $ getBitWidth tp
  v <- liftIO $ constantIntGetValue i
  rv <- liftIO $ apIntGetSExtValue v
  if bw==1
    then do
    val <- embedConst $ BoolValueC $ rv/=0
    return InstructionValue { symbolicType = TpBool
                            , symbolicValue = ValBool val
                            , alternative = Just (IntConst $ fromIntegral rv) }
    else do
    useBW <- asks bitPrecise
    if useBW
      then reifyNat (fromIntegral bw) $
           \bw' -> do
             val <- embedConst $ BitVecValueC (fromIntegral rv) bw'
             return InstructionValue { symbolicType = TpBounded bw'
                                     , symbolicValue = ValBounded val
                                     , alternative = Just (IntConst $ fromIntegral rv)
                                     }
      else do
        val <- embedConst $ IntValueC $ fromIntegral rv
        return InstructionValue { symbolicType = TpInt
                                , symbolicValue = ValInt val
                                , alternative = Just (IntConst $ fromIntegral rv)
                                }
realizeValue thread (castDown -> Just (null::Ptr ConstantPointerNull)) edge = do
  opts <- ask
  nullTp <- liftIO $ LLVM.getType null >>=
            sequentialTypeGetElementType >>=
            translateType0 opts
  return InstructionValue { symbolicType = TpPtr { tpPtr = Map.empty
                                                 , tpPtrType = nullTp }
                          , symbolicValue = ValPtr { valPtr = Map.empty
                                                   , valPtrType = nullTp }
                          , alternative = Just NullPtr
                          }
realizeValue thread (castDown -> Just undef) edge = do
  tp <- liftIO $ LLVM.getType (undef::Ptr UndefValue)
  defaultSymValue tp
realizeValue thread (castDown -> Just glob) edge = do
  isLocal <- liftIO $ globalVariableIsThreadLocal glob
  let ptr = MemoryPtr { memoryLoc = if isLocal then LocalTrg glob else GlobalTrg glob
                      , offsetPattern = [] }
  tp <- if isLocal
        then do
          locals <- gets $ threadGlobalDesc . getThreadStateDesc thread . stateAnnotation
          return $ case Map.lookup glob locals of
            Just (TpStatic _ t) -> t
            Just (TpDynamic t) -> t
        else do
          globs <- gets $ memoryDesc . stateAnnotation
          return $ case Map.lookup (Right glob) globs of
            Just (TpStatic _ t) -> t
            Just (TpDynamic t) -> t
  cond <- constant True
  return InstructionValue { symbolicType = TpPtr (Map.singleton ptr ()) tp
                          , symbolicValue = ValPtr (Map.singleton ptr (cond,[])) tp
                          , alternative = Nothing
                          }
realizeValue thread (castDown -> Just cexpr) edge = do
  instr <- liftIO $ constantExprAsInstruction (cexpr::Ptr ConstantExpr)
  realizeDefInstruction thread instr edge
realizeValue thread (castDown -> Just arg) edge = do
  val <- mkThreadArgument thread arg
  return InstructionValue { symbolicType = symType val
                          , symbolicValue = val
                          , alternative = Nothing }
realizeValue thread val edge = do
  str <- liftIO $ valueToString val
  error $ "Cannot realize value: "++str

defaultSymValue :: Ptr LLVM.Type
                -> LLVMRealization (InstructionValue ProgramInput ProgramState)
defaultSymValue (castDown -> Just itp) = do
  bw <- liftIO $ getBitWidth itp
  if bw==1
    then do
    val <- constant False
    return InstructionValue { symbolicType = TpBool
                            , symbolicValue = ValBool val
                            , alternative = Just (IntConst 0) }
    else do
    val <- 0
    return InstructionValue { symbolicType = TpInt
                            , symbolicValue = ValInt val
                            , alternative = Just (IntConst 0) }
defaultSymValue (castDown -> Just (ptp::Ptr PointerType)) = do
  opts <- ask
  rtp <- liftIO $ sequentialTypeGetElementType ptp
         >>= translateType0 opts
  return InstructionValue { symbolicType = TpPtr Map.empty rtp
                          , symbolicValue = ValPtr Map.empty rtp
                          , alternative = Just NullPtr
                          }
{-
translateType :: Map (Ptr CallInst) a -> Map MemoryTrg AllocType -> Ptr Type -> IO (Struct SymType)
translateType _ _ (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return $ Singleton TpBool
    _ -> return $ Singleton TpInt
translateType threads tps (castDown -> Just ptp) = do
  subType <- sequentialTypeGetElementType (ptp::Ptr PointerType) >>= translateType threads tps
  return $ Singleton $ TpPtr (allPtrsOfType subType tps) subType
translateType threads tps (castDown -> Just struct) = do
  hasName <- structTypeHasName struct
  name <- if hasName
          then fmap Just (structTypeGetName struct >>= stringRefData)
          else return Nothing
  case name of
   Just "struct.__thread_id" -> return $ Singleton $ TpThreadId (fmap (const ()) threads)
   Just "struct.pthread_mutex_t" -> return $ Singleton TpBool
   Just "struct.pthread_rwlock_t" -> return $ Singleton $ TpVector [TpBool,TpInt]
   Just "struct.pthread_cond_t"
     -> return $ Singleton $ TpCondition $
        Map.fromList $ (Nothing,()):[ (Just t,()) | t <- Map.keys threads ]
   _ -> do
     num <- structTypeGetNumElements struct
     els <- mapM (\i -> structTypeGetElementType struct i
                        >>= translateType threads tps
                 ) [0..num-1]
     return $ Struct els
translateType threads tps (castDown -> Just arr) = do
  subt <- sequentialTypeGetElementType arr >>= translateType threads tps
  num <- arrayTypeGetNumElements arr
  return $ Struct $ genericReplicate num subt
translateType _ _ tp = do
  typeDump tp
  error "Can't translate type"
-}

translateAllocType0 :: TranslationOptions -> AllocKind -> IO (Struct SymType)
translateAllocType0 opts (NormalAlloc tp) = translateType0 opts tp
translateAllocType0 opts (ThreadIdAlloc thr)
  = return (Singleton $ TpThreadId (Map.fromList [ (th,()) | th <- thr ]))

translateType0 :: TranslationOptions -> Ptr LLVM.Type -> IO (Struct SymType)
translateType0 opts (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return $ Singleton TpBool
    _ -> if bitPrecise opts
         then reifyNat (fromIntegral bw) $
              \bw' -> return $ Singleton $ TpBounded bw'
         else return $ Singleton TpInt
translateType0 opts (castDown -> Just ptr) = do
  subType <- sequentialTypeGetElementType (ptr::Ptr PointerType) >>= translateType0 opts
  return $ Singleton $ TpPtr Map.empty subType
translateType0 opts (castDown -> Just struct) = do
  hasName <- structTypeHasName struct
  name <- if hasName
          then fmap Just $ structTypeGetName struct >>= stringRefData
          else return Nothing
  case name of
   Just "struct.__thread_id" -> return $ Singleton $ TpThreadId Map.empty
   Just "struct.pthread_mutex_t" -> return $ Singleton TpBool
   Just "struct.pthread_rwlock_t" -> return $ Singleton $
                                     TpVector [TpBool,TpInt]
   Just "struct.pthread_cond_t" -> return $ Singleton $ TpCondition Map.empty
   _ -> do
     num <- structTypeGetNumElements struct
     tps <- mapM (\i -> structTypeGetElementType struct i >>= translateType0 opts) [0..num-1]
     return $ Struct tps
translateType0 opts (castDown -> Just arr) = do
  subt <- sequentialTypeGetElementType arr >>= translateType0 opts
  num <- arrayTypeGetNumElements arr
  return $ Struct $ genericReplicate num subt
translateType0 _ tp = do
  typeDump tp
  error "Cannot translate type"

instance Monoid (Edge inp st) where
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
      combine _ SometimesDefined _ = Just SometimesDefined
      combine _ _ SometimesDefined = Just SometimesDefined
      combine _ AlwaysDefined AlwaysDefined = Just AlwaysDefined
      only = fmap (\ev -> case ev of
                    AlwaysDefined -> SometimesDefined
                    _ -> ev)

realizeBlock :: Maybe (Ptr CallInst) -> Ptr BasicBlock -> Int
             -> ProgramInfo
             -> LLVMRealization ()
realizeBlock thread blk sblk info = do
  edge <- gets $ \s -> case Map.lookup (thread,blk,sblk) (edges s) of
    Nothing -> mempty
    Just e -> e
  name <- liftIO $ subBlockName blk sblk
  instrs <- liftIO $ getSubBlockInstructions blk sblk
  dontStep <- gets $ Map.null . threadStateDesc . stateAnnotation
  let latchCond = case thread of
        Nothing -> RState $ MainState $ LatchBlock blk sblk
        Just th -> RState $ ThreadState' th $ LatchBlock blk sblk
      allConds = (if isEntryBlock
                  then [latchCond]
                  else [])++
                 [ edgeActivation cond | cond <- edgeConditions edge ]
  act <- mkOr allConds >>= define name
  edgePhi <- sequence $ foldl
             (\cmp cond
              -> Map.unionWith
                 (\v1 v2 -> do
                     rv1 <- v1
                     rv2 <- v2
                     nval <- symITE (edgeActivation cond)
                             (symbolicValue rv1)
                             (symbolicValue rv2)
                     return $ InstructionValue { symbolicType = case typeUnion (symbolicType rv1) (symbolicType rv2) of
                                                   Just rtp -> rtp
                                                   Nothing -> trace ("Warning: Type error in phi, cannot union "++show (symbolicType rv1)++" and "++show (symbolicType rv2)) (symbolicType rv1)
                                               , symbolicValue = nval
                                               , alternative = Nothing }
                 ) (fmap return $ edgePhis cond) cmp
             ) Map.empty (edgeConditions edge)
  defCond <- if isEntryBlock
             then mkOr [ edgeActivation cond
                       | cond <- edgeConditions edge ]
             else return act
  edgePhiGates <- sequence $ Map.mapWithKey
                  (\(_,instr) val -> do
                      iname <- liftIO $ getNameString instr
                      rval <- defineSym iname val
                      return (act,rval)
                  ) edgePhi
  modify $ \s -> s { instructions = Map.union (instructions s) edgePhiGates }
  phiDefs <- mapM (\_ -> if isEntryBlock
                         then return SometimesDefined
                         else return AlwaysDefined
                  ) edgePhiGates
  let edge1 = edge { edgeValues = Map.union phiDefs
                                  (if isEntryBlock
                                   then fmap (\def -> case def of
                                               AlwaysDefined -> SometimesDefined
                                               _ -> def) (edgeValues edge)
                                   else edgeValues edge)
                   }
  modify $ \s -> s { edges = Map.delete (thread,blk,sblk) (edges s) }
  realizeInstructions thread blk sblk act instrs edge1
  where
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
         Just (fun::Ptr LLVM.Function) -> do
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

allPhis :: Ptr BasicBlock -> Ptr BasicBlock -> IO [(Ptr LLVM.Value,Ptr PHINode)]
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

allPhiNodes :: Ptr BasicBlock -> IO [Ptr PHINode]
allPhiNodes trg = do
  instrs <- getInstList trg
  it <- ipListBegin instrs
  allPhis' it
  where
    allPhis' it = do
      instr <- iListIteratorDeref it
      case castDown instr of
       Nothing -> return []
       Just phi -> do
         nxt_it <- iListIteratorNext it
         xs <- allPhis' nxt_it
         return (phi:xs)

{-outputValues :: LLVMRealization (Map (Maybe (Ptr CallInst),Ptr Instruction)
                                 (SymType,LLVMVal))
outputValues = do
  st <- get
  phis <- foldlM (\mp cond -> 
  where
    dontStep = Map.null (threadStateDesc $ stateAnnotation real)
    mp1 = Map.foldlWithKey (\mp instr tp
                            -> Map.insert (Nothing,instr)
                               (tp,getExpr Nothing instr) mp
                           ) Map.empty
          (latchValueDesc $ mainStateDesc $ stateAnnotation real)
    mp2 = Map.foldlWithKey
          (\mp th thSt
           -> Map.foldlWithKey
              (\mp instr tp
                -> Map.insert (Just th,instr)
                   (tp,getExpr (Just th) instr) mp
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
          Nothing -> error $ "outputValues: Cannot find old value of "++show instr-}

computeRStep :: LLVMRealization (Map (Maybe (Ptr CallInst)) (LLVMExpr BoolType))
computeRStep = do
  st <- get
  case Map.keys $ threadStateDesc $ stateAnnotation st of
    [] -> do
      step <- true
      return $ Map.singleton Nothing step
    ths -> do
      let allThreads = Nothing:(fmap Just ths)
      fmap Map.fromList $
        sequence [ do
                     let thisStep = RInput $ case th of
                           Nothing -> MainInput Step
                           Just th' -> ThreadInput' th' Step
                         thisRunning = case th of
                           Nothing -> []
                           Just th' -> [RState $ ThreadActivation th']
                         otherSteps = [ RInput $ case th' of
                                          Nothing -> MainInput Step
                                          Just th'' -> ThreadInput' th'' Step
                                      | th' <- allThreads
                                      , th'/=th ]
                         thisIntYields = [ RState $ case th of
                                             Nothing -> MainState $ LatchBlock blk sblk
                                             Just th'' -> ThreadState' th'' $ LatchBlock blk sblk
                                         | (th',blk,sblk) <- Map.keys $ internalYieldEdges st
                                         , th'==th ]
                         otherIntYields = [ RState $ case th' of
                                              Nothing -> MainState $ LatchBlock blk sblk
                                              Just th'' -> ThreadState' th'' $ LatchBlock blk sblk
                                          | (th',blk,sblk) <- Map.keys $ internalYieldEdges st
                                          , th'/=th]
                     notOthers <- mapM (\x -> not' x) otherSteps
                     notOtherIntYield <- mapM (\x -> not' x) otherIntYields
                     canStep <- and' (thisStep:thisRunning++notOthers++notOtherIntYield)
                     mustStep <- or' (canStep:thisIntYields)
                     rstep' <- define ("rstep"++(if n==0 then "" else show n)) mustStep
                     return (th,rstep')
                 | (th,n) <- zip allThreads [0..] ]

computeTransitionRelation :: LLVMRealization LLVMTransRel
computeTransitionRelation = do
  rsteps <- computeRStep
  st <- get
  let th :: ThreadStateDesc -> Ptr BasicBlock -> LLVMRealization (ThreadState LLVMInit)
      th desc start = do
        blks <- sequence $ Map.mapWithKey
                (\(blk,sblk) _ -> fmap Init $
                                  constant (blk==start && sblk==0)
                ) (latchBlockDesc desc)
        vals <- mapM (\tp -> foldExprs (\_ -> fmap Init . embedConst) (defaultConst tp)
                     ) (latchValueDesc desc)
        arg <- case threadArgumentDesc desc of
          Nothing -> return Nothing
          Just (arg,tp) -> do
            v <- foldExprs (\_ -> fmap Init . embedConst) (defaultConst tp)
            return (Just (arg,v))
        lmem <- mapM (\el -> foldExprs (\_ e -> return $ Init e) el) $
                Map.intersection (memoryInit st) (threadGlobalDesc desc)
        ret <- case threadReturnDesc desc of
          Nothing -> return Nothing
          Just tp -> fmap Just $ foldExprs (\_ -> fmap Init . embedConst) (defaultConst tp)
        return ThreadState { latchBlocks = blks
                           , latchValues = vals
                           , threadArgument = arg
                           , threadGlobals = lmem
                           , threadReturn = ret
                           }
  mainInit <- th (mainStateDesc $ stateAnnotation st) (mainBlock st)
  thsInit <- sequence $ Map.mapWithKey
             (\thId thd -> do
                 let Just start = Map.lookup thId (threadBlocks st)
                 st <- th thd start
                 running <- constant False
                 return (Init running,st)
             ) (threadStateDesc $ stateAnnotation st)
  memInit <- sequence $ Map.mapWithKey
             (\loc tp -> case loc of
               Left alloc -> createComposite (\tp' _ -> return (NoInit tp')) tp
               Right glob -> case Map.lookup glob (memoryInit st) of
                 Nothing -> createComposite (\tp' _ -> return (NoInit tp')) tp
                 Just init -> foldExprs (\_ e -> return $ Init e) init)
             (memoryDesc $ stateAnnotation st)
  let nxtBlks :: Maybe (Ptr CallInst) -> ThreadStateDesc
              -> LLVMRealization (Map (Ptr BasicBlock,Int) (LLVMExpr BoolType))
      nxtBlks th desc = do
        let Just rstep = Map.lookup th rsteps
        sequence $ Map.mapWithKey
          (\(blk,sblk) _ -> do
              let e0 = Map.lookup (th,blk,sblk) (edges st)
                  e1 = Map.lookup (th,blk,sblk) (yieldEdges st)
                  e2 = Map.lookup (th,blk,sblk) (internalYieldEdges st)
                  re = mconcat [ e | Just e <- [e0,e1,e2] ]
                  old = RState $ case th of
                    Nothing -> MainState $ LatchBlock blk sblk
                    Just th' -> ThreadState' th' $ LatchBlock blk sblk
              act <- mkOr $ [ edgeActivation cond
                            | cond <- edgeConditions re ]
              ite rstep act old
          ) (latchBlockDesc desc)
      nxtValues th desc = do
        let Just rstep = Map.lookup th rsteps
        sequence $ Map.mapWithKey
          (\instr tp -> do
              old <- createComposite
                     (\_ rev -> let tRev = LatchValue instr rev
                                    pRev = case th of
                                      Nothing -> MainState tRev
                                      Just th' -> ThreadState' th' tRev
                                in return $ RState pRev
                     ) tp
              alwaysDefined <- if Map.null (yieldEdges st) &&
                                  Map.null (internalYieldEdges st)
                               then foldlM (\allEdgesDefine edge
                                            -> case Map.lookup (th,instr) (edgeValues edge) of
                                               Just AlwaysDefined -> return allEdgesDefine
                                               Just SometimesDefined -> return False
                                               _ -> return False
                                           ) True (edges st)
                               else return False
              let phis = [ (phiVal,edgeActivation cond)
                         | edge <- Map.elems (edges st)
                         , cond <- edgeConditions edge
                         , phiVal <- case Map.lookup (th,instr)
                                          (edgePhis cond) of
                             Just rval -> [symbolicValue rval]
                             Nothing -> [] ]
              case phis of
                [] -> case Map.lookup (th,instr) (instructions st) of
                  Just (act,val) -> if alwaysDefined
                                    then symITE rstep (symbolicValue val) old
                                    else do
                    cond <- rstep .&. act
                    symITE cond (symbolicValue val) old
                _ -> if alwaysDefined
                     then symITEs phis
                     else do
                  ctrue <- true
                  symITEs (phis++[(old,ctrue)])
          ) (latchValueDesc desc)
      nxtThread th desc = do
        let Just rstep = Map.lookup th rsteps
        blks <- nxtBlks th desc
        vals <- nxtValues th desc
        arg <- case th of
          Nothing -> return Nothing
          Just th' -> case threadArgumentDesc desc of
            Nothing -> return Nothing
            Just (arg,tp) -> do
              old <- createComposite (\_ rev -> return $ RState $ ThreadState' th' $
                                                ThreadArgument rev
                                     ) tp
              case Map.lookup th' (spawnEvents st) of
                Nothing -> return (Just (arg,old))
                Just terms -> do
                  lcond <- true
                  new <- sequence [ do
                                      let Just rstepOth = Map.lookup oth rsteps
                                      ract <- rstepOth .&. act
                                      return (symbolicValue ret,ract)
                                  | (oth,act,Just ret) <- terms ] >>=
                         \conds -> symITEs $ conds++[(old,lcond)]
                  return (Just (arg,new))
        ret <- case th of
          Nothing -> return Nothing
          Just th' -> case threadReturnDesc desc of
            Nothing -> return Nothing
            Just tp -> do
              old <- createComposite (\_ rev -> return $ RState $ ThreadState' th' $
                                                ThreadReturn rev
                                     ) tp
              case Map.lookup th' (termEvents st) of
                Nothing -> return (Just old)
                Just terms -> do
                  lcond <- constant True
                  new <- symITEs $ [ (symbolicValue ret,act)
                                   | (act,Just ret) <- terms ]++
                         [(old,lcond)]
                  new' <- symITE rstep new old 
                  return (Just new')
        glob <- sequence $ Map.mapWithKey
                (\g tp -> do
                    old <- createComposite (\_ rev -> do
                                               let tRev = LocalMemory g rev
                                                   pRev = case th of
                                                     Nothing -> MainState tRev
                                                     Just th' -> ThreadState' th' tRev
                                               return $ RState pRev
                                           ) tp
                    foldlM (\cur ev
                            -> foldlM (\cur (ptr,(cond,idx))
                                       -> if memoryLoc ptr == LocalTrg g
                                          then do
                                            (res,ncur,_) <- accessAlloc
                                                            (\val _ -> do
                                                                nval <- symITE cond
                                                                        (symbolicValue $
                                                                         writeContent ev)
                                                                        val
                                                                return (Success (),nval,())
                                                            ) (idxList (offsetPattern ptr) idx)
                                                            cur ()
                                            return ncur
                                          else return cur
                                      ) cur (Map.toList $ target ev)
                           ) old (events st)
                ) (threadGlobalDesc desc)
        return ThreadState { latchBlocks = blks
                           , latchValues = vals
                           , threadArgument = arg
                           , threadGlobals = glob
                           , threadReturn = ret }
  nxtMain <- nxtThread Nothing (mainStateDesc $ stateAnnotation st)
  nxtThs <- sequence $ Map.mapWithKey
            (\thd desc -> do
                let Just rstep = Map.lookup (Just thd) rsteps
                    oldAct = RState $ ThreadActivation thd
                act1 <- case Map.lookup thd (spawnEvents st) of
                  Nothing -> return oldAct
                  Just spawns -> do
                    anySpawn <- mapM (\(spawner,cond,_) -> do
                                         let Just rstepSpawner = Map.lookup spawner rsteps
                                         rstepSpawner .&. cond
                                     ) spawns >>= mkOr
                    oldAct .|. anySpawn
                act2 <- case Map.lookup thd (termEvents st) of
                  Nothing -> return act1
                  Just terms -> do
                    cond <- mkOr (fmap fst terms)
                    (not' (rstep .&. cond)) .&. act1
                st <- nxtThread (Just thd) desc
                return (act2,st)
            ) (threadStateDesc $ stateAnnotation st)
  nxtMem <- sequence $ Map.mapWithKey
            (\loc tp -> do
                old <- createComposite (\_ rev -> return $ RState $ GlobalMemory loc rev) tp
                foldlM (\cur ev
                         -> let Just rstep = Map.lookup (eventThread ev) rsteps
                            in foldlM (\cur (ptr,(cond,idx))
                                       -> if memoryLoc ptr == (case loc of
                                                                Left alloc -> AllocTrg alloc
                                                                Right glob -> GlobalTrg glob)
                                          then do
                                            (res,ncur,_) <- accessAlloc
                                                            (\val _ -> do
                                                                rcond <- rstep .&. cond
                                                                nval <- symITE rcond
                                                                        (symbolicValue $
                                                                         writeContent ev)
                                                                        val
                                                                return (Success (),nval,())
                                                            ) (idxList (offsetPattern ptr) idx)
                                                            cur ()
                                            return ncur
                                          else return cur
                                      ) cur (Map.toList $ target ev)
                       ) old (events st)
            ) (memoryDesc $ stateAnnotation st)
  asserts <- mapM (\(th,e) -> do
                      let Just rstep = Map.lookup th rsteps
                      (not' rstep) .|. e
                  ) (assertions st)
  return $ LLVMTransRel { llvmInputDesc = inputAnnotation st
                        , llvmStateDesc = stateAnnotation st
                        , llvmDefinitions = definitions st
                        , llvmInit = ProgramState { mainState = mainInit
                                                  , threadState = thsInit
                                                  , memory = memInit }
                        , llvmNext = ProgramState { mainState = nxtMain
                                                  , threadState = nxtThs
                                                  , memory = nxtMem }
                        , llvmAssertions = asserts
                        , llvmInternalYields = Map.keys $ internalYieldEdges st
                        }

{-outputMem :: RealizationState ProgramInput ProgramState
             (Map MemoryLoc (AllocVal (RExpr ProgramInput ProgramState)),
              Map (Maybe (Ptr CallInst)) (Map (Ptr GlobalVariable)
                                          (AllocVal (RExpr ProgramInput ProgramState))),
              RealizationState ProgramInput ProgramState)
outputMem real
  = while "Generating output memory: " $
    Map.foldlWithKey
    (\(mem,lmem,real) n ev -> case ev of
      WriteEvent trgs cont wth _
        -> Map.foldlWithKey
           (\(mem,lmem,real) trg cond
            -> let (cond',dyn) = cond inp
                   idx = idxList (offsetPattern trg) dyn
               in case memoryLoc trg of
                    LocalTrg g
                      -> let Just vals = Map.lookup wth lmem
                             Just val = Map.lookup g vals
                             (_,nval,ngates) = accessWrite cont n idx cond' val (gateMp real)
                             nlmem = Map.insert wth (Map.insert g nval vals) lmem
                         in (mem,nlmem,real { gateMp = ngates })
                    _ -> let loc = case memoryLoc trg of
                                     AllocTrg i -> Left i
                                     GlobalTrg g -> Right g
                             val = case Map.lookup loc mem of
                                     Just v -> v
                             (_,nval,ngates) = accessWrite cont n idx cond' val (gateMp real)
                         in (Map.insert loc nval mem,lmem,
                             real { gateMp = ngates })
           ) (mem,lmem,real) trgs
    ) (memory (fst inp),
       Map.union (Map.singleton Nothing (threadGlobals $ mainState $ fst inp))
                 (Map.mapKeysMonotonic Just $
                  fmap (\(_,ts) -> threadGlobals ts) (threadState $ fst inp)),
       real) (events real)
  where
    accessWrite cont n idx cond' val gates
      = --trace ("Access write "++show idx) $
        accessAllocTypedIgnoreErrors (symbolicType cont)
        (\old gates -> let (new,ngates) = addSymGate gates
                                          (case typeUnion
                                                (symbolicType cont)
                                                (extractArgAnnotation old) of
                                           Just rtp -> rtp)
                                          (\inp -> symITE cond'
                                                   (symbolicValue cont inp)
                                                   old)
                                          (Just $ "write"++show n)
                       in (new,ngates)
        ) idx val gates-}

getConstant :: TranslationOptions -> Ptr Constant -> IO (Struct LLVMVal)
getConstant opts (castDown -> Just cint) = do
  tp <- LLVM.getType cint
  bw <- getBitWidth tp
  v <- constantIntGetValue cint
  rv <- apIntGetSExtValue v
  if bw==1
    then return $ Singleton $ ValBool $ RExpr $ E.Const $ BoolValue (rv/=0)
    else if bitPrecise opts
         then reifyNat (fromIntegral bw) $
              \bw' -> return $ Singleton $ ValBounded $ RExpr $ E.Const $
                               BitVecValue (fromIntegral rv) bw'
         else return $ Singleton $ ValInt $ RExpr $ E.Const $ IntValue (fromIntegral rv)
getConstant opts (castDown -> Just czero) = do
  tp <- LLVM.getType (czero::Ptr ConstantAggregateZero)
  zeroInit tp
  where
     zeroInit (castDown -> Just itp) = do
       bw <- getBitWidth itp
       if bw==1
         then return $ Singleton $ ValBool $ RExpr $ E.Const $ BoolValue False
         else return $ Singleton $ ValInt $ RExpr $ E.Const $ IntValue 0
     zeroInit (castDown -> Just struct) = do
       specialInit <- do
         hasName <- structTypeHasName struct
         if hasName
           then do
           name <- structTypeGetName struct >>= stringRefData
           case name of
            "struct.pthread_mutex_t" -> return $ Just $ Singleton $
                                        ValBool $ RExpr $ E.Const $ BoolValue False
            "struct.pthread_rwlock_t" -> return $ Just $ Singleton $
                                         ValVector [ValBool $ RExpr $ E.Const $ BoolValue False
                                                   ,ValInt $ RExpr $ E.Const $ IntValue 0]
            "struct.__thread_id" -> return $ Just $ Singleton $
                                    ValThreadId $ Map.empty
            "struct.pthread_cond_t" -> return $ Just $ Singleton $
                                       ValCondition $ Map.empty
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
     zeroInit (castDown -> Just (ptp::Ptr PointerType)) = do
       ptp' <- sequentialTypeGetElementType ptp
               >>= translateType0 opts
       return $ Singleton $ ValPtr Map.empty ptp'
     zeroInit tp = do
       typeDump tp
       error "No zero init."
getConstant opts (castDown -> Just cstruct) = do
  tp <- LLVM.getType (cstruct::Ptr ConstantStruct)
  num <- structTypeGetNumElements tp
  vals <- mapM (\i -> constantGetAggregateElement cstruct i >>= getConstant opts
               ) [0..num-1]
  return $ Struct vals
{-getConstant (castDown -> Just cstruct) = do
  tp <- getType (cstruct::Ptr ConstantStruct)
  name <- structTypeGetName tp >>= stringRefData
  case name of
   "struct.pthread_mutex_t" -> return $ ValBool (constant False)-}
getConstant opts (castDown -> Just (ptr::Ptr ConstantPointerNull)) = do
  tp <- LLVM.getType ptr
  stp <- sequentialTypeGetElementType tp
  rtp <- translateType0 opts stp
  return (Singleton (ValPtr { valPtr = Map.empty
                            , valPtrType = rtp }))
getConstant opts (castDown -> Just (cvec::Ptr ConstantDataArray)) = do
  sz <- constantDataSequentialGetNumElements cvec
  els <- mapM (\i -> do
                 c <- constantDataSequentialGetElementAsConstant cvec i
                 getConstant opts c
              ) [0..sz-1]
  return $ Struct els
getConstant opts (castDown -> Just (cvec::Ptr ConstantDataVector)) = do
  sz <- constantDataSequentialGetNumElements cvec
  els <- mapM (\i -> do
                 c <- constantDataSequentialGetElementAsConstant cvec i
                 getConstant opts c
              ) [0..sz-1]
  return $ Struct els
getConstant _ (castDown -> Just (_::Ptr ConstantArray)) = error "getConstant: ConstantArray"
getConstant _ (castDown -> Just (_::Ptr ConstantVector)) = error "getConstant: ConstantVector"
getConstant _ c = do
  str <- valueToString c
  error $ "getConstant: "++str

allPtrsOfType :: Struct SymType -> Map MemoryTrg AllocType -> Map MemoryPtr ()
allPtrsOfType tp mem
  = Map.fromList [ (MemoryPtr loc idx,())
                 | (loc,tp') <- Map.toList mem
                 , idx <- allAllocPtrs tp' ]
  where
    allAllocPtrs (TpStatic n tp')
      = [ acc:idx
        | idx <- allStructPtrs tp'
        , acc <- if n > 1
                 then DynamicAccess:[ StaticAccess (fromIntegral i)
                                    | i <- [0..n-1] ]
                 else [ StaticAccess (fromIntegral i)
                      | i <- [0..n-1] ]]
    allAllocPtrs (TpDynamic tp')
      = [ DynamicAccess:idx
        | idx <- allStructPtrs tp' ]
    allStructPtrs tp' = if sameStructType tp tp'
                        then [[]]
                        else (case tp' of
                               Struct [] -> []
                               Struct tps
                                 | allEq tps -> [ DynamicAccess:idx
                                                | idx <- allStructPtrs (head tps) ]++
                                                [ StaticAccess n:idx
                                                | (n,tp') <- zip [0..] tps
                                                , idx <- allStructPtrs tp' ]
                                 | otherwise -> [ StaticAccess n:idx
                                                | (n,tp') <- zip [0..] tps
                                                , idx <- allStructPtrs tp' ]
                               _ -> [])
    allEq [] = True
    allEq (tp:xs) = allEq' tp xs
    allEq' _ [] = True
    allEq' tp (tp':xs) = tp==tp' && allEq' tp xs

while :: String -> a -> a
while act = mapException (RealizationException act)

instance Show RealizationException where
  show (RealizationException pref ex) = pref++show ex

instance Exception RealizationException

instance GetType (RExpr ProgramInput ProgramState) where
  getType (RExpr e) = getType e
  getType (RInput rev) = getType rev
  getType (RState rev) = getType rev
  getType (RRef (DefExpr _ tp)) = tp
