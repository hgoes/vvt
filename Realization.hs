{-# LANGUAGE ViewPatterns,RankNTypes,ScopedTypeVariables,PackageImports,GADTs #-}
module Realization where

import Gates

import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)
import qualified Language.SMTLib2.Internals as SMT
import Foreign.Ptr
import LLVM.FFI
import qualified Data.Graph.Inductive as Gr
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (mapAccumL,sequence,traverse,mapM)
import Data.Foldable (foldlM)
import Data.Typeable (cast)
import Data.Either
import "mtl" Control.Monad.State (StateT,runStateT,get,gets,put,modify,lift,liftIO)
import Control.Applicative
import Prelude hiding (sequence,mapM)
import Data.List (intersperse)
import System.IO.Unsafe
import Foreign.Storable (peek)
import Foreign.C.String
import Foreign.Marshal.Array

import Language.SMTLib2.Pipe

type ValueMap = Map (Ptr Instruction) (SMTExpr UntypedValue)

-- | Stores activation condition for backward edges
--   Edges are stored in Target -> Source direction.
--   Map.fromList [(blk1,Map.fromList [(blk2,act)])] describes one edge, from blk2 to blk1 with condition act.
type LatchActs = Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (SMTExpr Bool))

-- | Activation vars, inputs and latch instructions
type LLVMInput = (LatchActs,ValueMap,ValueMap)

data LatchState = Defined (Ptr BasicBlock)
                | Latched
                | DefinedWhen (Ptr BasicBlock)

data RealizedBlock = RealizedBlock { latchedInstrs :: Map (Ptr Instruction)
                                                      (ProxyArgValue,LatchState)
                                   , realizedActivation :: LLVMInput -> SMTExpr Bool
                                   , realizedOutgoings :: Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool)
                                   }

data RealizedBlocks = RealizedBlocks { realizedBlocks :: Map (Ptr BasicBlock) RealizedBlock
                                     , realizedLatchActs :: Map (Ptr BasicBlock)
                                                            (Map (Ptr BasicBlock) ())
                                     , realizedLatches :: Map (Ptr Instruction) ProxyArgValue
                                     , realizedInputs :: Map (Ptr Instruction) ProxyArgValue
                                     , realizedGates :: GateMap LLVMInput
                                     , realizedInstrs :: Map (Ptr Instruction)
                                                         (ProxyArgValue,
                                                          LLVMInput -> SMTExpr UntypedValue)
                                     , realizedAssumes :: [LLVMInput -> SMTExpr Bool]
                                     , realizedAsserts :: [LLVMInput -> SMTExpr Bool]
                                     , realizedInit :: Ptr BasicBlock
                                     }

data BlockGraph a = BlockGraph { dependencies :: Gr.Gr a ()
                               , nodeMap :: Map (Ptr BasicBlock) Gr.Node
                               }

data ConcreteValues = ConcreteValues { srcBlock :: Ptr BasicBlock
                                     , trgBlock :: Ptr BasicBlock
                                     , latchValues :: Map (Ptr Instruction) SMT.Value
                                     , inputValues :: Map (Ptr Instruction) SMT.Value
                                     }

data AnalyzationSt = AnalyzationSt { analyzedBlock :: Ptr BasicBlock
                                   , readVars :: Map (Ptr Instruction) ProxyArgValue
                                   , readVarsTrans :: Map (Ptr Instruction) ProxyArgValue
                                   , phiReadVars :: Map (Ptr BasicBlock) (Map (Ptr Instruction) ProxyArgValue)
                                   , defineVars :: Map (Ptr Instruction) ProxyArgValue
                                   , defineInputs :: Map (Ptr Instruction) ProxyArgValue
                                   , jumpsTo :: Set (Ptr BasicBlock)
                                   }

data RealizationEnv = RealizationEnv { activation :: LLVMInput -> SMTExpr Bool
                                     , phis :: Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool,
                                                                     Map (Ptr Instruction) (ProxyArgValue,
                                                                                            LLVMInput -> SMTExpr UntypedValue)
                                                                    )
                                     , locals :: Map (Ptr Instruction)
                                                 (ProxyArgValue,
                                                  LLVMInput -> SMTExpr UntypedValue)
                                     , newDefinitions :: Map (Ptr Instruction)
                                                         (ProxyArgValue,
                                                          LLVMInput -> SMTExpr UntypedValue)
                                     , gateMp :: GateMap LLVMInput
                                     , outgoing :: Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool)
                                     , assertions' :: [LLVMInput -> SMTExpr Bool]
                                     , assumptions' :: [LLVMInput -> SMTExpr Bool]
                                     }

type RealizationMonad = StateT RealizationEnv IO

newtype Realization a = Realization { runRealization :: AnalyzationSt -> (AnalyzationSt,RealizationMonad a) }

type ErrorTrace = [ConcreteValues]

reReadVar :: Ptr Instruction -> ProxyArgValue
             -> Realization (LLVMInput -> SMTExpr UntypedValue)
reReadVar i tp
  = Realization $
    \anaSt -> (if Map.member i (defineVars anaSt)
               then anaSt
               else anaSt { readVars = Map.insert i tp (readVars anaSt) },
               do
                 loc <- gets locals
                 case Map.lookup i loc of
                  Just res -> return $ snd res
                  Nothing -> do
                    name <- liftIO $ getNameString i
                    error $ "Can't find local var "++name)

reReadPhi :: Ptr BasicBlock -> Ptr Instruction -> ProxyArgValue
             -> Realization (LLVMInput -> SMTExpr UntypedValue)
reReadPhi blk i tp
  = Realization $
    \anaSt -> (anaSt { phiReadVars = Map.insertWith Map.union blk
                                     (Map.singleton i tp)
                                     (phiReadVars anaSt) },
               do
                 blks <- gets phis
                 case Map.lookup blk blks of
                  Just (_,is) -> case Map.lookup i is of
                    Just res -> return $ snd res)

reDefineVar' :: Ptr Instruction -> ProxyArgValue
                -> Realization (LLVMInput -> SMTExpr UntypedValue)
                -> Realization ()
reDefineVar' i (ProxyArgValue (_::a) ann) v
  = reDefineVar i ann
    (fmap (\f inp -> castUntypedExprValue (f inp) :: SMTExpr a) v)

reDefineVar :: SMTValue a => Ptr Instruction -> SMTAnnotation a
               -> Realization (LLVMInput -> SMTExpr a)
               -> Realization ()
reDefineVar i p (v::Realization (LLVMInput -> SMTExpr a))
  = Realization $
    \anaSt -> let (anaSt1,vgen) = runRealization v anaSt
                  proxy = ProxyArgValue
                          (undefined::a) p
              in (anaSt1 { defineVars = Map.insert i
                                        proxy
                                        (defineVars anaSt1) },
                  do
                    rv <- vgen
                    name <- liftIO $ getNameString i
                    st <- get
                    let (expr,gmp) = addGate (gateMp st)
                                     (Gate rv p (Just name))
                    put $ st { gateMp = gmp
                             , locals = Map.insert i (proxy,const (UntypedExprValue expr))
                                        (locals st)
                             , newDefinitions = Map.insert i (proxy,const (UntypedExprValue expr))
                                                (newDefinitions st)
                             })

reMkInput :: Ptr Instruction -> ProxyArgValue
             -> Realization (LLVMInput -> SMTExpr UntypedValue)
reMkInput i p
  = Realization $ \anaSt -> (anaSt { defineVars = Map.insert i p (defineVars anaSt)
                                   , defineInputs = Map.insert i p (defineInputs anaSt) },
                             do
                               let acc (_,inp,_) = inp Map.! i
                               modify $ \st -> st { locals = Map.insert i
                                                             (p,acc)
                                                             (locals st)
                                                  , newDefinitions = Map.insert i
                                                                     (p,acc)
                                                                     (newDefinitions st)
                                                  }
                               return acc)

reJump :: Ptr BasicBlock
          -> Realization (LLVMInput -> SMTExpr Bool)
          -> Realization ()
reJump blk cond
  = Realization $
    \anaSt -> let (anaSt1,cgen) = runRealization cond anaSt
              in (anaSt1 { jumpsTo = Set.insert blk (jumpsTo anaSt1) },
                  do
                    c <- cgen
                    modify $ \st -> st { outgoing = Map.insertWith (\c1 c2 inp -> (c1 inp) .||. (c2 inp))
                                                    blk c
                                                    (outgoing st) })

reAssert :: Realization (LLVMInput -> SMTExpr Bool)
            -> Realization ()
reAssert cond
  = Realization $
    \anaSt -> let (anaSt1,cgen) = runRealization cond anaSt
              in (anaSt1,do
                     c <- cgen
                     modify $ \st -> st { assertions' = c:(assertions' st) })

reAssume :: Realization (LLVMInput -> SMTExpr Bool)
            -> Realization ()
reAssume cond
  = Realization $
    \anaSt -> let (anaSt1,cgen) = runRealization cond anaSt
              in (anaSt1,do
                     c <- cgen
                     modify $ \st -> st { assumptions' = c:(assumptions' st) })

emptyAnalyzationSt :: Ptr BasicBlock -> AnalyzationSt
emptyAnalyzationSt blk
  = AnalyzationSt { analyzedBlock = blk
                  , phiReadVars = Map.empty
                  , readVars = Map.empty
                  , readVarsTrans = Map.empty
                  , defineVars = Map.empty
                  , defineInputs = Map.empty
                  , jumpsTo = Set.empty
                  }

instance Functor Realization where
  fmap f (Realization x)
    = Realization $ \anaSt -> let (anaSt',res) = x anaSt
                              in (anaSt',fmap f res)

instance Applicative Realization where
  pure x = Realization $ \anaSt -> (anaSt,return x)
  (<*>) (Realization f) (Realization x)
    = Realization $ \anaSt -> let (anaSt1,rf) = f anaSt
                                  (anaSt2,rx) = x anaSt1
                              in (anaSt2,do
                                     rrf <- rf
                                     rrx <- rx
                                     return $ rrf rrx)

analyzeValue :: Ptr Value -> IO (Realization (LLVMInput -> SMTExpr UntypedValue))
analyzeValue (castDown -> Just instr) = do
  tp <- getType instr >>= translateType
  return $ reReadVar instr tp
analyzeValue (castDown -> Just i) = do
  c <- analyzeConstant i
  return (pure $ const c)

analyzeConstant :: Ptr ConstantInt -> IO (SMTExpr UntypedValue)
analyzeConstant i = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  let val = if bw==1
            then UntypedExprValue (constant (rv/=0))
            else UntypedExprValue (constant $ fromIntegral rv :: SMTExpr Integer)
  return val

analyzePhi :: ProxyArgValue -> [(Ptr BasicBlock,Ptr Value)]
              -> IO (Realization (LLVMInput -> SMTExpr UntypedValue))
analyzePhi tp inps = do
  rinps <- mapM (\(blk,val) -> case castDown val of
                  Just c -> do
                    rc <- analyzeConstant c
                    return (blk,pure $ const rc)
                  Nothing -> case castDown val of
                    Just i -> return (blk,reReadPhi blk i tp)
                ) inps
  return $ mkSwitch rinps
  where
    mkSwitch [(_,real)] = real
    mkSwitch ((blk,real):reals)
      = Realization $
        \anaSt -> let (anaSt1,act1) = runRealization real
                                      (anaSt { phiReadVars = Map.insertWith
                                                             Map.union
                                                             blk
                                                             Map.empty
                                                             (phiReadVars anaSt)
                                             })
                      (anaSt2,act2) = runRealization (mkSwitch reals) anaSt1
                  in (anaSt2,do
                         phi <- gets phis
                         case Map.lookup blk phi of
                          Just (cond,_) -> do
                            ifT <- act1
                            ifF <- act2
                            withProxyArgValue tp $
                              \(_::a) _
                              -> return $ \inp -> UntypedExprValue $
                                                  ite (cond inp)
                                                  (castUntypedExprValue (ifT inp) :: SMTExpr a)
                                                  (castUntypedExprValue $ ifF inp)
                          Nothing -> error $ "Phi block "++
                                     (unsafePerformIO $ getNameString blk)++
                                     " not found in "++
                                     (show $ fmap (unsafePerformIO . getNameString) $
                                      Map.keys phi))

mergeLatchState :: LatchState -> LatchState -> LatchState
mergeLatchState Latched Latched = Latched
mergeLatchState (Defined bb) (Defined _) = Defined bb
mergeLatchState (DefinedWhen bb) _ = DefinedWhen bb
mergeLatchState _ (DefinedWhen bb) = DefinedWhen bb
mergeLatchState (Defined bb) Latched = DefinedWhen bb
mergeLatchState Latched (Defined bb) = DefinedWhen bb

realizeBlock :: Gr.Node -> BlockGraph (AnalyzationSt,RealizationMonad ())
                -> RealizedBlocks -> IO RealizedBlocks
realizeBlock blkNode gr blks = do
  putStrLn $ "Realizing block "++(unsafePerformIO $ getNameString blk)
  putStrLn $ "Reading: "++(show $ fmap (unsafePerformIO . getNameString) (Map.keys $ readVarsTrans ana))
  putStrLn $ "Defining: "++(show $ fmap (unsafePerformIO . getNameString) (Map.keys $ defineVars ana))
  putStrLn $ "Phi latches: "++(show $ fmap (unsafePerformIO . getNameString) (Map.keys phiLatches))
  ((),nenv) <- runStateT real env
  let nblk = RealizedBlock { latchedInstrs = latchedInstrsOut
                           , realizedActivation = act
                           , realizedOutgoings = outgoing nenv }
  return (blks { realizedBlocks = Map.insert blk nblk (realizedBlocks blks)
               , realizedLatchActs = Map.insert blk nRealizedLatchActs (realizedLatchActs blks)
               , realizedLatches = Map.union (Map.union (realizedLatches blks)
                                              phiLatches)
                                   (fmap fst latchedInstrsIn)
               , realizedInputs = Map.union (realizedInputs blks)
                                  (defineInputs ana)
               , realizedGates = gateMp nenv
               , realizedInstrs = Map.union (realizedInstrs blks) (newDefinitions nenv)
               , realizedAssumes = (fmap (\ass inp -> (act inp) .=>. (ass inp)) $
                                    assumptions' nenv)++
                                   (realizedAssumes blks)
               , realizedAsserts = (fmap (\ass inp -> (act inp) .=>. (ass inp)) $
                                    assertions' nenv)++
                                   (realizedAsserts blks)
               })
  where
    (ana,real) = Gr.lab' $ Gr.context (dependencies gr) blkNode
    blk = analyzedBlock ana
    incs = fmap (Gr.lab' . (Gr.context $ dependencies gr)) $
           Gr.pre (dependencies gr) blkNode
    (realIncs,latchIncs) = partitionEithers $
                           fmap (\(anaSt,real)
                                 -> case Map.lookup (analyzedBlock anaSt)
                                         (realizedBlocks blks) of
                                     Just r -> Left (analyzedBlock anaSt,r)
                                     Nothing -> Right (anaSt,real)
                                ) incs
    nRealizedLatchActs = case realIncs of
                          [] -> Map.singleton nullPtr ()
                          _ -> foldl (\l (inc,_) -> Map.insert (analyzedBlock inc) () l)
                               (Map.findWithDefault Map.empty blk (realizedLatchActs blks))
                               latchIncs
    (act,gates1) = case acts of
      [f] -> (f,realizedGates blks)
      xs -> let (expr,ngt) = addGate (realizedGates blks)
                             (Gate (\inp -> app or' $ fmap (\f -> f inp) xs)
                              () (Just $ unsafePerformIO $ getNameString blk))
            in (const expr,ngt)
    acts = case realIncs of
      [] -> [ \(acts,_,_) -> (acts Map.! blk) Map.! nullPtr ]
      _ -> [ case Map.lookup blk (realizedOutgoings inc) of
              Just c -> \inp -> (realizedActivation inc inp) .&&. (c inp)
           | (_,inc) <- realIncs ]++
           [ \(acts,_,_) -> (acts Map.! blk) Map.! (analyzedBlock inc)
           | (inc,_) <- latchIncs ]    
    (phiLatches,phiInstrs) = Map.mapAccumWithKey
                             (\latches phiBlk phiInstrs
                              -> case Map.lookup phiBlk (realizedBlocks blks) of
                                  Nothing -> (Map.union latches phiInstrs,
                                              (\(acts,_,_) -> (acts Map.! blk)
                                                              Map.! phiBlk,
                                               Map.mapWithKey
                                               (\phiInstr tp
                                                -> (tp,\(_,_,instrs) -> instrs Map.! phiInstr))
                                               phiInstrs))
                                  Just rPhiBlk -> (latches,
                                                   (realizedActivation rPhiBlk,
                                                    Map.mapWithKey
                                                    (\phiInstr _ -> getRealizedPhiVar phiInstr
                                                                    blks rPhiBlk
                                                    ) phiInstrs))
                             ) (realizedLatches blks) (phiReadVars ana)
    latchedInstrs1 = foldl (\cur (_,blk) -> Map.unionWith
                                            (\(tp,c1) (_,c2) -> (tp,mergeLatchState c1 c2))
                                            cur (latchedInstrs blk)
                           ) Map.empty realIncs
    latchedInstrs2 = case latchIncs of
      [] -> latchedInstrs1
      _ -> Map.unionWith
           (\(tp,c1) (_,c2) -> (tp,mergeLatchState c1 c2))
           latchedInstrs1 $
           fmap (\tp -> (tp,Latched)
                ) (readVarsTrans ana)
    latchedInstrsOut = Map.union (fmap (\tp -> (tp,Defined blk)) (defineVars ana))
                       latchedInstrs2
    latchedInstrsIn = Map.intersection latchedInstrs2 (readVars ana)
    (gates2,instrsIn) = Map.mapAccumWithKey
                        (\gates instr (tp,st) -> case st of
                          Defined _ -> (gates,
                                        (tp,case Map.lookup instr (realizedInstrs blks) of
                                         Just (_,f) -> f))
                          Latched -> (gates,
                                      (tp,\(_,_,instrs) -> case Map.lookup instr instrs of
                                        Just v -> v))
                          DefinedWhen blk -> case Map.lookup blk (realizedBlocks blks) of
                            Just cblk -> case Map.lookup instr (realizedInstrs blks) of
                              Just (_,f)
                                -> withProxyArgValue tp $
                                   \(_::a) ann
                                   -> let trans inp@(_,_,instrs)
                                            = case Map.lookup instr instrs of
                                             Just v -> ite (realizedActivation cblk inp)
                                                       (castUntypedExprValue (f inp) :: SMTExpr a)
                                                       (castUntypedExprValue v)
                                          (expr,ngates) = addGate gates
                                                          (Gate trans ann $
                                                           Just $ (unsafePerformIO $ getNameString instr)++
                                                           "_"++
                                                           (unsafePerformIO $ getNameString blk))
                                      in (ngates,(tp,const $ UntypedExprValue expr))
                        ) gates1 latchedInstrsIn
    env = RealizationEnv { activation = act
                         , phis = phiInstrs
                         , locals = instrsIn
                         , newDefinitions = Map.empty
                         , gateMp = gates2
                         , outgoing = Map.empty
                         , assertions' = []
                         , assumptions' = []
                         }
    getRealizedPhiVar :: Ptr Instruction -> RealizedBlocks -> RealizedBlock
                      -> (ProxyArgValue,
                          LLVMInput -> SMTExpr UntypedValue)
    getRealizedPhiVar instr blks blk
      = case Map.lookup instr (latchedInstrs blk) of
         Just (_,Defined _) -> case Map.lookup instr (realizedInstrs blks) of
           Just r -> r
         Just (tp,Latched) -> (tp,\(_,_,instrs) -> case Map.lookup instr instrs of
                                Just r -> r)
         Just (tp,DefinedWhen cblk) -> case Map.lookup cblk (realizedBlocks blks) of
           Just cblk -> case Map.lookup instr (realizedInstrs blks) of
             Just (_,f) -> withProxyArgValue tp $
                           \(_::a) _
                           -> (tp,\inp@(_,_,instrs)
                                  -> UntypedExprValue $
                                     case Map.lookup instr instrs of
                                      Just v -> ite (realizedActivation cblk inp)
                                                (castUntypedExprValue (f inp) :: SMTExpr a)
                                                (castUntypedExprValue v))

realizeFunction :: Ptr Function -> IO RealizedBlocks
realizeFunction fun = do
  gr <- analyzeFunction fun
  entr <- getEntryBlock fun
  let [dfsTree] = Gr.dff [(nodeMap gr) Map.! entr] (dependencies gr)
      order = reverse $ Gr.postorder dfsTree
  foldlM (\cblks nd -> realizeBlock nd gr cblks
         ) (RealizedBlocks { realizedInit = entr
                           , realizedBlocks = Map.empty
                           , realizedLatchActs = Map.empty
                           , realizedLatches = Map.empty
                           , realizedInputs = Map.empty
                           , realizedGates = Map.empty
                           , realizedInstrs = Map.empty
                           , realizedAssumes = []
                           , realizedAsserts = [] })
    order

analyzeFunction :: Ptr Function -> IO (BlockGraph (AnalyzationSt,RealizationMonad ()))
analyzeFunction fun = do
  blks <- getBasicBlockList fun >>= ipListToList
          >>= mapM (\blk -> do
                       real <- analyzeBlock blk
                       return $ runRealization real (emptyAnalyzationSt blk)
                   )
  let nodes = zip [0..] blks
      node_mp = Map.fromList (fmap (\(i,(info,_)) -> (analyzedBlock info,i)) nodes)
  edges <- mapM (\(i,(info,_)) -> do
                    return [ (i,j,())
                           | succ <- Set.toList $ jumpsTo info
                           , let j = node_mp ! succ ]
                ) nodes
  let gr1 = Gr.mkGraph nodes (concat edges)
      gr2 = readTransitivity' gr1
  return $ BlockGraph gr2 node_mp
  where
    readTransitivity' gr = readTransitivity
                           (Gr.nmap (\(info,real) -> (info { readVarsTrans = readVars info },real)) gr) $
                           Map.fromListWith Map.union
                           [ (src,readVars info)
                           | (trg,(info,_)) <- Gr.labNodes gr
                           , src <- Gr.pre gr trg ]
    
    readTransitivity gr nds = case Map.minViewWithKey nds of
      Nothing -> gr
      Just ((nd,reads),nds')
        -> let (Just (inc,_,(info,real),out),gr') = Gr.match nd gr
               notDefined = Map.difference
                            (Map.difference reads (defineVars info))
                            (defineInputs info)
               notRead = Map.difference notDefined (readVarsTrans info)
           in if Map.null notRead
              then readTransitivity gr nds'
              else readTransitivity
                   ((inc,nd,(info { readVarsTrans = Map.union (readVarsTrans info) notRead },
                             real),out) Gr.& gr')
                   (foldl (\mp (_,nd) -> Map.insertWith Map.union nd notRead mp) nds' inc)


analyzeBlock :: Ptr BasicBlock -> IO (Realization ())
analyzeBlock blk = do
  instrs <- getInstList blk >>= ipListToList
  analyzeInstructions instrs

analyzeInstructions :: [Ptr Instruction] -> IO (Realization ())
analyzeInstructions [] = return (pure ())
analyzeInstructions (i:is) = do
  ri <- analyzeInstruction i
  ris <- analyzeInstructions is
  return $ ri *> ris

analyzeInstruction :: Ptr Instruction -> IO (Realization ())
analyzeInstruction i@(castDown -> Just opInst) = do
  lhs <- getOperand opInst 0
  rhs <- getOperand opInst 1
  op <- binOpGetOpCode opInst
  tp <- valueGetType lhs >>= translateType
  flhs <- analyzeValue lhs
  frhs <- analyzeValue rhs
  return $ case op of
   Add -> reDefineVar i () $
          (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) +
                             (castUntypedExprValue (rrhs inp))) <$>
          flhs <*> frhs
   Sub -> reDefineVar i () $
          (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) -
                             (castUntypedExprValue (rrhs inp))) <$>
          flhs <*> frhs
   Mul -> reDefineVar i () $
          (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) *
                             (castUntypedExprValue (rrhs inp))) <$>
          flhs <*> frhs
   And -> if tp==(ProxyArgValue (undefined::Bool) ())
          then reDefineVar i () $
               (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp)) .&&.
                                  (castUntypedExprValue (rrhs inp))) <$>
               flhs <*> frhs
          else error "And operator can't handle non-bool inputs."
   Or -> if tp==(ProxyArgValue (undefined::Bool) ())
         then reDefineVar i () $
              (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp)) .||.
                                 (castUntypedExprValue (rrhs inp))) <$>
              flhs <*> frhs
         else error "Or operator can't handle non-bool inputs."
   Xor -> if tp==(ProxyArgValue (undefined::Bool) ())
          then reDefineVar i () $
               (\rlhs rrhs inp -> app xor
                                  [castUntypedExprValue (rlhs inp)
                                  ,castUntypedExprValue (rrhs inp)]) <$>
               flhs <*> frhs
          else error "Xor operator can't handle non-bool inputs."
   _ -> error $ "Unknown operator: "++show op
analyzeInstruction (castDown -> Just brInst) = do
  is_cond <- branchInstIsConditional brInst
  if is_cond
    then (do
             ifTrue <- terminatorInstGetSuccessor brInst 0
             ifFalse <- terminatorInstGetSuccessor brInst 1
             cond <- branchInstGetCondition brInst >>= analyzeValue
             return $ reJump ifTrue (fmap (\c inp -> castUntypedExprValue (c inp))
                                     cond) *>
               reJump ifFalse (fmap (\c inp -> not' $ castUntypedExprValue (c inp))
                               cond))
    else (do
             trg <- terminatorInstGetSuccessor brInst 0
             return $ reJump trg (pure (const $ constant True)))
analyzeInstruction i@(castDown -> Just call) = do
  fname <- getFunctionName call
  case fname of
   '_':'_':'u':'n':'d':'e':'f':_ -> do
     tp <- getType i >>= translateType
     return $ reMkInput i tp *> pure ()
   "assert" -> do
     cond <- callInstGetArgOperand call 0 >>= analyzeValue
     return $ reAssert $ fmap (\c inp -> castUntypedExprValue (c inp)) cond
   "assume" -> do
     cond <- callInstGetArgOperand call 0 >>= analyzeValue
     return $ reAssume $ fmap (\c inp -> castUntypedExprValue (c inp)) cond
   _ -> error $ "Unknown function "++fname
analyzeInstruction i@(castDown -> Just icmp) = do
  op <- getICmpOp icmp
  lhs <- getOperand icmp 0 >>= analyzeValue
  rhs <- getOperand icmp 1 >>= analyzeValue
  return $ case op of
   I_EQ -> reDefineVar i () $
           (\rlhs rrhs inp -> entypeValue (.==. (castUntypedExprValue (rrhs inp))
                                          ) (rlhs inp)) <$>
           lhs <*> rhs
   I_NE -> reDefineVar i () $
           (\rlhs rrhs inp -> entypeValue (\lhs' -> not' $
                                                    lhs' .==. (castUntypedExprValue (rrhs inp))
                                          ) (rlhs inp)) <$>
           lhs <*> rhs
   I_SGE -> reDefineVar i () $
            (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) .>=.
                               (castUntypedExprValue (rrhs inp))) <$>
            lhs <*> rhs
   I_SGT -> reDefineVar i () $
            (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) .>.
                               (castUntypedExprValue (rrhs inp))) <$>
            lhs <*> rhs
   I_SLE -> reDefineVar i () $
            (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) .<=.
                               (castUntypedExprValue (rrhs inp))) <$>
            lhs <*> rhs
   I_SLT -> reDefineVar i () $
            (\rlhs rrhs inp -> (castUntypedExprValue (rlhs inp) :: SMTExpr Integer) .<.
                               (castUntypedExprValue (rrhs inp))) <$>
            lhs <*> rhs
analyzeInstruction i@(castDown -> Just ret) = do
  rval <- returnInstGetReturnValue ret
  return $ pure ()
analyzeInstruction i@(castDown -> Just (zext::Ptr ZExtInst)) = do
  op <- getOperand zext 0
  tp <- valueGetType op >>= translateType
  fop <- analyzeValue op
  if tp==(ProxyArgValue (undefined::Bool) ())
    then return $ reDefineVar i () $
         fmap (\v inp -> ite (castUntypedExprValue (v inp))
                         (constant (1::Integer))
                         (constant 0)) fop
    else withProxyArgValue tp $
         \(_::a) ann -> return $ reDefineVar i ann $
                        fmap (\v inp -> castUntypedExprValue (v inp) :: SMTExpr a) fop
analyzeInstruction i@(castDown -> Just select) = do
  cond <- selectInstGetCondition select >>= analyzeValue
  tVal <- selectInstGetTrueValue select
  tp <- valueGetType tVal >>= translateType
  tVal' <- analyzeValue tVal
  fVal' <- selectInstGetFalseValue select >>= analyzeValue
  withProxyArgValue tp $
    \(_::a) ann -> return $ reDefineVar i ann $
                   (\c t f inp -> ite (castUntypedExprValue $ c inp)
                                  (castUntypedExprValue (t inp) :: SMTExpr a)
                                  (castUntypedExprValue (f inp))) <$>
                   cond <*> tVal' <*> fVal'
analyzeInstruction i@(castDown -> Just phi) = do
  num <- phiNodeGetNumIncomingValues phi
  tp <- valueGetType i >>= translateType
  trg <- instructionGetParent i
  phis <- mapM (\n -> do
                   iblk <- phiNodeGetIncomingBlock phi n
                   ival <- phiNodeGetIncomingValue phi n
                   return (iblk,ival)
               ) [0..(num-1)]
  ana <- analyzePhi tp phis
  return $ reDefineVar' i tp ana
analyzeInstruction (castDown -> Just sw) = do
  cond <- switchInstGetCondition sw >>= analyzeValue
  def <- switchInstGetDefaultDest sw
  cases <- switchInstGetCases sw >>=
           mapM (\(val,trg) -> do
                    APInt _ val' <- constantIntGetValue val >>= peek
                    return (val',trg))
  return $ mkDefault def cases cond *>
    mkSwitch cases cond
  where
    mkDefault def cases val
      = reJump def (fmap (\rval inp -> app and' [ not' $
                                                  (castUntypedExprValue (rval inp)) .==.
                                                  (constant i)
                                                | (i,_) <- cases ]
                         ) val)
    mkSwitch [] _ = pure ()
    mkSwitch ((i,blk):rest) val
      = reJump blk (fmap (\rval inp -> (castUntypedExprValue (rval inp))
                                       .==. (constant i)
                         ) val) *>
        mkSwitch rest val
analyzeInstruction i = do
  valueDump i
  error "Unknown instruction"

(!) :: (ValueC a,Show b) => Map (Ptr a) b -> Ptr a -> b
(!) mp x = case Map.lookup x mp of
  Just y -> y
  Nothing -> error $ "Key "++(unsafePerformIO $ getNameString x)++" not found in "
             ++show [ (unsafePerformIO $ getNameString i,v) | (i,v) <- Map.toList mp]

blockGraph :: Ptr Function -> IO (BlockGraph (Ptr BasicBlock))
blockGraph fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  let nodes = zip [0..] blks
      node_mp = Map.fromList (fmap (\(i,blk) -> (blk,i)) nodes)
  edges <- mapM (\(i,blk) -> do
                    term <- getTerminator blk
                    no_succs <- terminatorInstGetNumSuccessors term
                    succs <- mapM (terminatorInstGetSuccessor term) [0..no_succs-1]
                    return [ (i,j,())
                           | succ <- succs
                           , let j = node_mp ! succ ]
                ) nodes
  return $ BlockGraph (Gr.mkGraph nodes (concat edges)) node_mp

translateType :: Ptr Type -> IO ProxyArgValue
translateType (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return (ProxyArgValue (undefined::Bool) ())
    _ -> return (ProxyArgValue (undefined::Integer) ())
translateType tp = do
  typeDump tp
  error "Can't translate type"

getFunctionName :: Ptr CallInst -> IO String
getFunctionName ci = do
  val <- callInstGetCalledValue ci
  getFunctionName' val
  where
    getFunctionName' (castDown -> Just (f::Ptr Function))
      = getNameString f
    getFunctionName' (castDown -> Just c) = do
      tp <- constantExprGetOpcode c
      case tp of
        CastOp BitCast -> do
          val <- getOperand c 0
          getFunctionName' val

createBlockVars :: String -> RealizedBlocks -> SMT LatchActs
createBlockVars pre st
  = sequence $ Map.mapWithKey
    (\trg -> sequence . Map.mapWithKey
             (\src _ -> do
                 name <- liftIO $ do
                       trgHasName <- hasName trg
                       srcHasName <- if src==nullPtr
                                     then return False
                                     else hasName src
                       trgName <- if trgHasName
                                  then getNameString trg
                                  else return "bb"
                       srcName <- if srcHasName
                                  then getNameString src
                                  else return "bb"
                       return (pre++srcName++"."++trgName)
                 varNamed name)
    ) (realizedLatchActs st)

-- | Encode the fact that only exactly one block may be active
blockConstraint :: LatchActs -> SMTExpr Bool
blockConstraint blks
  = app or' $
    fmap (app and') $
    exactlyOne [] [ act
                  | (_,trgs) <- Map.toList blks
                  , (_,act) <- Map.toList trgs ]
  where
    exactlyOne prev [x] = [prev++[x]]
    exactlyOne prev (x:xs)
      = (prev++(x:(fmap not' xs))):
        (exactlyOne (prev++[not' x]) xs)

createInstrVars :: String -> RealizedBlocks -> SMT ValueMap
createInstrVars pre st
  = sequence $ Map.mapWithKey
    (\instr ann -> do
        name <- liftIO $ do
              hn <- hasName instr
              n <- if hn
                   then getNameString instr
                   else return "instr"
              return (pre++n)
        varNamedAnn name ann
    ) (realizedLatches st)

createInputVars :: String -> RealizedBlocks -> SMT ValueMap
createInputVars pre st
  = sequence $ Map.mapWithKey
    (\instr ann -> do
        name <- liftIO $ do
              hn <- hasName instr
              n <- if hn
                   then getNameString instr
                   else return "input"
              return (pre++n)
        varNamedAnn name ann
    ) (realizedInputs st)

declareOutputActs :: (Monad m,Functor m) => RealizedBlocks -> RealizedGates -> LLVMInput
                     -> SMT' m (LatchActs
                               ,RealizedGates)
declareOutputActs st real inp
  = runStateT
    (Map.traverseWithKey
     (\trg srcs
      -> Map.traverseWithKey
         (\src _ -> do
             real <- get
             case Map.lookup src (realizedBlocks st) of
              Just blk -> do
                (expr,nreal) <- lift $ declareGate (realizedActivation blk inp) real
                                (realizedGates st) inp
                put nreal
                return expr
              Nothing
                | src==nullPtr -> return (constant False)
         ) srcs
     ) (realizedLatchActs st)
    ) real

declareOutputInstrs :: (Monad m,Functor m) => RealizedBlocks -> RealizedGates -> LLVMInput
                       -> SMT' m (ValueMap
                                 ,RealizedGates)
declareOutputInstrs st real inp@(acts,_,instrs)
  = runStateT
    (Map.traverseWithKey
     (\instr tp -> do
         real <- get
         let trans = case Map.lookup instr allLatch of
               Just (_,Defined _) -> case Map.lookup instr (realizedInstrs st) of
                 Just (_,f) -> f inp
               Just (_,Latched) -> case Map.lookup instr instrs of
                 Just v -> v
               Just (_,DefinedWhen cblk) -> case Map.lookup cblk (realizedBlocks st) of
                 Just cblk -> case Map.lookup instr (realizedInstrs st) of
                   Just (_,f) -> withProxyArgValue tp $
                                 \(_::a) _
                                 -> UntypedExprValue $
                                    ite (realizedActivation cblk inp)
                                    (castUntypedExprValue (f inp) :: SMTExpr a)
                                    (castUntypedExprValue $ instrs Map.! instr)
         (expr,nreal) <- lift $ declareGate trans real (realizedGates st) inp
         put nreal
         return expr
     ) (realizedLatches st)
    ) real
  where
    allLatch = Map.foldlWithKey
               (\clatch trg srcs
                 -> Map.foldlWithKey
                    (\clatch src _
                      -> case Map.lookup src (realizedBlocks st) of
                          Just blk -> Map.unionWith (\(tp,c1) (_,c2) -> (tp,mergeLatchState c1 c2))
                                      clatch (latchedInstrs blk)
                          Nothing
                            | src==nullPtr -> clatch
                    ) clatch srcs
               ) Map.empty (realizedLatchActs st)

declareAssertions :: (Monad m,Functor m) => RealizedBlocks -> RealizedGates -> LLVMInput
                     -> SMT' m ([SMTExpr Bool]
                               ,RealizedGates)
declareAssertions st real inp
  = runStateT (traverse (\ass -> do
                            real <- get
                            (expr,nreal) <- lift $ declareGate (ass inp) real (realizedGates st) inp
                            put nreal
                            return expr
                        ) (realizedAsserts st)
              ) real

declareAssumptions :: (Monad m,Functor m) => RealizedBlocks -> RealizedGates -> LLVMInput
                     -> SMT' m ([SMTExpr Bool]
                               ,RealizedGates)
declareAssumptions st real inp
  = runStateT (traverse (\ass -> do
                            real <- get
                            (expr,nreal) <- lift $ declareGate (ass inp) real (realizedGates st) inp
                            put nreal
                            return expr
                        ) (realizedAssumes st)
              ) real

initialState :: RealizedBlocks -> LatchActs -> SMTExpr Bool
initialState st acts
  = app and' [ if trgBlk==realizedInit st &&
                  srcBlk==nullPtr
               then act
               else not' act
             | (trgBlk,srcs) <- Map.toList acts
             , (srcBlk,act) <- Map.toList srcs ]

getConcreteValues :: Monad m => RealizedBlocks -> LLVMInput -> SMT' m ConcreteValues
getConcreteValues st (acts,instrs,inps) = do
  acts' <- mapM (mapM getValue) acts
  (trg,src) <- case [ (trg,src)
                    | (trg,srcs) <- Map.toList acts'
                    , (src,act) <- Map.toList srcs
                    , act ] of
                 [] -> error "Realization.getConcreteValues: No latch block is active."
                 x:_ -> return x
  vals <- concretizeMap instrs (realizedLatches st)
  inps' <- concretizeMap inps (realizedInputs st)
  return $ ConcreteValues { srcBlock = src
                          , trgBlock = trg
                          , latchValues = vals
                          , inputValues = inps' }
  where
    concretizeMap mp tps = do
      res <- mapM (\(instr,ProxyArgValue (_::t) ann)
                   -> case asValueType (undefined::t) ann
                           (\(_::t') ann' -> do
                               v <- getValue (castUntypedExprValue instr::SMTExpr t')
                               return $ mangle v ann') of
                        Nothing -> return Nothing
                        Just act -> do
                          res <- act
                          return $ Just res
                  ) (Map.intersectionWith (,) mp tps)
      return $ Map.mapMaybe id res


instance Show ConcreteValues where
  show cv = unsafePerformIO $ do
    trg <- do
      trgHasName <- hasName (trgBlock cv)
      if trgHasName
        then getNameString (trgBlock cv)
        else return $ show (trgBlock cv)
    src <- if srcBlock cv==nullPtr
           then return ""
           else (do
                    srcHasName <- hasName (srcBlock cv)
                    if srcHasName
                      then getNameString (srcBlock cv)
                      else return $ show (srcBlock cv))
    vals <- mapM (\(instr,val) -> do
                     instrName <- do
                       instrHasName <- hasName instr
                       if instrHasName
                         then getNameString instr
                         else return $ show instr
                     return $ instrName++"="++show val
                 ) (Map.toList $ latchValues cv)
    inps <- mapM (\(instr,val) -> do
                     instrName <- do
                       instrHasName <- hasName instr
                       if instrHasName
                         then getNameString instr
                         else return $ show instr
                     return $ instrName++"="++show val
                 ) (Map.toList $ latchValues cv)
    return $ "("++src++"~>"++trg++"|"++
      concat (intersperse "," vals)++"|"++
      concat (intersperse "," inps)++")"

extractBlock :: Map (Ptr BasicBlock) (Map (Ptr BasicBlock) Bool) -> (Ptr BasicBlock,Ptr BasicBlock)
extractBlock mp = case blks of
  [x] -> x
  [] -> error "No basic block is active in state."
  _ -> error "More than one basic block is active in state."
  where
    blks = [ (src,trg) | (trg,srcs) <- Map.toList mp
                       , (src,act) <- Map.toList srcs
                       , act ]

getProgram :: String -> String -> IO (Ptr Function)
getProgram entry file = do
  Just buf <- getFileMemoryBufferSimple file
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  applyOptimizations mod entry
  moduleDump mod
  moduleGetFunctionString mod entry

applyOptimizations :: Ptr Module -> String -> IO ()
applyOptimizations mod entry = do
  pm <- newPassManager
  mapM (\(APass c) -> do
           pass <- c
           passManagerAdd pm pass) (passes entry)
  passManagerRun pm mod
  deletePassManager pm

data APass = forall p. PassC p => APass (IO (Ptr p))

passes :: String -> [APass]
passes entry
  = [APass createPromoteMemoryToRegisterPass
    ,APass createConstantPropagationPass
    ,APass createLoopSimplifyPass
    ,APass (do
               m <- newCString entry
               arr <- newArray [m]
               export_list <- newArrayRef arr 1
               --export_list <- newArrayRefEmpty
               createInternalizePass export_list)
    ,APass (createFunctionInliningPass 100)
    ,APass createCFGSimplificationPass
    ,APass createInstructionNamerPass]
