{-# LANGUAGE ViewPatterns,RankNTypes,ScopedTypeVariables,PackageImports,GADTs,FlexibleInstances #-}
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
import Data.Foldable (foldlM,concat)
import Foreign.Storable (peek)
import Foreign.C.String
import Foreign.Marshal.Array
import "mtl" Control.Monad.State (StateT,runStateT,get,gets,put,modify,lift,liftIO)
import System.IO.Unsafe
import Data.Traversable (mapAccumL,sequence,traverse,mapM)
import Prelude hiding (sequence,mapM,concat)
import Data.List (intersperse)
import Data.Either (partitionEithers)
import Data.Typeable (cast)

type ValueMap = Map (Ptr Instruction) (SMTExpr UntypedValue)

type LatchActs = Map (Ptr BasicBlock) (SMTExpr Bool)

data LatchState = Defined (Ptr BasicBlock)
                | Latched
                | DefinedWhen (Ptr BasicBlock)

data Analyzation = Analyzation { instructionState :: Map (Ptr Instruction) LatchState
                               , implicitLatches :: Map (Ptr Instruction) (ProxyArgValue,
                                                                           Ptr BasicBlock)
                               , explicitLatches :: Map (Ptr Instruction)
                                                    (ProxyArgValue,
                                                     [(Ptr BasicBlock,Ptr Value)],
                                                     [(Ptr BasicBlock,Ptr Value)])
                               , latchBlocks :: Map (Ptr BasicBlock) ()
                               , analyzedBlocks :: Set (Ptr BasicBlock)
                               , blkGraph :: BlockGraph
                               }

-- | Activation vars, inputs and latch instructions
type LLVMInput = (LatchActs,ValueMap,ValueMap)

data Realization = Realization { edgeActivations :: Map (Ptr BasicBlock)
                                                    (Map (Ptr BasicBlock)
                                                     (LLVMInput -> SMTExpr Bool))
                               , blockActivations :: Map (Ptr BasicBlock)
                                                     (LLVMInput -> SMTExpr Bool)
                               , instructions :: Map (Ptr Instruction)
                                                 RealizedValue
                               , inputs :: Map (Ptr Instruction) ProxyArgValue
                               , forwardEdges :: Map (Ptr BasicBlock) [LLVMInput -> SMTExpr Bool]
                               , asserts :: Map (Ptr BasicBlock) [LLVMInput -> SMTExpr Bool]
                               , assumes :: [LLVMInput -> SMTExpr Bool]
                               , gateMp :: GateMap LLVMInput
                               }

data RealizedValue = forall a. SMTValue a => NormalValue (SMTAnnotation a) (LLVMInput -> SMTExpr a)
                   | IntConst Integer
                   | OrList [LLVMInput -> SMTExpr Integer]
                   | ExtBool (LLVMInput -> SMTExpr Bool)

data BlockGraph = BlockGraph { nodeMap :: Map (Ptr BasicBlock) Gr.Node
                             , dependencies :: Gr.Gr (Ptr BasicBlock) ()
                             }

data RealizedBlocks = RealizedBlocks { realizedLatchBlocks :: Map (Ptr BasicBlock)
                                                              (LLVMInput -> SMTExpr Bool)
                                     , realizedLatches :: Map (Ptr Instruction)
                                                          (ProxyArgValue,
                                                           LLVMInput -> SMTExpr UntypedValue)
                                     , realizedInputs :: Map (Ptr Instruction) ProxyArgValue
                                     , realizedGates :: GateMap LLVMInput
                                     , realizedAssumes :: [LLVMInput -> SMTExpr Bool]
                                     , realizedAsserts :: [LLVMInput -> SMTExpr Bool]
                                     , realizedInit :: Ptr BasicBlock
                                     }

data ConcreteValues = ConcreteValues { block :: Ptr BasicBlock
                                     , latchValues :: Map (Ptr Instruction) SMT.Value
                                     , inputValues :: Map (Ptr Instruction) SMT.Value
                                     }

type ErrorTrace = [ConcreteValues]

data RealizationOptions = RealizationOptions { useErrorState :: Bool
                                             , exactPredecessors :: Bool
                                             }

blockGraph :: Ptr Function -> IO BlockGraph
blockGraph fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  let nodes = zip [0..] blks
      nodeMp = Map.fromList [ (blk,nd) | (nd,blk) <- nodes ]
  lst <- mapM (\(nd,blk) -> do
                  term <- getTerminator blk
                  num <- terminatorInstGetNumSuccessors term
                  succBlks <- mapM (terminatorInstGetSuccessor term) [0..num-1]
                  return [ (nd,nodeMp Map.! blk',())
                         | blk' <- succBlks ]
              ) nodes
  return $ BlockGraph { nodeMap = nodeMp
                      , dependencies = Gr.mkGraph nodes (concat lst)
                      }

analyzeBlock :: Analyzation -> Ptr BasicBlock -> IO Analyzation
analyzeBlock ana blk = do
  instrs <- getInstList blk >>= ipListToList
  foldlM (analyzeInstruction backedges) ana' instrs
  where
    nd = (nodeMap $ blkGraph ana) Map.! blk
    incs = Set.fromList $ fmap (\nd -> case Gr.lab (dependencies $ blkGraph ana) nd of
                                        Just b -> b
                               ) $ Gr.pre (dependencies $ blkGraph ana) nd
    backedges = Set.difference incs (analyzedBlocks ana)
    hasBackedge = not $ Set.null backedges
    isInit = Set.null incs
    nInstrState = if hasBackedge
                  then fmap (\s -> case s of
                              Latched -> Latched
                              Defined blk' -> DefinedWhen blk'
                              DefinedWhen blk' -> DefinedWhen blk'
                            ) (instructionState ana)
                  else instructionState ana
    ana' = ana { instructionState = nInstrState
               , analyzedBlocks = Set.insert blk (analyzedBlocks ana)
               , latchBlocks = if hasBackedge || isInit
                               then Map.insert blk () (latchBlocks ana)
                               else latchBlocks ana }

translateType :: Ptr Type -> IO ProxyArgValue
translateType (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return (ProxyArgValue (undefined::Bool) ())
    _ -> return (ProxyArgValue (undefined::Integer) ())
translateType tp = do
  typeDump tp
  error "Can't translate type"

analyzeValue :: Analyzation -> Ptr Value -> IO Analyzation
analyzeValue ana (castDown -> Just instr)
  = case Map.lookup instr (instructionState ana) of
  Just (Defined _) -> return ana
  Just (DefinedWhen blk) -> do
    tp <- getType instr >>= translateType
    return $ ana { implicitLatches = Map.insert instr (tp,blk)
                                     (implicitLatches ana)
                 }
  Nothing -> return ana
  {-Nothing -> return $ ana { instructionState = Map.insert instr Latched
                                               (instructionState ana)
                          , implicitLatches = Map.insert instr ()
                                              (implicitLatches ana)
                          }-}
analyzeValue ana _ = return ana

analyzeInstruction :: Set (Ptr BasicBlock) -> Analyzation -> Ptr Instruction -> IO Analyzation
analyzeInstruction backedges ana i@(castDown -> Just phi) = do
  blk <- instructionGetParent i
  numPhi <- phiNodeGetNumIncomingValues phi
  phis <- mapM (\n -> do
                   blk <- phiNodeGetIncomingBlock phi n
                   val <- phiNodeGetIncomingValue phi n
                   return (blk,val)
               ) [0..numPhi-1]
  ana1 <- foldlM analyzeValue ana (fmap snd phis)
  let (phis1,phis2) = partitionEithers $
                      fmap (\(blk,val) -> if Set.member blk backedges
                                          then Left (blk,val)
                                          else Right (blk,val)
                           ) phis
  tp <- getType phi >>= translateType
  return $ ana1 { explicitLatches = Map.insert i (tp,phis1,phis2)
                                    (explicitLatches ana1)
                , instructionState = Map.insert i (Defined blk)
                                     (instructionState ana1)
                }
analyzeInstruction _ ana i = do
  blk <- instructionGetParent i
  numOps <- getNumOperands i
  ops <- mapM (getOperand i) [0..numOps-1]
  ana1 <- foldlM analyzeValue ana ops
  return $ ana1 { instructionState = Map.insert i (Defined blk) (instructionState ana1) }

realizeFunction :: RealizationOptions -> Analyzation -> Ptr Function
                   -> IO Realization
realizeFunction opts ana fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  let initInstrs1 = Map.mapWithKey
                    (\i (ProxyArgValue (_::a) ann,_)
                     -> NormalValue ann (\(_,_,instrs)
                                         -> castUntypedExprValue (instrs Map.! i) :: SMTExpr a
                                        )
                    ) (implicitLatches ana)
      initInstrs2 = Map.mapWithKey
                    (\i (ProxyArgValue (_::a) ann,_,_)
                     -> NormalValue ann (\(_,_,instrs)
                                         -> castUntypedExprValue (instrs Map.! i) :: SMTExpr a
                                        )
                    ) (explicitLatches ana)
      initInstrs = Map.union initInstrs1 initInstrs2
      real = Realization { edgeActivations = Map.empty
                         , blockActivations = if useErrorState opts
                                              then Map.singleton nullPtr
                                                   (if exactPredecessors opts
                                                    then (\(acts,_,_) -> app and' $ [acts Map.! nullPtr]++
                                                                         [ not' act
                                                                         | (blk,act) <- Map.toList acts
                                                                         , blk/=nullPtr ]
                                                         )
                                                    else (\(acts,_,_) -> acts Map.! nullPtr))
                                              else Map.empty
                         , instructions = initInstrs
                         , inputs = Map.empty
                         , forwardEdges = Map.empty
                         , asserts = Map.empty
                         , assumes = []
                         , gateMp = emptyGateMap
                         }
  foldlM (realizeBlock opts ana) real blks
             

realizeValue :: Analyzation -> Realization -> Ptr Value
                -> IO RealizedValue
realizeValue ana real (castDown -> Just instr)
  = case Map.lookup instr (instructions real) of
     Just res -> return res
realizeValue ana real (castDown -> Just i) = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return $ NormalValue () (const $ constant $ rv/=0)
    else return $ IntConst (fromIntegral rv)

realizeBlock :: RealizationOptions -> Analyzation -> Realization -> Ptr BasicBlock
                -> IO Realization
realizeBlock opts ana real blk = do
  name <- getNameString blk
  let latchCond = case Map.lookup blk (latchBlocks ana) of
        Just _ -> if exactPredecessors opts
                  then [\(acts,_,_) -> app and' $ [acts Map.! blk]++
                                       [ not' act |(blk',act) <- Map.toList acts
                                                  , blk'/=blk ]
                       ]
                  else [\(acts,_,_) -> acts Map.! blk]
        Nothing -> []
      normalCond = case Map.lookup blk (forwardEdges real) of
          Just incs -> incs
          Nothing -> []
      conds = latchCond++normalCond
      (act,gates1) = let (act',gates') = addGate (gateMp real)
                                         (Gate { gateTransfer = case conds of
                                                  [f] -> \inp -> f inp
                                                  _ -> \inp -> app or' [ f inp | f <- conds ]
                                               , gateAnnotation = ()
                                               , gateName = Just name })
                     in (const act',gates')
      real' = real { blockActivations = Map.insert blk act
                                        (blockActivations real)
                   , gateMp = gates1
                   , forwardEdges = Map.delete blk (forwardEdges real) }
  instrs <- getInstList blk >>= ipListToList
  foldlM (realizeInstruction opts ana) real' instrs

defineInstr' :: Analyzation -> Realization -> Ptr Instruction -> ProxyArgValue
               -> (LLVMInput -> SMTExpr UntypedValue)
               -> IO Realization
defineInstr' ana real instr tp f
  = withProxyArgValue tp $
    \(_::a) ann
    -> defineInstr ana real instr
       (NormalValue ann
        (\inp -> (castUntypedExprValue (f inp) :: SMTExpr a)))

defineInstr :: Analyzation -> Realization -> Ptr Instruction
               -> RealizedValue
               -> IO Realization
defineInstr ana real instr (NormalValue tp f) = do
  name <- getNameString instr
  let trans = case Map.lookup instr (implicitLatches ana) of
        Just (_,blk) -> case Map.lookup blk (blockActivations real) of
          Just act -> \inp@(_,_,instrs)
                      -> ite (act inp)
                         (f inp)
                         (castUntypedExprValue $ instrs Map.! instr)
        Nothing -> f
      (expr,ngates) = addGate (gateMp real)
                      (Gate { gateTransfer = trans
                            , gateAnnotation = tp
                            , gateName = Just name })
  return $ real { gateMp = ngates
                , instructions = Map.insert instr (NormalValue tp (const expr))
                                 (instructions real)
                }
defineInstr ana real instr val
  | Map.member instr (implicitLatches ana) = error "Special value is latched."
  | otherwise = return $ real { instructions = Map.insert instr val
                                               (instructions real)
                              }

realizeDefInstruction :: Analyzation -> Realization -> Ptr Instruction
                      -> IO RealizedValue
realizeDefInstruction ana real i@(castDown -> Just opInst) = do
  lhs <- getOperand opInst 0
  rhs <- getOperand opInst 1
  op <- binOpGetOpCode opInst
  tp <- valueGetType lhs >>= translateType
  flhs <- realizeValue ana real lhs
  frhs <- realizeValue ana real rhs
  case op of
   Add -> return $ NormalValue () $
          \inp -> (asSMTValue flhs inp :: SMTExpr Integer) +
                  (asSMTValue frhs inp)
   Sub -> return $ NormalValue () $
          \inp -> (asSMTValue flhs inp :: SMTExpr Integer) -
                  (asSMTValue frhs inp)
   Mul -> return $ NormalValue () $
          \inp -> (asSMTValue flhs inp :: SMTExpr Integer) *
                  (asSMTValue frhs inp)
   And -> if tp==(ProxyArgValue (undefined::Bool) ())
          then return $ NormalValue () $
               \inp -> (asSMTValue flhs inp) .&&.
                       (asSMTValue frhs inp)
          else error "And operator can't handle non-bool inputs."
   Or -> if tp==(ProxyArgValue (undefined::Bool) ())
         then return $ NormalValue () $
              \inp -> (asSMTValue flhs inp) .||.
                      (asSMTValue frhs inp)
         else (if tp==(ProxyArgValue (undefined::Integer) ())
               then return (case flhs of
                             OrList xs -> case frhs of
                               OrList ys -> OrList $ xs++ys
                               _ -> OrList $ xs++[asSMTValue frhs]
                             _ -> case frhs of
                               OrList ys -> OrList $ [asSMTValue flhs]++ys
                               _ -> OrList [asSMTValue flhs,
                                            asSMTValue frhs])
               else error "Or operator can only handle bool and int inputs.")
   Xor -> case (flhs,frhs) of
     (ExtBool l,ExtBool r) -> return $ ExtBool (\inp -> app xor
                                                        [l inp
                                                        ,r inp])
     (ExtBool l,IntConst 1) -> return $ ExtBool (\inp -> not' $ l inp)
     _ -> if tp==(ProxyArgValue (undefined::Bool) ())
          then return $ NormalValue () $
               \inp -> app xor
                       [asSMTValue flhs inp
                       ,asSMTValue frhs inp]
          else error "Xor operator can't handle non-bool inputs."
   Shl -> case frhs of
     IntConst rv
       -> return $ NormalValue () $
          \inp -> (asSMTValue flhs inp :: SMTExpr Integer)*
                  (constant $ 2^rv)
   LShr -> case frhs of
     IntConst rv
       -> return $ NormalValue () $
          \inp -> (asSMTValue flhs inp) `div'` (constant $ 2^rv)
   _ -> error $ "Unknown operator: "++show op
realizeDefInstruction ana real i@(castDown -> Just call) = do
  fname <- getFunctionName call
  case fname of
   '_':'_':'u':'n':'d':'e':'f':_ -> do
     tp <- getType i >>= translateType
     withProxyArgValue tp $
       \(_::a) ann -> return $ NormalValue ann $
                      \(_,inp,_) -> castUntypedExprValue (inp Map.! i) :: SMTExpr a
realizeDefInstruction ana real i@(castDown -> Just icmp) = do
  op <- getICmpOp icmp
  lhs <- getOperand icmp 0 >>= realizeValue ana real
  rhs <- getOperand icmp 1 >>= realizeValue ana real
  return $ case op of
   I_EQ -> case (lhs,rhs) of
     (OrList xs,IntConst 0) -> NormalValue () (\inp -> app and' [ (x inp) .==. 0 | x <- xs ])
     (IntConst 0,OrList xs) -> NormalValue () (\inp -> app and' [ (x inp) .==. 0 | x <- xs ])
     _ -> withSMTValue lhs $
          \_ lhs' -> NormalValue () (\inp -> (lhs' inp) .==. (asSMTValue rhs inp))
   I_NE -> case (lhs,rhs) of
     (OrList xs,IntConst 0) -> NormalValue () (\inp -> app or' [ not' $ (x inp) .==. 0
                                                               | x <- xs ])
     (IntConst 0,OrList xs) -> NormalValue () (\inp -> app or' [ not' $ (x inp) .==. 0
                                                               | x <- xs ])
     _ -> withSMTValue lhs $
          \_ lhs' -> NormalValue () (\inp -> not' $ (lhs' inp) .==. (asSMTValue rhs inp))
   I_SGE -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .>=.
                    (asSMTValue rhs inp)
   I_UGE -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .>=.
                    (asSMTValue rhs inp)
   I_SGT -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .>.
                    (asSMTValue rhs inp)
   I_UGT -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .>.
                    (asSMTValue rhs inp)
   I_SLE -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .<=.
                    (asSMTValue rhs inp)
   I_ULE -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .<=.
                    (asSMTValue rhs inp)
   I_SLT -> case (lhs,rhs) of
     (OrList xs,IntConst 0) -> NormalValue () (\inp -> app and' [ (x inp) .<. 0
                                                                | x <- xs ])
     _ -> NormalValue () $
          \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .<.
                  (asSMTValue rhs inp)
   I_ULT -> NormalValue () $
            \inp -> (asSMTValue lhs inp :: SMTExpr Integer) .<.
                    (asSMTValue rhs inp)
realizeDefInstruction ana real i@(castDown -> Just (zext::Ptr ZExtInst)) = do
  op <- getOperand zext 0
  tp <- valueGetType op >>= translateType
  fop <- realizeValue ana real op
  if tp==(ProxyArgValue (undefined::Bool) ())
    then return $ ExtBool (asSMTValue fop)
    else (withProxyArgValue tp $
          \(_::a) ann -> return $ NormalValue ann $
                         \inp -> asSMTValue fop inp :: SMTExpr a)
realizeDefInstruction ana real i@(castDown -> Just (trunc::Ptr TruncInst)) = do
  op <- getOperand trunc 0
  tp <- valueGetType i >>= translateType
  fop <- realizeValue ana real op
  if tp==(ProxyArgValue (undefined::Bool) ())
    then return $ NormalValue () $
         \inp -> (asSMTValue fop inp) .==. (constant (1::Integer))
    else return fop
realizeDefInstruction ana real i@(castDown -> Just select) = do
  cond <- selectInstGetCondition select >>= realizeValue ana real
  tVal <- selectInstGetTrueValue select
  tp <- valueGetType tVal >>= translateType
  tVal' <- realizeValue ana real tVal
  fVal' <- selectInstGetFalseValue select >>= realizeValue ana real
  withProxyArgValue tp $
    \(_::a) ann
    -> return $ NormalValue ann $
       \inp -> ite (asSMTValue cond inp)
               (asSMTValue tVal' inp :: SMTExpr a)
               (asSMTValue fVal' inp)
realizeDefInstruction ana real i@(castDown -> Just phi)
  = case Map.lookup i (explicitLatches ana) of
     Just (tp,recPhis,phis) -> do
       trg <- instructionGetParent i
       let edges = case Map.lookup trg (edgeActivations real) of
             Just ed -> ed
       num <- phiNodeGetNumIncomingValues phi
       phis' <- mapM (\(blk,val) -> do
                         val' <- realizeValue ana real val
                         let edge = case Map.lookup blk edges of
                               Just act -> act
                         return (edge,val')
                     ) phis
       withProxyArgValue tp $
         \(_::a) ann
          -> let mkITE [(_,val)] inp
                   | null recPhis = asSMTValue val inp
                 mkITE [] (_,_,instrs) = castUntypedExprValue (instrs Map.! i)
                 mkITE ((cond,val):xs) inp
                   = ite (cond inp)
                     (asSMTValue val inp)
                     (mkITE xs inp)
             in return $ NormalValue ann $
                \inp -> mkITE phis' inp :: SMTExpr a
realizeDefInstruction ana real i = do
  valueDump i
  error "Unknown instruction"

realizeInstruction :: RealizationOptions -> Analyzation -> Realization -> Ptr Instruction -> IO Realization
realizeInstruction opts ana real i@(castDown -> Just brInst) = do
  src <- instructionGetParent brInst
  srcName <- getNameString src
  is_cond <- branchInstIsConditional brInst
  let act = case Map.lookup src (blockActivations real) of
        Just a -> a
      restr inp = if useErrorState opts
                  then (case Map.lookup src (asserts real) of
                         Just conds -> [ c inp | c <- conds ]
                         Nothing -> [])
                  else []
  if is_cond
    then (do
             ifTrue <- terminatorInstGetSuccessor brInst 0
             ifTrueName <- getNameString ifTrue
             ifFalse <- terminatorInstGetSuccessor brInst 1
             ifFalseName <- getNameString ifFalse
             NormalValue _ (cast -> Just cond) <- branchInstGetCondition brInst
                                                  >>= realizeValue ana real
             let tCond inp = app and' $ [act inp,cond inp]++(restr inp)
                 fCond inp = app and' $ [act inp,not' $ cond inp]++(restr inp)
                 (tGate,gates1) = addGate (gateMp real)
                                  (Gate { gateTransfer = tCond
                                        , gateAnnotation = ()
                                        , gateName = Just $ srcName++"."++ifTrueName })
                 (fGate,gates2) = addGate gates1
                                  (Gate { gateTransfer = fCond
                                        , gateAnnotation = ()
                                        , gateName = Just $ srcName++"."++ifFalseName })
             return $ real { edgeActivations = Map.insertWith Map.union
                                               ifTrue
                                               (Map.singleton src (const tGate)) $
                                               Map.insertWith Map.union
                                               ifFalse
                                               (Map.singleton src (const fGate)) $
                                               edgeActivations real
                           , forwardEdges = Map.insertWith (++)
                                            ifTrue [const tGate] $
                                            Map.insertWith (++)
                                            ifFalse [const fGate] $
                                            forwardEdges real
                           , gateMp = gates2 })
    else (do
             trg <- terminatorInstGetSuccessor brInst 0
             return $ real { edgeActivations = Map.insertWith Map.union
                                               trg
                                               (Map.singleton src act)
                                               (edgeActivations real)
                           , forwardEdges = Map.insertWith (++)
                                            trg [\inp -> case restr inp of
                                                          [] -> act inp
                                                          xs -> app and' $ [act inp]++xs]
                                            (forwardEdges real)
                           })
realizeInstruction opts ana real i@(castDown -> Just call) = do
  blk <- instructionGetParent i
  let act = case Map.lookup blk (blockActivations real) of
        Just a -> a
  fname <- getFunctionName call
  case fname of
   '_':'_':'u':'n':'d':'e':'f':_ -> do
     tp <- getType i >>= translateType
     defineInstr' ana (real { inputs = Map.insert i tp (inputs real)
                            }) i tp (\(_,inp,_) -> inp Map.! i)
   "assert" -> do
     NormalValue _ (cast -> Just cond) <- callInstGetArgOperand call 0
                                          >>= realizeValue ana real
     return $ real { asserts = Map.insertWith (++)
                               blk [cond]
                               (asserts real) }
   "assume" -> do
     NormalValue _ (cast -> Just cond) <- callInstGetArgOperand call 0
                                          >>= realizeValue ana real
     return $ real { assumes = (\inp -> (act inp) .=>. (cond inp)):
                               (assumes real) }
   _ -> error $ "Unknown function "++fname
realizeInstruction opts ana real i@(castDown -> Just ret) = do
  rval <- returnInstGetReturnValue ret
  return real
realizeInstruction opts ana real (castDown -> Just sw) = do
  src <- instructionGetParent sw
  srcName <- getNameString src
  NormalValue _ (cast -> Just cond) <- switchInstGetCondition sw
                                       >>= realizeValue ana real
  def <- switchInstGetDefaultDest sw
  defName <- getNameString def
  cases <- switchInstGetCases sw >>=
           mapM (\(val,trg) -> do
                    APInt _ val' <- constantIntGetValue val >>= peek
                    return (val',trg))
  let act = case Map.lookup src (blockActivations real) of
        Just a -> a
      (defEdge,ngates) = addGate (gateMp real)
                         (Gate { gateTransfer = \inp -> app and' ((act inp):
                                                                  [ not' $
                                                                    (cond inp)
                                                                    .==.
                                                                    (constant val)
                                                                  | (val,_) <- cases ])
                               , gateAnnotation = ()
                               , gateName = Just $ srcName++"."++defName
                               })
  foldlM (\real (val,trg) -> do
             trgName <- getNameString trg
             let (edge,ngates) = addGate (gateMp real)
                                 (Gate { gateTransfer = \inp -> (act inp) .&&.
                                                                ((cond inp)
                                                                 .==.
                                                                 (constant val))
                                       , gateAnnotation = ()
                                       , gateName = Just $ srcName++"."++trgName })
             return $ real { gateMp = ngates
                           , edgeActivations = Map.insertWith Map.union
                                               trg
                                               (Map.singleton src (const edge))
                                               (edgeActivations real)
                           , forwardEdges = Map.insertWith (++)
                                            trg [const edge]
                                            (forwardEdges real)
                           }
         ) (real { gateMp = ngates
                 , edgeActivations = Map.insertWith Map.union
                                     def
                                     (Map.singleton src (const defEdge))
                                     (edgeActivations real)
                 , forwardEdges = Map.insertWith (++)
                                  def [const defEdge]
                                  (forwardEdges real) }) cases
realizeInstruction opts ana real i = do
  res <- realizeDefInstruction ana real i
  defineInstr ana real i res

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

getModel :: RealizationOptions -> Ptr Function -> IO RealizedBlocks
getModel opts fun = do
  gr <- blockGraph fun
  blks <- getBasicBlockList fun >>= ipListToList
  ana <- foldlM analyzeBlock (Analyzation { instructionState = Map.empty
                                          , implicitLatches = Map.empty
                                          , explicitLatches = Map.empty
                                          , latchBlocks = if useErrorState opts
                                                          then Map.singleton nullPtr ()
                                                          else Map.empty
                                          , analyzedBlocks = Set.empty
                                          , blkGraph = gr }) blks
  real <- realizeFunction opts ana fun
  getModel' opts (head blks) ana real

getModel' :: RealizationOptions -> Ptr BasicBlock -> Analyzation -> Realization
             -> IO RealizedBlocks
getModel' opts init ana real = do
  (phiInstrs,real2) <- runStateT
                       (Map.traverseWithKey
                        (\i (tp,phis,_)
                         -> case phis of
                             [] -> return Nothing
                             _ -> do
                               creal <- get
                               trg <- lift $ instructionGetParent i
                               let trg_act = case Map.lookup trg (blockActivations creal) of
                                     Just a -> a
                                   is_implicit = case Map.lookup i (implicitLatches ana) of
                                     Just _ -> True
                                     Nothing -> False
                               name <- lift $ getNameString i
                               withProxyArgValue tp $
                                 \(_::a) ann -> do
                                   phis' <- mapM (\(src,val) -> do
                                                     let act = case Map.lookup trg (edgeActivations creal) of
                                                           Just acts -> case Map.lookup src acts of
                                                             Just a -> a
                                                     val' <- lift $ realizeValue ana creal val
                                                     return (act,asSMTValue val')
                                                 ) phis
                                   let trg_val = case Map.lookup i (instructions creal) of
                                         Just (NormalValue _ (cast -> Just v)) -> v :: LLVMInput -> SMTExpr a
                                       (expr,ngates) = addGate (gateMp creal)
                                                       (Gate { gateTransfer = mkITE (if is_implicit
                                                                                     then Just (trg_act,trg_val)
                                                                                     else Nothing)
                                                                              i phis' :: LLVMInput -> SMTExpr a
                                                             , gateAnnotation = ann
                                                             , gateName = Just name })
                                   put $ creal { gateMp = ngates }
                                   return $ Just (tp,const $ UntypedExprValue expr)
                        ) (explicitLatches ana)
                       ) real1
  let phiInstrs' = Map.mapMaybe id phiInstrs
  latchInstrs' <- Map.traverseWithKey (\i val -> do
                                          tp <- getType i >>= translateType
                                          return (tp,val)
                                      ) latchInstrs
  return $ RealizedBlocks { realizedLatchBlocks = latchBlks
                          , realizedLatches = Map.union phiInstrs' latchInstrs'
                          , realizedInputs = inputs real2
                          , realizedGates = gateMp real2
                          , realizedAssumes = assumes real2
                          , realizedAsserts = rasserts
                          , realizedInit = init
                          }
  where
    (gates1,latchBlks) = Map.mapAccumWithKey
                         (\gates blk _
                           -> if blk==nullPtr && useErrorState opts
                              then (let (act,gates') = addGate gates
                                                       (Gate { gateTransfer = \inp -> app or' ([ not' (c inp)
                                                                                               | c <- allAsserts ]++
                                                                                               [((blockActivations real) Map.! nullPtr) inp])
                                                             , gateAnnotation = ()
                                                             , gateName = Just "err" })
                                    in (gates',const act))
                              else case Map.lookup blk (forwardEdges real) of
                                    Nothing -> (gates,const $ constant False)
                                    Just incs -> let name = unsafePerformIO $ getNameString blk
                                                     (act',gates') = addGate gates
                                                                     (Gate { gateTransfer = case incs of
                                                                              [f] -> f
                                                                              _ -> \inp -> app or' [ f inp | f <- incs ]
                                                                           , gateAnnotation = ()
                                                                           , gateName = Just name })
                                                 in (gates',const act')
                         ) (gateMp real) (latchBlocks ana)
    real1 = real { gateMp = gates1 }
    latchInstrs = fmap (\val -> case val of
                         NormalValue _ v -> \inp -> UntypedExprValue (v inp)
                       ) $ Map.intersection (instructions real1) (implicitLatches ana)
    mkITE (Just (trg_act,trg_val)) i [] inp@(_,_,instrs)
      = ite (trg_act inp)
        (trg_val inp)
        (castUntypedExprValue (instrs Map.! i))
    mkITE Nothing i [(_,val)] inp = val inp
    mkITE end i ((cond,val):xs) inp = ite (cond inp)
                                      (val inp)
                                      (mkITE end i xs inp)
    rasserts = if useErrorState opts
               then (case Map.lookup nullPtr (blockActivations real1) of
                      Just act -> [\inp -> not' (act inp)])
               else allAsserts
    allAsserts = concat $
                 Map.mapWithKey
                 (\blk ass
                  -> case Map.lookup blk (blockActivations real1) of
                      Just act -> if null ass
                                  then [\inp -> not' (act inp)]
                                  else [\inp -> (act inp) .=>. (a inp)
                                       | a <- ass ]
                 ) (asserts real1)
-- Interface starts here:

createBlockVars :: String -> RealizedBlocks -> SMT LatchActs
createBlockVars pre st
  = sequence $ Map.mapWithKey
    (\blk _ -> do
        name <- if blk==nullPtr
                then return "err"
                else liftIO $ getNameString blk
        varNamed (pre++"L."++name)
    ) (realizedLatchBlocks st)

-- | Encode the fact that only exactly one block may be active
blockConstraint :: LatchActs -> SMTExpr Bool
blockConstraint blks
  = app or' $
    fmap (app and') $
    exactlyOne [] (Map.elems blks)
  where
    exactlyOne prev [x] = [prev++[x]]
    exactlyOne prev (x:xs)
      = (prev++(x:(fmap not' xs))):
        (exactlyOne (prev++[not' x]) xs)

createInstrVars :: String -> RealizedBlocks -> SMT ValueMap
createInstrVars pre st
  = sequence $ Map.mapWithKey
    (\instr (ann,_) -> do
        name <- liftIO $ do
              hn <- hasName instr
              n <- if hn
                   then getNameString instr
                   else return "instr"
              return (pre++"L."++n)
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
              return (pre++"I."++n)
        varNamedAnn name ann
    ) (realizedInputs st)

declareOutputActs :: (Monad m,Functor m) => RealizedBlocks -> RealizedGates -> LLVMInput
                     -> SMT' m (LatchActs
                               ,RealizedGates)
declareOutputActs st real inp
  = runStateT
    (Map.traverseWithKey
     (\trg act -> do
         real <- get
         (expr,nreal) <- lift $ declareGate (act inp) real
                         (realizedGates st) inp
         put nreal
         return expr
     ) (realizedLatchBlocks st)
    ) real

declareOutputInstrs :: (Monad m,Functor m) => RealizedBlocks -> RealizedGates -> LLVMInput
                       -> SMT' m (ValueMap
                                 ,RealizedGates)
declareOutputInstrs st real inp
  = runStateT
    (Map.traverseWithKey
     (\instr (tp,val) -> do
         real <- get
         (expr,nreal) <- lift $ declareGate (val inp) real
                         (realizedGates st) inp
         put nreal
         return expr
     ) (realizedLatches st)
    ) real

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
  = app and' [ if blk==realizedInit st
               then act
               else not' act
             | (blk,act) <- Map.toList acts ]

blockAnnotation :: RealizedBlocks -> ArgAnnotation LatchActs
blockAnnotation st = fmap (const ()) (realizedLatchBlocks st)

latchAnnotation :: RealizedBlocks -> ArgAnnotation ValueMap
latchAnnotation st = fmap fst (realizedLatches st)

getConcreteValues :: Monad m => RealizedBlocks -> LLVMInput -> SMT' m ConcreteValues
getConcreteValues st (acts,inps,instrs) = do
  acts' <- mapM getValue acts
  blk <- case [ blk
              | (blk,act) <- Map.toList acts'
              , act ] of
          [] -> error "Realization.getConcreteValues: No latch block is active."
          [x] -> return x
          _ -> error "Realization.getConcreteValues: More than one block is active."
  vals <- concretizeMap instrs (fmap fst $ realizedLatches st)
  inps' <- concretizeMap inps (realizedInputs st)
  return $ ConcreteValues { block = blk
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

extractBlock :: Map (Ptr BasicBlock) Bool -> Ptr BasicBlock
extractBlock mp = case blks of
  [x] -> x
  [] -> error "No basic block is active in state."
  _ -> error "More than one basic block is active in state."
  where
    blks = [ blk | (blk,act) <- Map.toList mp
                 , act ]

getProgram :: String -> String -> IO (Ptr Function)
getProgram entry file = do
  Just buf <- getFileMemoryBufferSimple file
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  applyOptimizations mod entry
  --moduleDump mod
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
  = [APass createTypeBasedAliasAnalysisPass
    --,APass createScopedNoAliasAAPass
    ,APass createBasicAliasAnalysisPass
    ,APass createIPSCCPPass
    ,APass createGlobalOptimizerPass
    ,APass createDeadArgEliminationPass
    ,APass createInstructionCombiningPass
    ,APass createCFGSimplificationPass
    ,APass createPruneEHPass
    ,APass (do
               m <- newCString entry
               arr <- newArray [m]
               export_list <- newArrayRef arr 1
               --export_list <- newArrayRefEmpty
               createInternalizePass export_list)
    ,APass (createFunctionInliningPass 100)
    --,APass (createArgumentPromotionPass 0)
    ,APass (createScalarReplAggregatesPass (-1) False (-1) (-1) (-1))
    ,APass createEarlyCSEPass
    ,APass createJumpThreadingPass
    ,APass createCorrelatedValuePropagationPass
    ,APass createCFGSimplificationPass
    ,APass createInstructionCombiningPass
    ,APass createTailCallEliminationPass
    ,APass createCFGSimplificationPass
    ,APass createReassociatePass
    --,APass createLoopRotatePass
    ,APass createLICMPass
    --,APass (createLoopUnswitchPass False)
    ,APass createInstructionCombiningPass
    --,APass createIndVarSimplifyPass
    ,APass createLoopIdiomPass
    ,APass createLoopDeletionPass
    --,APass createSimpleLoopUnrollPass
    ,APass (createGVNPass False)
    ,APass createMemCpyOptPass
    ,APass createSCCPPass
    ,APass createInstructionCombiningPass
    ,APass createJumpThreadingPass
    ,APass createCorrelatedValuePropagationPass
    ,APass createDeadStoreEliminationPass
    ,APass createAggressiveDCEPass
    ,APass createCFGSimplificationPass
    ,APass createInstructionCombiningPass
    ,APass createBarrierNoopPass
    ,APass createCFGSimplificationPass
    ,APass createInstructionCombiningPass
    --,APass (createLoopUnrollPass (-1) (-1) (-1) (-1))
    --,APass createAlignmentFromAssumptionsPass
    ,APass createGlobalDCEPass
    ,APass createConstantMergePass
    ,APass createInstructionNamerPass]

instance Show ConcreteValues where
  show cv = unsafePerformIO $ do
    blk <- do
      isNamed <- hasName (block cv)
      if isNamed
        then getNameString (block cv)
        else return $ show (block cv)
    vals <- mapM (\(instr,val) -> do
                     instrName <- do
                       instrHasName <- hasName instr
                       if instrHasName
                         then getNameString instr
                         else return $ show instr
                     return $ instrName++"="++renderVal val
                 ) (Map.toList $ latchValues cv)
    inps <- mapM (\(instr,val) -> do
                     instrName <- do
                       instrHasName <- hasName instr
                       if instrHasName
                         then getNameString instr
                         else return $ show instr
                     return $ instrName++"="++renderVal val
                 ) (Map.toList $ inputValues cv)
    return $ "("++blk++"|"++
      concat (intersperse "," vals)++"|"++
      concat (intersperse "," inps)++")"
    where
      renderVal (IntValue n) = show n
      renderVal (BoolValue n) = show n

asSMTValue :: SMTValue a => RealizedValue -> LLVMInput -> SMTExpr a
asSMTValue val = withSMTValue val (\_ f -> case cast f of
                                    Just f' -> f')

withSMTValue :: RealizedValue
             -> (forall a. SMTValue a => SMTAnnotation a -> (LLVMInput -> SMTExpr a) -> b)
             -> b
withSMTValue (NormalValue ann f) app = app ann f
withSMTValue (IntConst x) app = app () (const $ constant x)
withSMTValue (OrList _) _ = error "Or operator can only be applied to boolean values."
withSMTValue (ExtBool f) app = app () (\inp -> ite (f inp)
                                               (constant (1::Integer))
                                               (constant 0))
