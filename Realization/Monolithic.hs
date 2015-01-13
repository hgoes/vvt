{-# LANGUAGE ViewPatterns,RankNTypes,ScopedTypeVariables,PackageImports,GADTs,FlexibleInstances,
             TypeFamilies, MultiParamTypeClasses,DeriveDataTypeable #-}
module Realization.Monolithic where

import Realization
import Realization.Common
import Gates
import RSM
--import KarrLLVM
import Karr

import Language.SMTLib2 hiding (getModel)
import Language.SMTLib2.Internals hiding (Value)
import Language.SMTLib2.Pipe (createSMTPipe)
import Foreign.Ptr
import LLVM.FFI hiding (Vector)
import qualified Data.Graph.Inductive as Gr
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (foldlM,concat)
import Foreign.Storable (peek)
import "mtl" Control.Monad.State (StateT,runStateT,get,put,lift,liftIO,MonadIO)
import Control.Monad (when)
import System.IO.Unsafe
import Data.Traversable (sequence,traverse,mapM)
import Prelude hiding (sequence,mapM,concat)
import Data.List (intersperse,sortBy)
import Data.Either (partitionEithers)
import Data.Typeable (cast)
import Data.Ord (comparing)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import qualified Data.IntMap as IMap
import System.IO (withFile,IOMode(ReadMode))

import Language.SMTLib2.Debug

type ValueMap = Map (Ptr Instruction) SymInstr

type LatchActs = Map (Ptr BasicBlock) (SMTExpr Bool)

data LatchState = Defined (Ptr BasicBlock)
                | Latched
                | DefinedWhen (Ptr BasicBlock)

data Analyzation = Analyzation { instructionState :: Map (Ptr Instruction) LatchState
                               , implicitLatches :: Map (Ptr Instruction) (InstrType,
                                                                           Ptr BasicBlock)
                               , explicitLatches :: Map (Ptr Instruction)
                                                    (InstrType,
                                                     [(Ptr BasicBlock,Ptr Value)],
                                                     [(Ptr BasicBlock,Ptr Value)])
                               , latchBlocks :: Map (Ptr BasicBlock) ()
                               , analyzedBlocks :: Set (Ptr BasicBlock)
                               , blkGraph :: BlockGraph
                               }

-- | Activation vars, inputs and latch instructions
type LLVMInput = (LatchActs,ValueMap,ValueMap,Maybe [SMTExpr Integer])

data Realization = Realization { edgeActivations :: Map (Ptr BasicBlock)
                                                    (Map (Ptr BasicBlock)
                                                     (LLVMInput -> SMTExpr Bool))
                               , blockActivations :: Map (Ptr BasicBlock)
                                                     (LLVMInput -> SMTExpr Bool)
                               , instructions :: Map (Ptr Instruction)
                                                 (RealizedValue LLVMInput)
                               , inputs :: Map (Ptr Instruction) InstrType
                               , forwardEdges :: Map (Ptr BasicBlock) [LLVMInput -> SMTExpr Bool]
                               , asserts :: Map (Ptr BasicBlock) [LLVMInput -> SMTExpr Bool]
                               , assumes :: [LLVMInput -> SMTExpr Bool]
                               , gateMp :: GateMap LLVMInput
                               }

data BlockGraph = BlockGraph { nodeMap :: Map (Ptr BasicBlock) Gr.Node
                             , dependencies :: Gr.Gr (Ptr BasicBlock) ()
                             }

data RealizedBlocks = RealizedBlocks { realizedLatchBlocks :: Map (Ptr BasicBlock)
                                                              (LLVMInput -> SMTExpr Bool)
                                     , realizedLatches :: Map (Ptr Instruction)
                                                          (InstrType,
                                                           LLVMInput -> SymInstr)
                                     , realizedInputs :: Map (Ptr Instruction) InstrType
                                     , realizedGates :: GateMap LLVMInput
                                     , realizedAssumes :: [LLVMInput -> SMTExpr Bool]
                                     , realizedAsserts :: [LLVMInput -> SMTExpr Bool]
                                     , realizedInit :: Ptr BasicBlock
                                     , realizedLinear :: Maybe (Vector (Ptr Instruction))
                                     , realizedKarr :: [(Ptr BasicBlock,[([(Ptr Instruction,Integer)],Integer)])]
                                     , realizedExtraPredicates :: [(LatchActs,ValueMap) -> SMTExpr Bool]
                                     }

data ConcreteValues = ConcreteValues { block :: Ptr BasicBlock
                                     , latchValues :: Map (Ptr Instruction) ValInstr
                                     , inputValues :: Map (Ptr Instruction) ValInstr
                                     }

type ErrorTrace = [ConcreteValues]

data RealizationOptions = RealizationOptions { useErrorState :: Bool
                                             , exactPredecessors :: Bool
                                             , optimize :: Bool
                                             , eliminateDiv :: Bool
                                             , integerEncoding :: IntegerEncoding LLVMInput
                                             , forceNondet :: Ptr Instruction -> Bool
                                             , useKarr :: Bool
                                             , extraPredicates :: Maybe String
                                             , verbosity :: Int
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

analyzeBlock :: RealizationOptions -> Analyzation -> Ptr BasicBlock -> IO Analyzation
analyzeBlock opts ana blk = do
  instrs <- getInstList blk >>= ipListToList
  foldlM (analyzeInstruction opts backedges) ana' instrs
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

translateType :: IntegerEncoding LLVMInput -> Ptr Type -> IO InstrType
translateType enc (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return TpBool
    _ -> case enc of
          EncInt -> return TpInteger
          EncLin l _ -> return $ TpLinear $ Vec.length l
translateType _ tp = do
  typeDump tp
  error "Can't translate type"

analyzeValue :: RealizationOptions -> Analyzation -> Ptr Value -> IO Analyzation
analyzeValue opts ana (castDown -> Just instr)
  = case Map.lookup instr (instructionState ana) of
  Just (Defined _) -> return ana
  Just (DefinedWhen blk) -> do
    tp <- getType instr >>= translateType (integerEncoding opts)
    return $ ana { implicitLatches = Map.insert instr (tp,blk)
                                     (implicitLatches ana)
                 }
  Nothing -> return ana
  {-Nothing -> return $ ana { instructionState = Map.insert instr Latched
                                               (instructionState ana)
                          , implicitLatches = Map.insert instr ()
                                              (implicitLatches ana)
                          }-}
analyzeValue _ ana _ = return ana

analyzeInstruction :: RealizationOptions -> Set (Ptr BasicBlock) -> Analyzation -> Ptr Instruction -> IO Analyzation
analyzeInstruction opts backedges ana i@(castDown -> Just phi) = do
  blk <- instructionGetParent i
  numPhi <- phiNodeGetNumIncomingValues phi
  phis <- mapM (\n -> do
                   blk <- phiNodeGetIncomingBlock phi n
                   val <- phiNodeGetIncomingValue phi n
                   return (blk,val)
               ) [0..numPhi-1]
  ana1 <- foldlM (analyzeValue opts) ana (fmap snd phis)
  let (phis1,phis2) = partitionEithers $
                      fmap (\(blk,val) -> if Set.member blk backedges
                                          then Left (blk,val)
                                          else Right (blk,val)
                           ) phis
  tp <- getType phi >>= translateType (integerEncoding opts)
  return $ ana1 { explicitLatches = Map.insert i (tp,phis1,phis2)
                                    (explicitLatches ana1)
                , instructionState = Map.insert i (Defined blk)
                                     (instructionState ana1)
                }
analyzeInstruction opts _ ana i = do
  blk <- instructionGetParent i
  numOps <- getNumOperands i
  ops <- mapM (getOperand i) [0..numOps-1]
  ana1 <- foldlM (analyzeValue opts) ana ops
  return $ ana1 { instructionState = Map.insert i (Defined blk) (instructionState ana1) }

realizeFunction :: RealizationOptions -> Analyzation -> Ptr Function
                   -> IO Realization
realizeFunction opts ana fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  let initInstrs1 = Map.mapWithKey
                    (\i (tp,_)
                     -> NormalValue tp (\(_,_,instrs,_)
                                        -> instrs Map.! i)
                    ) (implicitLatches ana)
      initInstrs2 = Map.mapWithKey
                    (\i (tp,_,_)
                     -> NormalValue tp (\(_,_,instrs,_)
                                        -> instrs Map.! i)
                    ) (explicitLatches ana)
      initInstrs = Map.union initInstrs1 initInstrs2
      real = Realization { edgeActivations = Map.empty
                         , blockActivations = if useErrorState opts
                                              then Map.singleton nullPtr
                                                   (if exactPredecessors opts
                                                    then (\(acts,_,_,_) -> app and' $ [acts Map.! nullPtr]++
                                                                           [ not' act
                                                                           | (blk,act) <- Map.toList acts
                                                                           , blk/=nullPtr ]
                                                         )
                                                    else (\(acts,_,_,_) -> acts Map.! nullPtr))
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
                -> IO (RealizedValue LLVMInput)
realizeValue ana real (castDown -> Just instr)
  = case Map.lookup instr (instructions real) of
     Just res -> return res
     Nothing -> do
       iname <- getNameString instr
       error $ "Cannot find value of instruction "++iname
realizeValue ana real (castDown -> Just i) = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return $ NormalValue TpBool (const $ SymBool $ constant $ rv/=0)
    else return $ IntConst (fromIntegral rv)
realizeValue ana real (castDown -> Just undef) = do
  tp <- getType (undef::Ptr UndefValue)
  defaultValue tp
  where
    defaultValue (castDown -> Just itp) = do
      bw <- getBitWidth itp
      if bw==1
        then return $ NormalValue TpBool (const $ SymBool $ constant False)
        else return $ IntConst 0

realizeBlock :: RealizationOptions -> Analyzation -> Realization -> Ptr BasicBlock
                -> IO Realization
realizeBlock opts ana real blk = do
  name <- getNameString blk
  let latchCond = case Map.lookup blk (latchBlocks ana) of
        Just _ -> if exactPredecessors opts
                  then [\(acts,_,_,_) -> app and' $ [acts Map.! blk]++
                                         [ not' act |(blk',act) <- Map.toList acts
                                                    , blk'/=blk ]
                       ]
                  else [\(acts,_,_,_) -> acts Map.! blk]
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

defineInstr' :: RealizationOptions
             -> Analyzation -> Realization -> Ptr Instruction -> InstrType
             -> (LLVMInput -> SymInstr)
             -> IO Realization
defineInstr' opts ana real instr tp f
  = defineInstr opts ana real instr (NormalValue tp f)

defineInstr :: RealizationOptions
               -> Analyzation -> Realization -> Ptr Instruction
               -> RealizedValue LLVMInput
               -> IO Realization
defineInstr opts ana real instr (NormalValue tp f) = do
  name <- getNameString instr
  let trans = case Map.lookup instr (implicitLatches ana) of
        Just (_,blk) -> case Map.lookup blk (blockActivations real) of
          Just act -> \inp@(_,_,instrs,_)
                      -> symITE (act inp)
                         (f inp)
                         (instrs Map.! instr)
        Nothing -> f
      (expr,ngates) = addSymGate (gateMp real) tp trans (Just name)
  return $ real { gateMp = ngates
                , instructions = Map.insert instr (NormalValue tp (const expr))
                                 (instructions real)
                }
defineInstr opts ana real instr val
  | Map.member instr (implicitLatches ana)
    = let (tp,f) = toSMTValue val (integerEncoding opts)
      in defineInstr opts ana real instr (NormalValue tp f)
  | otherwise = return $ real { instructions = Map.insert instr val
                                               (instructions real)
                              }

realizeDefInstruction :: RealizationOptions
                      -> Analyzation -> Realization -> Ptr Instruction
                      -> IO (RealizedValue LLVMInput)
realizeDefInstruction opts ana real i@(castDown -> Just opInst) = do
  lhs <- getOperand opInst 0
  rhs <- getOperand opInst 1
  op <- binOpGetOpCode opInst
  tp <- valueGetType lhs >>= translateType (integerEncoding opts)
  flhs <- realizeValue ana real lhs
  frhs <- realizeValue ana real rhs
  case op of
   Add -> let (tp,lhs') = toSMTValue flhs (integerEncoding opts)
              rhs' = asSMTValue frhs (integerEncoding opts)
          in return $ NormalValue tp $
             \inp -> symAdd (lhs' inp) (rhs' inp)
   Sub -> let (tp,lhs') = toSMTValue flhs (integerEncoding opts)
              rhs' = asSMTValue frhs (integerEncoding opts)
          in return $ NormalValue tp $
             \inp -> symSub (lhs' inp) (rhs' inp)
   Mul -> case integerEncoding opts of
     EncInt -> return $ NormalValue TpInteger $
               \inp -> SymInteger $ (symInt $ asSMTValue flhs EncInt inp) *
                       (symInt $ asSMTValue frhs EncInt inp)
     EncLin l _ -> case flhs of
       IntConst c -> return $ NormalValue (TpLinear $ Vec.length l) $
                     \inp -> let SymLinear v1 c1 = asSMTValue frhs (integerEncoding opts) inp
                             in SymLinear (fmap (*(constant c)) v1) (c1*(constant c))
       _ -> case frhs of
         IntConst c -> return $ NormalValue (TpLinear $ Vec.length l) $
                       \inp -> let SymLinear v1 c1 = asSMTValue flhs (integerEncoding opts) inp
                               in SymLinear (fmap (*(constant c)) v1) (c1*(constant c))
         _ -> error $ "Non-linear operation"
   And -> if tp==TpBool
          then return $ NormalValue TpBool $
               \inp -> SymBool $ (symBool $ asSMTValue flhs (integerEncoding opts) inp) .&&.
                       (symBool $ asSMTValue frhs (integerEncoding opts) inp)
          else error "And operator can't handle non-bool inputs."
   Or -> if tp==TpBool
         then return $ NormalValue TpBool $
              \inp -> SymBool $ (symBool $ asSMTValue flhs (integerEncoding opts) inp) .||.
                      (symBool $ asSMTValue frhs (integerEncoding opts) inp)
         else return (case flhs of
                       OrList xs -> case frhs of
                         OrList ys -> OrList $ xs++ys
                         _ -> OrList $ xs++[asSMTValue frhs (integerEncoding opts)]
                       _ -> case frhs of
                         OrList ys -> OrList $ [asSMTValue flhs (integerEncoding opts)]++ys
                         _ -> OrList [asSMTValue flhs (integerEncoding opts),
                                      asSMTValue frhs (integerEncoding opts)])
   Xor -> case (flhs,frhs) of
     (ExtBool l,ExtBool r) -> return $ ExtBool (\inp -> app xor
                                                        [l inp
                                                        ,r inp])
     (ExtBool l,IntConst 1) -> return $ ExtBool (\inp -> not' $ l inp)
     _ -> if tp==TpBool
          then return $ NormalValue TpBool $
               \inp -> SymBool $ app xor
                       [symBool $ asSMTValue flhs (integerEncoding opts) inp
                       ,symBool $ asSMTValue frhs (integerEncoding opts) inp]
          else error "Xor operator can't handle non-bool inputs."
   Shl -> case frhs of
     IntConst rv
       -> case integerEncoding opts of
           EncInt -> return $ NormalValue TpInteger $
                     \inp -> SymInteger $ (symInt $ asSMTValue flhs (integerEncoding opts) inp)*
                             (constant $ 2^rv)
           EncLin l extr -> return $ NormalValue (TpLinear $ Vec.length l) $
                            \inp -> let SymLinear v1 c1 = asSMTValue flhs (EncLin l extr) inp
                                    in SymLinear (fmap (*(constant $ 2^rv)) v1)
                                       (c1*(constant $ 2^rv))
   LShr -> case frhs of
     IntConst rv
       -> case integerEncoding opts of
           EncInt -> return $ NormalValue TpInteger $
                     \inp -> SymInteger $ (symInt $ asSMTValue flhs EncInt inp) `div'`
                             (constant $ 2^rv)
   _ -> error $ "Unknown operator: "++show op
realizeDefInstruction opts ana real i@(castDown -> Just call) = do
  fname <- getFunctionName call
  case fname of
   '_':'_':'n':'o':'n':'d':'e':'t':_ -> do
     tp <- getType i >>= translateType (integerEncoding opts)
     return $ NormalValue tp $ \(_,inp,_,_) -> inp Map.! i
realizeDefInstruction opts ana real i@(castDown -> Just icmp) = do
  op <- getICmpOp icmp
  lhs <- getOperand icmp 0 >>= realizeValue ana real
  rhs <- getOperand icmp 1 >>= realizeValue ana real
  return $ NormalValue TpBool (SymBool . encodeCmpOp (integerEncoding opts) op lhs rhs)
realizeDefInstruction opts ana real i@(castDown -> Just (zext::Ptr ZExtInst)) = do
  op <- getOperand zext 0
  tp <- valueGetType op >>= translateType (integerEncoding opts)
  fop <- realizeValue ana real op
  if tp==TpBool
    then return $ ExtBool (symBool . asSMTValue fop (integerEncoding opts))
    else return $ NormalValue tp $ asSMTValue fop (integerEncoding opts)
realizeDefInstruction opts ana real i@(castDown -> Just (trunc::Ptr TruncInst)) = do
  op <- getOperand trunc 0
  tp <- valueGetType i >>= translateType (integerEncoding opts)
  fop <- realizeValue ana real op
  if tp==TpBool
    then return $ NormalValue TpBool $
         \inp -> SymBool $ (asInteger' (integerEncoding opts) fop inp) .==. (constant 1)
    else return fop
realizeDefInstruction opts ana real i@(castDown -> Just select) = do
  cond <- selectInstGetCondition select >>= realizeValue ana real
  tVal <- selectInstGetTrueValue select
  tp <- valueGetType tVal >>= translateType (integerEncoding opts)
  tVal' <- realizeValue ana real tVal
  fVal' <- selectInstGetFalseValue select >>= realizeValue ana real
  return $ NormalValue tp $
    \inp -> symITE (symBool $ asSMTValue cond (integerEncoding opts) inp)
            (asSMTValue tVal' (integerEncoding opts) inp)
            (asSMTValue fVal' (integerEncoding opts) inp)
realizeDefInstruction opts ana real i@(castDown -> Just phi)
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
       let mkITE [(_,val)] inp
             | null recPhis = asSMTValue val (integerEncoding opts) inp
           mkITE [] (_,_,instrs,_) = instrs Map.! i
           mkITE ((cond,val):xs) inp = symITE (cond inp)
                                       (asSMTValue val (integerEncoding opts) inp)
                                       (mkITE xs inp)
       return $ NormalValue tp (mkITE phis')
realizeDefInstruction _ ana real i = do
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
             cond <- branchInstGetCondition brInst
                     >>= realizeValue ana real
             let cond' = symBool . asSMTValue cond EncInt
                 tCond inp = app and' $ [act inp,cond' inp]++(restr inp)
                 fCond inp = app and' $ [act inp,not' $ cond' inp]++(restr inp)
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
   '_':'_':'n':'o':'n':'d':'e':'t':_ -> do
     tp <- getType i >>= translateType (integerEncoding opts)
     defineInstr' opts ana (real { inputs = Map.insert i tp (inputs real)
                                 }) i tp (\(_,inp,_,_) -> inp Map.! i)
   "assert" -> do
     cond <- callInstGetArgOperand call 0
             >>= realizeValue ana real
     let cond' = symBool . asSMTValue cond EncInt
     return $ real { asserts = Map.insertWith (++)
                               blk [cond']
                               (asserts real) }
   "assume" -> do
     cond <- callInstGetArgOperand call 0
             >>= realizeValue ana real
     let cond' = symBool . asSMTValue cond EncInt
     return $ real { assumes = (\inp -> (act inp) .=>. (cond' inp)):
                               (assumes real) }
   _ -> error $ "Unknown function "++fname
realizeInstruction opts ana real i@(castDown -> Just ret) = do
  rval <- returnInstGetReturnValue ret
  return real
realizeInstruction opts ana real (castDown -> Just sw) = do
  src <- instructionGetParent sw
  srcName <- getNameString src
  cond <- switchInstGetCondition sw
          >>= realizeValue ana real
  def <- switchInstGetDefaultDest sw
  defName <- getNameString def
  cases <- switchInstGetCases sw >>=
           mapM (\(val,trg) -> do
                    APInt _ val' <- constantIntGetValue val >>= peek
                    return (val',trg))
  let cond' = asInteger' (integerEncoding opts) cond
      act = case Map.lookup src (blockActivations real) of
        Just a -> a
      (defEdge,ngates) = addGate (gateMp real)
                         (Gate { gateTransfer = \inp -> app and' ((act inp):
                                                                  [ not' $
                                                                    (cond' inp)
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
                                                                ((cond' inp)
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
realizeInstruction opts ana real i@(castDown -> Just opInst)
  | eliminateDiv opts = do
  op <- binOpGetOpCode opInst
  case op of
   LShr -> do
     lhs <- getOperand opInst 0
     rhs <- getOperand opInst 1
     flhs <- realizeValue ana real lhs
     frhs <- realizeValue ana real rhs
     case frhs of
      IntConst rv -> do
        tp <- getType opInst >>= translateType (integerEncoding opts)
        defineInstr' opts ana (real { inputs = Map.insert i tp (inputs real)
                                    , assumes = (\inp@(_,inp',_,_)
                                                 -> (asInteger' (integerEncoding opts) flhs inp) .==.
                                                    (symInt $ inp' Map.! i)*(2^rv)):
                                                (assumes real)
                                    }) i tp (\(_,inp,_,_) -> inp Map.! i)
   _ -> do
     res <- realizeDefInstruction opts ana real i
     defineInstr opts ana real i res
realizeInstruction opts@(RealizationOptions { integerEncoding = enc@(EncLin _ _) }) ana real i@(castDown -> Just icmp) = do
  op <- getICmpOp icmp
  lhs <- getOperand icmp 0 >>= realizeValue ana real
  rhs <- getOperand icmp 1 >>= realizeValue ana real
  defineInstr' opts ana (real { inputs = Map.insert i TpBool (inputs real)
                              }) i TpBool $
    \inps@(_,inp,_,_)
    -> let lhs' = asSMTValue lhs enc inps
           rhs' = asSMTValue rhs enc inps
       in SymBool $ case lhs' of
           SymLinear vl cl -> case rhs' of
             SymLinear vr cr -> ite (app and' $
                                     (Vec.toList $ fmap (.==. (constant 0)) vl)++
                                     (Vec.toList $ fmap (.==. (constant 0)) vr))
                                (case op of
                                  I_EQ -> cl .==. cr
                                  I_NE -> not' $ cl .==. cr
                                  I_SGE -> cl .>=. cr
                                  I_UGE -> cl .>=. cr
                                  I_SGT -> cl .>. cr
                                  I_UGT -> cl .>. cr
                                  I_SLE -> cl .<=. cr
                                  I_ULE -> cl .<=. cr
                                  I_SLT -> cl .<. cr
                                  I_ULT -> cl .<. cr)
                                (symBool $ inp Map.! i)
realizeInstruction opts ana real i = do
  if forceNondet opts i
    then (do
             tp <- getType i >>= translateType (integerEncoding opts)
             defineInstr' opts ana (real { inputs = Map.insert i tp (inputs real)
                                         }) i tp (\(_,inp,_,_) -> inp Map.! i))
    else (do
             res <- realizeDefInstruction opts ana real i
             defineInstr opts ana real i res)

getModel :: RealizationOptions -> Ptr Function -> IO RealizedBlocks
getModel opts fun = do
  gr <- blockGraph fun
  blks <- getBasicBlockList fun >>= ipListToList
  ana <- foldlM (analyzeBlock opts)
         (Analyzation { instructionState = Map.empty
                      , implicitLatches = Map.empty
                      , explicitLatches = Map.empty
                      , latchBlocks = if useErrorState opts
                                      then Map.singleton nullPtr ()
                                      else Map.empty
                      , analyzedBlocks = Set.empty
                      , blkGraph = gr }) blks
  real <- realizeFunction opts ana fun
  res <- getModel' opts (head blks) ana real
  karrT <- if useKarr opts
           then getKarrTrans opts (Map.keys $ Map.mapMaybe
                                   (\(tp,_) -> if tp==TpInteger
                                               then Just tp
                                               else Nothing
                                   ) $ realizedLatches res) fun
           else return []
  extra <- case extraPredicates opts of
    Nothing -> return []
    Just file -> withFile file ReadMode $
                 \h -> parseLLVMPreds h
                       (Map.keys $ realizedLatchBlocks res)
                       (Map.keys $ realizedLatches res)
                       (\(_,instrs) i -> instrs Map.! i)
                       (\(blks,_) b -> blks Map.! b)
  return (res { realizedKarr = karrT
              , realizedExtraPredicates = extra })

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
                               phis' <- mapM (\(src,val) -> do
                                                 let act = case Map.lookup trg (edgeActivations creal) of
                                                       Just acts -> case Map.lookup src acts of
                                                         Just a -> a
                                                 val' <- lift $ realizeValue ana creal val
                                                 return (act,asSMTValue val' (integerEncoding opts))
                                             ) phis
                               let trg_val = case Map.lookup i (instructions creal) of
                                     Just (NormalValue _ v) -> v
                                   (expr,ngates) = addSymGate (gateMp creal) tp
                                                   (mkITE (if is_implicit
                                                           then Just (trg_act,trg_val)
                                                           else Nothing) i phis')
                                                   (Just name)
                               put $ creal { gateMp = ngates }
                               return $ Just (tp,const expr)
                        ) (explicitLatches ana)
                       ) real1
  let phiInstrs' = Map.mapMaybe id phiInstrs
  latchInstrs' <- Map.traverseWithKey (\i val -> do
                                          tp <- getType i >>= translateType (integerEncoding opts)
                                          return (tp,val)
                                      ) latchInstrs
  return $ RealizedBlocks { realizedLatchBlocks = latchBlks
                          , realizedLatches = Map.union phiInstrs' latchInstrs'
                          , realizedInputs = inputs real2
                          , realizedGates = gateMp real2
                          , realizedAssumes = assumes real2
                          , realizedAsserts = rasserts
                          , realizedInit = init
                          , realizedLinear = case integerEncoding opts of
                                              EncInt -> Nothing
                                              EncLin v _ -> Just v
                          , realizedKarr = []
                          , realizedExtraPredicates = []
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
                         NormalValue _ v -> v
                       ) $ Map.intersection (instructions real1) (implicitLatches ana)
    mkITE (Just (trg_act,trg_val)) i [] inp@(_,_,instrs,_)
      = symITE (trg_act inp)
        (trg_val inp)
        (instrs Map.! i)
    mkITE Nothing i [(_,val)] inp = val inp
    mkITE end i ((cond,val):xs) inp = symITE (cond inp)
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

getConcreteValues :: Monad m => RealizedBlocks -> LLVMInput -> SMT' m ConcreteValues
getConcreteValues st (acts,inps,instrs,_) = do
  acts' <- mapM getValue acts
  blk <- case [ blk
              | (blk,act) <- Map.toList acts'
              , act ] of
          [] -> error "Realization.getConcreteValues: No latch block is active."
          [x] -> return x
          _ -> error "Realization.getConcreteValues: More than one block is active."
  vals <- concretizeMap instrs
  inps' <- concretizeMap inps
  return $ ConcreteValues { block = blk
                          , latchValues = vals
                          , inputValues = inps' }
  where
    concretizeMap mp = mapM (\instr -> unliftArgs instr getValue) mp

instance Show ConcreteValues where
  show cv = unsafePerformIO $ do
    blk <- if (block cv)==nullPtr
           then return "err"
           else do
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
      renderVal (ValInteger n) = show n
      renderVal (ValBool n) = show n
      renderVal (ValLinear vec c) = show (vec,c)

instance TransitionRelation RealizedBlocks where
  type State RealizedBlocks = (LatchActs,ValueMap)
  type Input RealizedBlocks = (ValueMap,Maybe [SMTExpr Integer])
  type RevState RealizedBlocks = Map Integer (Either (Ptr BasicBlock) (Ptr Instruction))
  type PredicateExtractor RealizedBlocks = RSMState (Ptr BasicBlock) (Ptr Instruction)
  type RealizationProgress RealizedBlocks = RealizedGates
  createStateVars pre st = do
    blks <- sequence $ Map.mapWithKey
            (\blk _ -> do
                name <- if blk==nullPtr
                        then return "err"
                        else liftIO $ getNameString blk
                varNamed (pre++"L."++name)
            ) (realizedLatchBlocks st)
    instrs <- sequence $ Map.mapWithKey
              (\instr (tp,_) -> case tp of
                TpLinear _ -> case realizedLinear st of
                  Just lvec -> return $ SymLinear (fmap (\i -> if i==instr
                                                               then constant 1
                                                               else constant 0
                                                        ) lvec) (constant 0)
                _ -> do
                  name <- liftIO $ do
                    hn <- hasName instr
                    n <- if hn
                         then getNameString instr
                         else return "instr"
                    return (pre++"L."++n)
                  argVarsAnnNamed name tp
              ) (realizedLatches st)
    return (blks,instrs)
  createRevState pre st = do
    (blks,instrs) <- createStateVars pre st
    let rmp1 = Map.foldlWithKey
               (\rmp blk (Var idx _)
                 -> Map.insert idx (Left blk) rmp
               ) Map.empty blks
        rmp2 = Map.foldlWithKey
               (\rmp instr var
                 -> case var of
                     SymBool (Var idx _) -> Map.insert idx (Right instr) rmp
                     SymInteger (Var idx _) -> Map.insert idx (Right instr) rmp
               ) rmp1 instrs
    return ((blks,instrs),rmp2)
  relativizeExpr _ rev trm (blks,instrs)
    = snd $ foldExpr (\_ expr
                      -> ((),case expr of
                              Var idx ann -> case Map.lookup idx rev of
                                Just (Left blk)
                                  -> case cast (blks Map.! blk) of
                                      Just r -> r
                                Just (Right instr)
                                  -> case instrs Map.! instr of
                                      SymBool e -> case cast e of
                                        Just r -> r
                                      SymInteger e -> case cast e of
                                        Just r -> r
                              _ -> expr)
                     ) () trm
  createInputVars pre st = do
    inps <- sequence $ Map.mapWithKey
            (\instr tp -> case tp of
              TpLinear _ -> case realizedLinear st of
                Just lvec -> do
                  inp <- var
                  return $ SymLinear (fmap (const $ constant 0) lvec) (ite inp (constant 0) (constant 1))
              _ -> do
                name <- liftIO $ do
                  hn <- hasName instr
                  n <- if hn
                       then getNameString instr
                       else return "input"
                  return (pre++"I."++n)
                argVarsAnnNamed name tp
            ) (realizedInputs st)
    lins <- case realizedLinear st of
      Nothing -> return Nothing
      Just vec -> do
        rvec <- mapM (const var) vec
        return $ Just (Vec.toList rvec)
    return (inps,lins)
  initialState st (acts,_)
    = app and' [ if blk==realizedInit st
                 then act
                 else not' act
               | (blk,act) <- Map.toList acts ]
  stateInvariant _ (blks,_)
    = app or' $
      fmap (app and') $
      exactlyOne [] (Map.elems blks)
    where
      exactlyOne prev [x] = [prev++[x]]
      exactlyOne prev (x:xs)
        = (prev++(x:(fmap not' xs))):
          (exactlyOne (prev++[not' x]) xs)
  declareNextState st (blks,instrs) (inp,lins) _ real = do
    let inp' = (blks,inp,instrs,lins)
    (nblks,real1) <- runStateT
                     (Map.traverseWithKey
                      (\trg act -> do
                          real <- get
                          (expr,nreal) <- lift $ declareGate (act inp') real
                                          (realizedGates st) inp'
                          put nreal
                          return expr
                      ) (realizedLatchBlocks st)
                     ) real
    (ninstrs,real2) <- runStateT
                       (Map.traverseWithKey
                        (\instr (tp,val) -> do
                            real <- get
                            (expr,nreal) <- lift $ declareSymGate (val inp') real
                                            (realizedGates st) inp'
                            put nreal
                            return expr
                        ) (realizedLatches st)
                       ) real1
    return ((nblks,ninstrs),real2)
  declareAssertions st (blks,instrs) (inp,lins) real
    = runStateT (traverse (\ass -> do
                              real <- get
                              (expr,nreal) <- lift $ declareGate (ass inp') real
                                              (realizedGates st) inp'
                              put nreal
                              return expr
                          ) (realizedAsserts st)
                ) real
    where
      inp' = (blks,inp,instrs,lins)
  declareAssumptions st (blks,instrs) (inp,lins) real
    = runStateT (traverse (\ass -> do
                              real <- get
                              (expr,nreal) <- lift $ declareGate (ass inp') real
                                              (realizedGates st) inp'
                              put nreal
                              return expr
                          ) (realizedAssumes st)
                ) real
    where
      inp' = (blks,inp,instrs,lins)
  annotationState st = (fmap (const ()) (realizedLatchBlocks st),fmap fst (realizedLatches st))
  annotationInput st = (realizedInputs st,
                        case realizedLinear st of
                         Nothing -> Nothing
                         Just vec -> Just $ Vec.toList $ fmap (const ()) vec)
  renderPartialState _ (blks,instrs) = do
    blk <- findBlk [ (blk,act)
                   | (blk,Just act) <- Map.toList blks ]
    instrs' <- mapM (\(instr,val) -> do
                        isNamed <- liftIO $ hasName instr
                        instrName <- if isNamed
                                     then liftIO $ getNameString instr
                                     else return "<unnamed>"
                        return $ instrName++"="++show val
                    ) [ (instr,val) | (instr,Just val) <- Map.toList instrs ]
    return $ blk++"["++concat (intersperse "," instrs')++"]"
    where
      findBlk xs = do
        lst <- mapM (\(blk,act) -> do
                        name <- if blk==nullPtr
                                then return "err"
                                else (do
                                         isNamed <- liftIO $ hasName blk
                                         if isNamed
                                           then liftIO $ getNameString blk
                                           else return "<unnamed>")
                        if act
                          then return name
                          else return $ "!"++name
                    ) (sortBy (comparing (not . snd)) xs)
        return $ concat $ intersperse "," lst
  suggestedPredicates mdl = (fmap (\p -> (True,p)) $
                             blkPredicates (fmap (const ()) (realizedLatchBlocks mdl))++
                             splitPredicates (cmpPredicates (fmap fst (realizedLatches mdl))))++
                            [ (False,\(_,instrs) -> op (case [ if f==1
                                                               then (symInt $ instrs Map.! i)*(constant f)
                                                               else (symInt $ instrs Map.! i)*(constant f)
                                                             | (i,f) <- vec, f/=0 ] of
                                                         [] -> constant 0
                                                         [x] -> x
                                                         xs -> app plus xs
                                                       ) (constant c))
                            | (blk,aff) <- realizedKarr mdl
                            , (vec,c) <- aff
                            , op <- [(.>.),(.>=.)] ]++
                            [ (False,pred) | pred <- realizedExtraPredicates mdl ]
  defaultPredicateExtractor _ = return emptyRSM
  extractPredicates mdl rsm full lifted = do
    let blk = case [ blk | (blk,True) <- Map.toList (fst full) ] of
               [b] -> b
        nrsm = addRSMState blk (Map.mapMaybe (\el -> do
                                                 rel <- el
                                                 case rel of
                                                  ValInteger i -> Just i
                                                  _ -> Nothing
                                             ) $ snd lifted) rsm
    (nrsm',props) <- mineStates (createSMTPipe "z3" ["-smt2","-in"]) nrsm
    return (nrsm',fmap (\prop (_,vals) -> prop (\v -> case vals Map.! v of
                                                       SymInteger rv -> rv)) props)
  startingProgress _ = Map.empty

assertPredicates :: RealizedBlocks -> [(LatchActs,ValueMap) -> SMTExpr Bool]
assertPredicates mdl
  = fmap (\ass (acts,latch)
          -> let inp = (acts,fmap defInput (realizedInputs mdl),latch,Nothing)
             in translateGateExpr (ass inp)
                (realizedGates mdl) Map.empty inp
         ) (realizedAsserts mdl)
  where
    defInput TpBool = SymBool (constant False)
    defInput TpInteger = SymInteger(constant 0)

getKarrTrans :: RealizationOptions -> [Ptr Instruction] -> Ptr Function
                -> IO [(Ptr BasicBlock,[([(Ptr Instruction,Integer)],Integer)])]
getKarrTrans opts instrs fun = do
  nmdl <- getModel (opts { integerEncoding = EncLin instrVec (\(_,_,_,Just lin) -> lin)
                         , useKarr = False
                         , extraPredicates = Nothing
                         }) fun
  when (verbosity opts > 2) $ do
    instrNames <- mapM getNameString instrs
    putStrLn $ "Karr variables: "++show instrNames
  pipe <- createSMTPipe "z3" ["-smt2","-in"] -- >>= namedDebugBackend "karr"
  trans <- withSMTBackend pipe $ do
    (blks,instrs) <- createStateVars "" nmdl
    inp <- createInputVars "" nmdl
    ((nblks,ninstrs),gts1) <- declareNextState nmdl (blks,instrs) inp Nothing Map.empty
    (assumps,gts2) <- declareAssumptions nmdl (blks,instrs) inp gts1
    assert $ stateInvariant nmdl (blks,instrs)
    assert $ stateInvariant nmdl (nblks,ninstrs)
    mapM_ assert assumps
    allSat blks nblks ninstrs
  initBlk <- getEntryBlock fun
  let (rev,mp,trans') = buildKarrCFG Map.empty Map.empty Map.empty trans
      numVars = length instrs
      initSt = rev Map.! initBlk
      karrSt0 = initKarr numVars initSt
                (\src trg -> trans' Map.! src Map.! trg)
                (\src -> Map.keys $ trans' Map.! src)
      karrStEnd = finishKarr karrSt0
  when (verbosity opts > 2) $ do
    putStrLn $ "Karr result: "++show karrStEnd
  return [ (ndBlk,[ (zipWith (\x y -> (x,y)) instrs (Vec.toList vec),c)
                  | (vec,c) <- extractPredicateVec diag ])
         | (nd,diag) <- IMap.toList (karrNodes karrStEnd)
         , let ndBlk = mp Map.! nd ]
  where
    instrVec = Vec.fromList instrs
    allSat blks nblks ninstrs = do
      hasSolution <- checkSat
      if hasSolution
        then (do
                 cblks <- mapM getValue blks
                 cnblks <- mapM getValue nblks
                 cvecs <- mapM (\i -> case ninstrs Map.! i of
                                 SymLinear vec _ -> mapM getValue vec
                               ) instrVec
                 ccs <- mapM (\i -> case ninstrs Map.! i of
                                     SymLinear _ c -> getValue c
                             ) instrVec
                 let src_blk = head [ blk | (blk,True) <- Map.toList cblks ]
                     trg_blk = head [ blk | (blk,True) <- Map.toList cnblks ]
                 when (verbosity opts > 2) $ do
                   liftIO $ (if src_blk==nullPtr then return "err" else getNameString src_blk) >>= putStr
                   liftIO $ putStr " ~> "
                   liftIO $ (if trg_blk==nullPtr then return "err" else getNameString trg_blk) >>= putStr
                   liftIO $ putStr ": " >> putStr (show $ Vec.toList $ fmap Vec.toList cvecs) >> putStr " " >> print (Vec.toList ccs)
                 -- Block solution
                 assert $ app or' $ concat
                   [ Map.elems $ Map.intersectionWith (\v c -> not' $ v .==. constant c) blks cblks
                   , Map.elems $ Map.intersectionWith (\v c -> not' $ v .==. constant c) nblks cnblks
                   , [ not' $ var .==. (constant fac)
                     | (instr,facs) <- Vec.toList $ Vec.zip instrVec cvecs
                     , let SymLinear varVec _ = ninstrs Map.! instr
                     , (var,fac) <- Vec.toList $ Vec.zip varVec facs ]
                   , [ not' $ var .==. (constant c)
                     | (instr,c) <- Vec.toList $ Vec.zip instrVec ccs
                     , let SymLinear _ var = ninstrs Map.! instr ] ]
                 rest <- allSat blks nblks ninstrs
                 return $ (src_blk,trg_blk,cvecs,ccs):rest)
        else return []

buildKarrCFG :: Map (Ptr BasicBlock) Int
             -> Map Int (Ptr BasicBlock)
             -> Map Int (Map Int [(Vector (Vector Integer),Vector Integer)])
             -> [(Ptr BasicBlock,
                  Ptr BasicBlock,
                  Vector (Vector Integer),
                  Vector Integer)]
             -> (Map (Ptr BasicBlock) Int,Map Int (Ptr BasicBlock),
                 Map Int (Map Int [(Vector (Vector Integer),Vector Integer)]))
buildKarrCFG rev mp trans [] = (rev,mp,trans)
buildKarrCFG rev mp trans ((src,trg,vec,c):rest)
  = buildKarrCFG rev2 mp2 ntrans rest
  where
    (isrc,rev1,mp1) = case Map.lookup src rev of
      Just i -> (i,rev,mp)
      Nothing -> let sz = Map.size rev
                 in (sz,Map.insert src sz rev,Map.insert sz src mp)
    (itrg,rev2,mp2) = case Map.lookup trg rev1 of
      Just i -> (i,rev1,mp1)
      Nothing -> let sz = Map.size rev1
                 in (sz,Map.insert trg sz rev1,Map.insert sz trg mp1)
    ntrans = Map.alter (\trgs -> Just $ case trgs of
                         Nothing -> Map.singleton itrg [(vec,c)]
                         Just trgs' -> Map.alter (\ts -> Just $ case ts of
                                                   Nothing -> [(vec,c)]
                                                   Just ts' -> (vec,c):ts'
                                                 ) itrg trgs'
                       ) isrc trans

sanityCheck :: RealizedBlocks -> IO Bool
sanityCheck mdl = do
  pipe <- createSMTPipe "z3" ["-smt2","-in"] -- >>= namedDebugBackend "sanity"
  withSMTBackend pipe $ do
    (blks,instrs) <- createStateVars "" mdl
    inp@(inpInstrs,lin) <- createInputVars "" mdl
    ((nblks,ninstrs),gts1) <- declareNextState mdl (blks,instrs) inp Nothing Map.empty
    (assumps,gts2) <- declareAssumptions mdl (blks,instrs) inp gts1
    assert $ stateInvariant mdl (blks,instrs)
    mapM_ assert assumps
    assert $ not' $ stateInvariant mdl (nblks,ninstrs)
    res <- checkSat
    if res
      then (do
               vals <- getConcreteValues mdl (blks,inpInstrs,instrs,lin)
               error $ "Unlawful state is reachable:\n"++show vals)
      else return True
  
