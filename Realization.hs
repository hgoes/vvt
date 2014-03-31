{-# LANGUAGE RankNTypes,ScopedTypeVariables,ViewPatterns #-}
module Realization where

import Data.Map (Map)
import qualified Data.Map as Map
import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)
import Foreign.Ptr
import LLVM.FFI
import Data.Typeable
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,mapM_,mapM)

import Gates

type ValueMap = Map (Ptr Instruction) UntypedExpr
type LatchActs = Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (SMTExpr Bool))

type LLVMInput = (LatchActs,ValueMap,ValueMap)

type LLVMOutput = (LatchActs,ValueMap)

data RealizationSt = RealizationSt { initBlk :: Ptr BasicBlock
                                   , prevBlks :: Map (Ptr BasicBlock) GateExpr
                                   , prevInstrs :: Map (Ptr Instruction) UntypedExpr
                                   , inputInstrs :: Map (Ptr Instruction) ProxyArg
                                   , latchInstrs :: Map (Ptr Instruction) ProxyArg
                                   , latchBlks :: Map (Ptr BasicBlock) (Map (Ptr BasicBlock) ())
                                   , gates :: GateMap LLVMInput
                                   , forwardEdges :: Map (Ptr BasicBlock)
                                                     (Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool))
                                   , backwardEdges :: Map (Ptr BasicBlock)
                                                      (Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool))
                                   , assertions :: [LLVMInput -> SMTExpr Bool]
                                   , assumptions :: [LLVMInput -> SMTExpr Bool]
                                   }

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

translateType :: Ptr Type -> IO ProxyArg
translateType (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return (ProxyArg (undefined::Bool) ())
    _ -> return (ProxyArg (undefined::Integer) ())
translateType tp = do
  typeDump tp
  error "Can't translate type"

translateValue :: RealizationSt -> Ptr Value -> IO (LLVMInput -> UntypedExpr,ProxyArg)
translateValue st val = case castDown val of
  Just instr -> case Map.lookup instr (prevInstrs st) of
    Just res -> case res of
      UntypedExpr (e::SMTExpr a) -> return (const res,ProxyArg (undefined::a) (extractAnnotation e))
    Nothing -> case Map.lookup instr (inputInstrs st) of
      Just tp -> return (\(_,inp,_) -> inp Map.! instr,tp)
      Nothing -> case Map.lookup instr (latchInstrs st) of
        Just tp -> return (\(_,_,latch) -> latch Map.! instr,tp)
        Nothing -> do
          vname <- getNameString val
          error $ "Value "++vname++" not found."
  Nothing -> case castDown val of
    Just i -> do
      c <- translateConstant i
      case c of
        UntypedExpr (e::SMTExpr a) -> return (const c,ProxyArg (undefined::a) (extractAnnotation e))

translateConstant :: Ptr ConstantInt -> IO UntypedExpr
translateConstant i = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return $ UntypedExpr (constant (rv/=0))
    else return $ UntypedExpr (constant $ fromIntegral rv :: SMTExpr Integer)

realizeFunction :: Ptr Function -> IO RealizationSt
realizeFunction fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  foldlM realizeBlk (RealizationSt { initBlk = head blks
                                   , prevBlks = Map.empty
                                   , prevInstrs = Map.empty
                                   , inputInstrs = Map.empty
                                   , latchInstrs = Map.empty
                                   , latchBlks = Map.empty
                                   , gates = emptyGateMap
                                   , forwardEdges = Map.empty
                                   , backwardEdges = Map.empty
                                   , assertions = []
                                   , assumptions = []
                                   }) blks
  where
    realizeBlk :: RealizationSt -> Ptr BasicBlock -> IO RealizationSt
    realizeBlk st blk = do
      name <- getNameString blk
      let (isInit,gate) = case Map.lookup blk (forwardEdges st) of
            Nothing -> (True,Gate (\(acts,_,_) -> case Map.lookup blk acts of
                                      Just mp -> app or' (Map.elems mp)) () (Just name))
            Just inc -> (False,Gate (\inp -> app or' (fmap (\f -> f inp) (Map.elems inc))) () (Just name))
          (gexpr,ngates) = addGate' (gates st) gate
          st0 = st { gates = ngates
                   , prevBlks = Map.insert blk gexpr (prevBlks st)
                   , latchBlks = if isInit
                                 then Map.insertWith Map.union blk (Map.singleton nullPtr ()) (latchBlks st)
                                 else latchBlks st
                   , backwardEdges = if isInit
                                     then Map.insertWith
                                          Map.union
                                          blk (Map.singleton nullPtr (const $ constant False))
                                          (backwardEdges st)
                                     else backwardEdges st
                   }
          act = const (InternalObj gexpr ())
      instrs <- getInstList blk >>= ipListToList
      (instrs',st1) <- handlePhis st0 instrs
      foldlM (realizeInstr act) st1 instrs'

    realizeInstr :: (LLVMInput -> SMTExpr Bool) -> RealizationSt -> Ptr Instruction
                    -> IO RealizationSt
    realizeInstr _ st i@(castDown -> Just opInst) = do
      name <- getNameString i
      op <- binOpGetOpCode opInst
      (lhs,lhs_tp) <- getOperand opInst 0 >>= translateValue st
      (rhs,rhs_tp) <- getOperand opInst 1 >>= translateValue st
      let withOp :: (forall t. SMTType t => (LLVMInput -> SMTExpr t) -> SMTAnnotation t -> a) -> a
          withOp f = case op of
            Add -> f (\inp -> let l = castUntypedExpr $ lhs inp :: SMTExpr Integer
                                  r = castUntypedExpr $ rhs inp
                              in l + r) ()
            Sub -> f (\inp -> let l = castUntypedExpr $ lhs inp :: SMTExpr Integer
                                  r = castUntypedExpr $ rhs inp
                              in l - r) ()
            Mul -> f (\inp -> let l = castUntypedExpr $ lhs inp :: SMTExpr Integer
                                  r = castUntypedExpr $ rhs inp
                              in l * r) ()
            And -> if lhs_tp == (ProxyArg (undefined::Bool) ())
                   then f (\inp -> let l = castUntypedExpr $ lhs inp
                                       r = castUntypedExpr $ rhs inp
                                   in l .&&. r) ()
                   else error "And operator can't handle non-bool inputs."
            Or -> if lhs_tp == (ProxyArg (undefined::Bool) ())
                  then f (\inp -> let l = castUntypedExpr $ lhs inp
                                      r = castUntypedExpr $ rhs inp
                                  in l .||. r) ()
                  else error "Or operator can't handle non-bool inputs."
            Xor -> if lhs_tp == (ProxyArg (undefined::Bool) ())
                   then f (\inp -> let l = castUntypedExpr $ lhs inp
                                       r = castUntypedExpr $ rhs inp
                                   in app xor [l,r]) ()
                   else error "Xor operator can't handle non-bool inputs."
            _ -> error $ "Unknown operator: "++show op
      withOp $ \fun ann -> do
        let (expr,ngt) = addGate (gates st) (Gate fun ann (Just name))
        return $ st { gates = ngt
                    , prevInstrs = Map.insert i (UntypedExpr expr) (prevInstrs st) }
    realizeInstr act st (castDown -> Just brInst) = do
      blk <- instructionGetParent brInst
      is_cond <- branchInstIsConditional brInst
      if is_cond
        then (do
                 ifTrue <- terminatorInstGetSuccessor brInst 0
                 ifFalse <- terminatorInstGetSuccessor brInst 1
                 (cond,_) <- branchInstGetCondition brInst >>= translateValue st
                 let res1 = if ifTrue==blk
                            then Nothing
                            else Map.lookup ifTrue (prevBlks st)
                     st0 = case res1 of
                       Just gexpr
                         -> st { backwardEdges = Map.insertWith Map.union ifTrue
                                                 (Map.singleton blk
                                                  (\inp -> (act inp) .&&.
                                                           (castUntypedExpr $ cond inp)))
                                                 (backwardEdges st)
                               , gates = modifyGate gexpr (gates st) $
                                         \(Gate fun ann name)
                                          -> Gate (\inp@(acts,_,_) -> case Map.lookup ifTrue acts of
                                                      Just mp -> case Map.lookup blk mp of
                                                        Just act -> act .||. (fun inp)) ann name
                               }
                       Nothing -> st { forwardEdges = Map.insertWith Map.union ifTrue
                                                      (Map.singleton blk
                                                       (\inp -> (act inp) .&&.
                                                                (castUntypedExpr $ cond inp)))
                                                      (forwardEdges st) }
                     res2 = if ifFalse==blk
                            then Nothing
                            else Map.lookup ifFalse (prevBlks st0)
                     st1 = case res2 of
                       Just gexpr
                         -> st0 { backwardEdges = Map.insertWith Map.union ifFalse
                                                  (Map.singleton blk
                                                   (\inp -> (act inp) .&&.
                                                            (not' (castUntypedExpr $ cond inp))))
                                                  (backwardEdges st0)
                                , gates = modifyGate gexpr (gates st0) $
                                          \(Gate fun ann name)
                                          -> Gate (\inp@(acts,_,_) -> case Map.lookup ifFalse acts of
                                                      Just mp -> case Map.lookup blk mp of
                                                        Just act -> act .||. (fun inp)) ann name

                                }
                       Nothing -> st0 { forwardEdges = Map.insertWith Map.union ifFalse
                                                       (Map.singleton blk
                                                        (\inp -> (act inp) .&&.
                                                                 (not' (castUntypedExpr $ cond inp))))
                                                       (forwardEdges st0) }
                 return st1)
        else (do
                 nxt <- terminatorInstGetSuccessor brInst 0
                 case Map.lookup nxt (prevBlks st) of
                   Just gexpr
                     -> return $ st { backwardEdges = Map.insertWith Map.union nxt
                                                      (Map.singleton blk act)
                                                      (backwardEdges st)
                                    , gates = modifyGate gexpr (gates st) $
                                              \(Gate fun ann name)
                                              -> Gate (\inp@(acts,_,_) -> case Map.lookup nxt acts of
                                                          Just mp -> case Map.lookup blk mp of
                                                            Just act -> act .||. (fun inp)) ann name
                                    }
                   Nothing -> return $ st { forwardEdges = Map.insertWith Map.union nxt
                                                           (Map.singleton blk act)
                                                           (forwardEdges st) })
    realizeInstr act st i@(castDown -> Just call) = do
      fname <- getFunctionName call
      case fname of
        '_':'_':'u':'n':'d':'e':'f':_ -> do
          trg_tp <- valueGetType i >>= translateType
          return $ st { inputInstrs = Map.insert i trg_tp (inputInstrs st) }
        "assert" -> do
          cond <- callInstGetArgOperand call 0
          (cond',_) <- translateValue st cond
          return $ st { assertions = (\inp -> (act inp) .=>. (castUntypedExpr (cond' inp)))
                                     :assertions st }
        "assume" -> do
          cond <- callInstGetArgOperand call 0
          (cond',_) <- translateValue st cond
          return $ st { assumptions = (\inp -> (act inp) .=>. (castUntypedExpr (cond' inp)))
                                      :assumptions st }
        _ -> error $ "Unknown function "++fname
    realizeInstr _ st i@(castDown -> Just icmp) = do
      name <- getNameString i
      op <- getICmpOp icmp
      (lhs,lhs_tp) <- getOperand icmp 0 >>= translateValue st
      (rhs,rhs_tp) <- getOperand icmp 1 >>= translateValue st
      withProxyArg lhs_tp $
        \(_::a) ann -> do
          let gate = Gate (\inp -> let l = castUntypedExpr (lhs inp) :: SMTExpr a
                                       r = castUntypedExpr (rhs inp)
                                   in case op of
                                     I_EQ -> l .==. r
                                     I_NE -> not' (l .==. r)
                                     I_SGE -> case cast (l,r) of
                                       Just (l',r') -> l' .>=. (r'::SMTExpr Integer)
                                     I_SGT -> case cast (l,r) of
                                       Just (l',r') -> l' .>. (r'::SMTExpr Integer)
                                     I_SLE -> case cast (l,r) of
                                       Just (l',r') -> l' .<=. (r'::SMTExpr Integer)
                                     I_SLT -> case cast (l,r) of
                                       Just (l',r') -> l' .<. (r'::SMTExpr Integer)
                                     _ -> error $ "Unknown operator: "++show op
                          ) () (Just name)
              (res,ngates) = addGate (gates st) gate
          return $ st { gates = ngates
                      , prevInstrs = Map.insert i (UntypedExpr res) (prevInstrs st) }
    realizeInstr _ st i@(castDown -> Just ret) = do
      rval <- returnInstGetReturnValue ret
      if rval==nullPtr
        then return st
        else return st
    realizeInstr _ st i@(castDown -> Just (zext::Ptr ZExtInst)) = do
      name <- getNameString i
      (op,op_tp) <- getOperand zext 0 >>= translateValue st
      trg_tp <- valueGetType zext >>= translateType
      let gate = if op_tp==(ProxyArg (undefined::Bool) ())
                 then Gate (\inp -> ite (castUntypedExpr $ op inp)
                                    (constant (1::Integer)) (constant 0)) () (Just name)
                 else Gate (\inp -> castUntypedExpr $ op inp) () (Just name)
          (res,ngates) = addGate (gates st) gate
      return $ st { gates = ngates
                  , prevInstrs = Map.insert i (UntypedExpr res) (prevInstrs st) }
    realizeInstr _ st i@(castDown -> Just select) = do
      name <- getNameString i
      (cond,ctp) <- selectInstGetCondition select >>= translateValue st
      (tVal,ttp) <- selectInstGetTrueValue select >>= translateValue st
      (fVal,ftp) <- selectInstGetFalseValue select >>= translateValue st
      withProxyArg ttp $
        \(_::a) ann -> do
          let gate = Gate (\inp -> ite (castUntypedExpr $ cond inp)
                                   (castUntypedExpr (tVal inp) :: SMTExpr a)
                                   (castUntypedExpr (fVal inp))) ann (Just name)
              (res,ngates) = addGate (gates st) gate
          return $ st { gates = ngates
                      , prevInstrs = Map.insert i (UntypedExpr res) (prevInstrs st) }
    realizeInstr _ _ i = do
      valueDump i
      error "Unknown instruction"

    handlePhis :: RealizationSt -> [Ptr Instruction] -> IO ([Ptr Instruction],RealizationSt)
    handlePhis st (i:is) = case castDown i of
      Just phi -> do
        name <- getNameString i
        tp <- valueGetType i >>= translateType
        blk <- instructionGetParent i
        num <- phiNodeGetNumIncomingValues phi
        lst <- mapM (\i -> do
                        iblk <- phiNodeGetIncomingBlock phi i
                        ival <- phiNodeGetIncomingValue phi i
                        let prev = if blk==iblk
                                   then Nothing
                                   else Map.lookup iblk (prevBlks st)
                        case prev of
                          Just act -> do
                            (extr,_) <- translateValue st ival
                            return (Left (InternalObj act (),extr))
                          Nothing -> case castDown ival of
                            Nothing -> case castDown ival of
                              Just instr -> return (Right (iblk,Left instr))
                            Just c -> do
                              rv <- translateConstant c
                              return (Right (iblk,Right rv))
                   ) [0..(num-1)]
        let nst = withProxyArg tp $
                  \(_::a) ann
                  -> let (res,ngt) = addGate (gates st)
                                     (Gate (\inp
                                            -> mkITE blk inp lst :: SMTExpr a) ann (Just name))
                     in foldl (\cst el -> case el of
                                  Left _ -> cst
                                  Right (src,val)
                                    -> cst { latchBlks = Map.insertWith Map.union blk
                                                         (Map.singleton src ()) (latchBlks cst)
                                           , latchInstrs = case val of
                                                Right _ -> latchInstrs cst
                                                Left i -> Map.insert i tp (latchInstrs cst) }
                              ) (st { prevInstrs = Map.insert i (UntypedExpr res) (prevInstrs st)
                                    , gates = ngt }) lst
        handlePhis nst is
      Nothing -> return (i:is,st)

    mkITE :: SMTType a => Ptr BasicBlock -> LLVMInput
             -> [Either (SMTExpr Bool,LLVMInput -> UntypedExpr) (Ptr BasicBlock,Either (Ptr Instruction) UntypedExpr)]
             -> SMTExpr a
    mkITE blk inp@(acts,_,latchs) (x:xs)
      = case x of
      Left (act,extr) -> case xs of
        [] -> castUntypedExpr $ extr inp
        _ -> ite act (castUntypedExpr $ extr inp) (mkITE blk inp xs)
      Right (src,Right val) -> case xs of
        [] -> castUntypedExpr val
        _ -> case Map.lookup blk acts of
          Just mp -> case Map.lookup src mp of
            Just act -> ite act (castUntypedExpr val) (mkITE blk inp xs)
      Right (src,Left instr) -> case Map.lookup instr latchs of
        Just val -> case xs of
          [] -> castUntypedExpr val
          _ -> case Map.lookup blk acts of
            Just mp -> case Map.lookup src mp of
              Just act -> ite act (castUntypedExpr val) (mkITE blk inp xs)
