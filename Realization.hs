{-# LANGUAGE RankNTypes,ScopedTypeVariables,ViewPatterns,PackageImports,DeriveDataTypeable,GADTs #-}
module Realization where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intersperse)
import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)
import qualified Language.SMTLib2.Internals as SMT
import Foreign.Ptr
import LLVM.FFI
import Data.Typeable
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,mapM_,mapM,concat,sequence)
import "mtl" Control.Monad.State (StateT,runStateT,get,put,lift)
import System.IO.Unsafe

import Gates
import Model

type ValueMap = Map (Ptr Instruction) (SMTExpr UntypedValue)

-- | Stores activation condition for backward edges
--   Edges are stored in Target -> Source direction.
--   Map.fromList [(blk1,Map.fromList [(blk2,act)])] describes one edge, from blk2 to blk1 with condition act.
type LatchActs = Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (SMTExpr Bool))

type LLVMInput = (LatchActs,ValueMap,ValueMap)

type LLVMOutput = (LatchActs,ValueMap)

data RealizationSt = RealizationSt { initBlk :: Ptr BasicBlock
                                   , prevBlks :: Map (Ptr BasicBlock) GateExpr
                                   , prevInstrs :: Map (Ptr Instruction) (SMTExpr UntypedValue)
                                   , inputInstrs :: Map (Ptr Instruction) ProxyArgValue
                                   , latchInstrs :: Map (Ptr Instruction) ProxyArgValue
                                   , latchBlks :: Map (Ptr BasicBlock) (Map (Ptr BasicBlock) ())
                                   , gates :: GateMap LLVMInput
                                   , forwardEdges :: Map (Ptr BasicBlock)
                                                     (Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool))
                                   , backwardEdges :: Map (Ptr BasicBlock)
                                                      (Map (Ptr BasicBlock) (LLVMInput -> SMTExpr Bool))
                                   , assertions :: [LLVMInput -> SMTExpr Bool]
                                   , assumptions :: [LLVMInput -> SMTExpr Bool]
                                   }

data ConcreteValues = ConcreteValues { srcBlock :: Ptr BasicBlock
                                     , trgBlock :: Ptr BasicBlock
                                     , latchValues :: Map (Ptr Instruction) SMT.Value
                                     , inputValues :: Map (Ptr Instruction) SMT.Value
                                     }

type ErrorTrace = [ConcreteValues]

data SymValue = BoolValue (SMTExpr Bool)
              | IntValue (SMTExpr Integer)
              deriving (Typeable,Eq,Ord,Show)

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

translateType :: Ptr Type -> IO ProxyArgValue
translateType (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return (ProxyArgValue (undefined::Bool) ())
    _ -> return (ProxyArgValue (undefined::Integer) ())
translateType tp = do
  typeDump tp
  error "Can't translate type"

translateValue :: RealizationSt -> Ptr Value -> IO (LLVMInput -> SMTExpr UntypedValue,ProxyArgValue)
translateValue st val = case castDown val of
  Just instr -> case Map.lookup instr (prevInstrs st) of
    Just res -> return (const res,extractAnnotation res)
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
      return (const c,extractAnnotation c)

translateConstant :: Ptr ConstantInt -> IO (SMTExpr UntypedValue)
translateConstant i = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return $ UntypedExprValue (constant (rv/=0))
    else return $ UntypedExprValue (constant $ fromIntegral rv :: SMTExpr Integer)

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
      let withOp :: (forall t. SMTValue t => (LLVMInput -> SMTExpr t) -> SMTAnnotation t -> a) -> a
          withOp f = case op of
            Add -> f (\inp -> let l = castUntypedExprValue $ lhs inp :: SMTExpr Integer
                                  r = castUntypedExprValue $ rhs inp
                              in l + r) ()
            Sub -> f (\inp -> let l = castUntypedExprValue $ lhs inp :: SMTExpr Integer
                                  r = castUntypedExprValue $ rhs inp
                              in l - r) ()
            Mul -> f (\inp -> let l = castUntypedExprValue $ lhs inp :: SMTExpr Integer
                                  r = castUntypedExprValue $ rhs inp
                              in l * r) ()
            And -> if lhs_tp == (ProxyArgValue (undefined::Bool) ())
                   then f (\inp -> let l = castUntypedExprValue $ lhs inp
                                       r = castUntypedExprValue $ rhs inp
                                   in l .&&. r) ()
                   else error "And operator can't handle non-bool inputs."
            Or -> if lhs_tp == (ProxyArgValue (undefined::Bool) ())
                  then f (\inp -> let l = castUntypedExprValue $ lhs inp
                                      r = castUntypedExprValue $ rhs inp
                                  in l .||. r) ()
                  else error "Or operator can't handle non-bool inputs."
            Xor -> if lhs_tp == (ProxyArgValue (undefined::Bool) ())
                   then f (\inp -> let l = castUntypedExprValue $ lhs inp
                                       r = castUntypedExprValue $ rhs inp
                                   in app xor [l,r]) ()
                   else error "Xor operator can't handle non-bool inputs."
            _ -> error $ "Unknown operator: "++show op
      withOp $ \fun ann -> do
        let (expr,ngt) = addGate (gates st) (Gate fun ann (Just name))
        return $ st { gates = ngt
                    , prevInstrs = Map.insert i (UntypedExprValue expr) (prevInstrs st) }
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
                                                           (castUntypedExprValue $ cond inp)))
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
                                                                (castUntypedExprValue $ cond inp)))
                                                      (forwardEdges st) }
                     res2 = if ifFalse==blk
                            then Nothing
                            else Map.lookup ifFalse (prevBlks st0)
                     st1 = case res2 of
                       Just gexpr
                         -> st0 { backwardEdges = Map.insertWith Map.union ifFalse
                                                  (Map.singleton blk
                                                   (\inp -> (act inp) .&&.
                                                            (not' (castUntypedExprValue $ cond inp))))
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
                                                                 (not' (castUntypedExprValue $ cond inp))))
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
          return $ st { assertions = (\inp -> (act inp) .=>. (castUntypedExprValue (cond' inp)))
                                     :assertions st }
        "assume" -> do
          cond <- callInstGetArgOperand call 0
          (cond',_) <- translateValue st cond
          return $ st { assumptions = (\inp -> (act inp) .=>. (castUntypedExprValue (cond' inp)))
                                      :assumptions st }
        _ -> error $ "Unknown function "++fname
    realizeInstr _ st i@(castDown -> Just icmp) = do
      name <- getNameString i
      op <- getICmpOp icmp
      (lhs,lhs_tp) <- getOperand icmp 0 >>= translateValue st
      (rhs,rhs_tp) <- getOperand icmp 1 >>= translateValue st
      withProxyArgValue lhs_tp $
        \(_::a) ann -> do
          let gate = Gate (\inp -> let l = castUntypedExprValue (lhs inp) :: SMTExpr a
                                       r = castUntypedExprValue (rhs inp)
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
                      , prevInstrs = Map.insert i (UntypedExprValue res) (prevInstrs st) }
    realizeInstr _ st i@(castDown -> Just ret) = do
      rval <- returnInstGetReturnValue ret
      if rval==nullPtr
        then return st
        else return st
    realizeInstr _ st i@(castDown -> Just (zext::Ptr ZExtInst)) = do
      name <- getNameString i
      (op,op_tp) <- getOperand zext 0 >>= translateValue st
      trg_tp <- valueGetType zext >>= translateType
      let gate = if op_tp==(ProxyArgValue (undefined::Bool) ())
                 then Gate (\inp -> ite (castUntypedExprValue $ op inp)
                                    (constant (1::Integer)) (constant 0)) () (Just name)
                 else Gate (\inp -> castUntypedExprValue $ op inp) () (Just name)
          (res,ngates) = addGate (gates st) gate
      return $ st { gates = ngates
                  , prevInstrs = Map.insert i (UntypedExprValue res) (prevInstrs st) }
    realizeInstr _ st i@(castDown -> Just select) = do
      name <- getNameString i
      (cond,ctp) <- selectInstGetCondition select >>= translateValue st
      (tVal,ttp) <- selectInstGetTrueValue select >>= translateValue st
      (fVal,ftp) <- selectInstGetFalseValue select >>= translateValue st
      withProxyArgValue ttp $
        \(_::a) ann -> do
          let gate = Gate (\inp -> ite (castUntypedExprValue $ cond inp)
                                   (castUntypedExprValue (tVal inp) :: SMTExpr a)
                                   (castUntypedExprValue (fVal inp))) ann (Just name)
              (res,ngates) = addGate (gates st) gate
          return $ st { gates = ngates
                      , prevInstrs = Map.insert i (UntypedExprValue res) (prevInstrs st) }
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
        let nst = withProxyArgValue tp $
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
                              ) (st { prevInstrs = Map.insert i (UntypedExprValue res) (prevInstrs st)
                                    , gates = ngt }) lst
        handlePhis nst is
      Nothing -> return (i:is,st)

    mkITE :: SMTValue a => Ptr BasicBlock -> LLVMInput
             -> [Either (SMTExpr Bool,LLVMInput -> SMTExpr UntypedValue)
                 (Ptr BasicBlock,Either (Ptr Instruction) (SMTExpr UntypedValue))]
             -> SMTExpr a
    mkITE blk inp@(acts,_,latchs) (x:xs)
      = case x of
      Left (act,extr) -> case xs of
        [] -> castUntypedExprValue $ extr inp
        _ -> ite act (castUntypedExprValue $ extr inp) (mkITE blk inp xs)
      Right (src,Right val) -> case xs of
        [] -> castUntypedExprValue val
        _ -> case Map.lookup blk acts of
          Just mp -> case Map.lookup src mp of
            Just act -> ite act (castUntypedExprValue val) (mkITE blk inp xs)
      Right (src,Left instr) -> case Map.lookup instr latchs of
        Just val -> case xs of
          [] -> castUntypedExprValue val
          _ -> case Map.lookup blk acts of
            Just mp -> case Map.lookup src mp of
              Just act -> ite act (castUntypedExprValue val) (mkITE blk inp xs)

declareOutputActs :: (Monad m,Functor m) => RealizationSt -> RealizedGates -> LLVMInput
                     -> SMT' m (LatchActs
                               ,RealizedGates)
declareOutputActs st real inp
  = runStateT (Map.traverseWithKey
               (\trg el
                -> Map.traverseWithKey
                   (\src act -> do
                       real <- get
                       (expr,nreal) <- lift $ declareGate (act inp) real (gates st) inp
                       put nreal
                       return expr
                   ) el
               ) (backwardEdges st)
              ) real

declareOutputInstrs :: (Monad m,Functor m) => RealizationSt -> RealizedGates -> LLVMInput
                       -> SMT' m (ValueMap
                                 ,RealizedGates)
declareOutputInstrs st real inp
  = runStateT (Map.traverseWithKey
               (\instr (UntypedExprValue val) -> do
                   real <- get
                   (expr,nreal) <- lift $ declareGate val real (gates st) inp
                   put nreal
                   return (UntypedExprValue expr)) (Map.intersection (prevInstrs st) (latchInstrs st))
              ) real

declareAssertions :: (Monad m,Functor m) => RealizationSt -> RealizedGates -> LLVMInput
                     -> SMT' m ([SMTExpr Bool]
                               ,RealizedGates)
declareAssertions st real inp
  = runStateT (traverse (\ass -> do
                            real <- get
                            (expr,nreal) <- lift $ declareGate (ass inp) real (gates st) inp
                            put nreal
                            return expr
                        ) (assertions st)
              ) real

declareAssumptions :: (Monad m,Functor m) => RealizationSt -> RealizedGates -> LLVMInput
                     -> SMT' m ([SMTExpr Bool]
                               ,RealizedGates)
declareAssumptions st real inp
  = runStateT (traverse (\ass -> do
                            real <- get
                            (expr,nreal) <- lift $ declareGate (ass inp) real (gates st) inp
                            put nreal
                            return expr
                        ) (assumptions st)
              ) real

getOutput :: RealizationSt -> LLVMInput -> LLVMOutput
getOutput st inp
  = let acts = fmap (fmap (\act -> translateGateExpr (act inp) (gates st) Map.empty inp)) (backwardEdges st)
        latchs = fmap (\(UntypedExprValue xs)
                       -> UntypedExprValue $ translateGateExpr xs (gates st) Map.empty inp) $
                 Map.intersection (prevInstrs st) (latchInstrs st)
    in (acts,latchs)

getModel :: RealizationSt -> Model ValueMap (LatchActs,ValueMap)
getModel real = Model { inpAnnotation = inputInstrs real
                      , stAnnotation = (latchBlks real,latchInstrs real)
                      , initState = \(acts,instrs)
                                     -> app and' [ if src_blk==nullPtr
                                                   then act
                                                   else not' act
                                                 | (trg_blk,srcs) <- Map.toList acts
                                                 , (src_blk,act) <- Map.toList srcs ]
                      , nextState = \(acts,instrs) inp (acts',instrs')
                                     -> let (nacts,ninstrs) = getOutput real (acts,instrs,inp)
                                            as1 = concat $
                                                  fmap Map.elems $
                                                  Map.elems $
                                                  Map.intersectionWith
                                                  (Map.intersectionWith (.==.))
                                                  acts' nacts
                                            as2 = Map.elems $
                                                  Map.intersectionWith
                                                  (\e1 e2
                                                   -> entypeValue (\e1' -> e1' .==. (castUntypedExprValue e2))
                                                      e1)
                                                  instrs' ninstrs
                                        in app and' (as1++as2)
                      , assertion = \(acts,instrs) inp
                                     -> app and' $
                                        fmap (\ass -> translateGateExpr (ass (acts,instrs,inp))
                                                      (gates real) Map.empty (acts,instrs,inp)
                                             ) (assertions real)
                      }

initialState :: RealizationSt -> LatchActs -> SMTExpr Bool
initialState st acts
  = app and' [ if trgBlk==initBlk st &&
                  srcBlk==nullPtr
               then act
               else not' act
             | (trgBlk,srcs) <- Map.toList acts
             , (srcBlk,act) <- Map.toList srcs ]

getConcreteValues :: Monad m => RealizationSt -> LLVMInput -> SMT' m ConcreteValues
getConcreteValues st (acts,instrs,inps) = do
  acts' <- mapM (mapM getValue) acts
  (trg,src) <- case [ (trg,src)
                    | (trg,srcs) <- Map.toList acts'
                    , (src,act) <- Map.toList srcs
                    , act ] of
                 [] -> error "Realization.getConcreteValues: No latch block is active."
                 x:_ -> return x
  vals <- concretizeMap instrs (latchInstrs st)
  inps <- concretizeMap inps (inputInstrs st)
  return $ ConcreteValues { srcBlock = src
                          , trgBlock = trg
                          , latchValues = vals
                          , inputValues = inps }
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

createBlockVars :: String -> RealizationSt -> SMT LatchActs
createBlockVars pre st
  = sequence $ Map.mapWithKey
    (\trg -> sequence . Map.mapWithKey
             (\src _ -> do
                 let name = unsafePerformIO $ do
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
    ) (latchBlks st)

createIntBlockVar :: String -> RealizationSt -> SMT LatchActs
createIntBlockVar name st = do
  v <- varNamed name
  return $ snd $ mapAccumL (mapAccumL (\n _ -> (n+1,v .==. (constant n)))) (0::Integer) (latchBlks st)

createInstrVars :: String -> RealizationSt -> SMT ValueMap
createInstrVars pre st
  = sequence $ Map.mapWithKey
    (\instr ann -> do
        let name = unsafePerformIO $ do
              hn <- hasName instr
              n <- if hn
                   then getNameString instr
                   else return "instr"
              return (pre++n)
        varNamedAnn name ann
    ) (latchInstrs st)

createInputVars :: String -> RealizationSt -> SMT ValueMap
createInputVars pre st
  = sequence $ Map.mapWithKey
    (\instr ann -> do
        let name = unsafePerformIO $ do
              hn <- hasName instr
              n <- if hn
                   then getNameString instr
                   else return "input"
              return (pre++n)
        varNamedAnn name ann
    ) (inputInstrs st)

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
