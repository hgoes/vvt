{-# LANGUAGE ViewPatterns,RankNTypes,ScopedTypeVariables,PackageImports,GADTs,FlexibleInstances,
             TypeFamilies, MultiParamTypeClasses,DeriveDataTypeable #-}
module Realization.BlockWise where

import Realization
import Realization.Common
import Gates
import RSM

import LLVM.FFI
import Foreign.Ptr
import Foreign.Storable (peek)
import Data.Map (Map)
import qualified Data.Map as Map
import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)
import Language.SMTLib2.Pipe (createSMTPipe)
import Data.Typeable
import Data.Foldable (foldlM)
import Data.Traversable (sequence,traverse)
import "mtl" Control.Monad.State (runStateT,get,put,liftIO,lift)
import Data.List (intersperse,sortBy)
import Data.Ord (comparing)
import Prelude hiding (sequence)

type Inputs = (Map (Ptr BasicBlock) (SMTExpr Bool), -- Blocks
               Map (Ptr Instruction) (SMTExpr UntypedValue), -- Latches
               Map (Ptr Instruction) (SMTExpr UntypedValue)) -- Inputs

data Realization = Realization { blocks :: Map (Ptr BasicBlock) ()
                               , latches :: Map (Ptr Instruction) ProxyArgValue
                               , inputs :: Map (Ptr Instruction) ProxyArgValue
                               , gates :: GateMap Inputs
                               , outputBlocks :: Map (Ptr BasicBlock) [Inputs -> SMTExpr Bool]
                               , outputInstrs :: Map (Ptr Instruction) (RealizedValue Inputs)
                               , outputPhis :: Map (Ptr Instruction) [(Inputs -> SMTExpr Bool,
                                                                       RealizedValue Inputs)]
                               , assumes :: [Inputs -> SMTExpr Bool]
                               , initBlk :: Ptr BasicBlock
                               }

realizeValue :: Ptr Value -> Realization
                -> Map (Ptr Instruction) (RealizedValue Inputs) -- ^ Local definitions
                -> IO (RealizedValue Inputs,
                       Realization)
realizeValue (castDown -> Just instr) real defs
  = case Map.lookup instr defs of
     Just val -> return (val,real)
     Nothing -> do
       tp <- getType instr >>= translateType
       let val = withProxyArgValue tp $
                 \(_::a) ann
                 -> NormalValue ann (\(_,l,_) -> castUntypedExprValue
                                                 (l Map.! instr)
                                                 :: SMTExpr a)
       return (val,
               real { latches = Map.insert instr tp (latches real)
                    })
realizeValue (castDown -> Just i) real _ = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return (NormalValue () (const $ constant $ rv/=0),real)
    else return (IntConst (fromIntegral rv),real)

mkGate :: Ptr Instruction -> RealizedValue Inputs
          -> (Inputs -> SMTExpr Bool)
          -> Realization
          -> Map (Ptr Instruction) (RealizedValue Inputs)
          -> IO (Inputs -> SMTExpr Bool,
                 Map (Ptr Instruction) (RealizedValue Inputs),
                 Realization)
mkGate instr (NormalValue ann fun) act real defs = do
  name <- getNameString instr
  let (rexpr,ngates) = addGate (gates real)
                       (Gate { gateTransfer = fun
                             , gateAnnotation = ann
                             , gateName = Just name })
      val = NormalValue ann (const rexpr)
  return (act,
          Map.insert instr val defs,
          real { gates = ngates })
mkGate instr val act real defs
  = return (act,Map.insert instr val defs,real)

realizePhis :: Ptr BasicBlock -> (Inputs -> SMTExpr Bool) -> Ptr BasicBlock
               -> Realization
               -> Map (Ptr Instruction) (RealizedValue Inputs)
               -> IO Realization
realizePhis src act trg real defs = do
  instrs <- getInstList trg >>= ipListToList
  realizePhis' real instrs
  where
    realizePhis' real (i:is) = case castDown i of
      Just phi -> do
        val <- getPhiValue phi 0
        (rval,nreal) <- realizeValue val real defs
        realizePhis' (nreal { outputPhis = Map.insertWith (++) i
                                           [(act,rval)] $
                                           outputPhis nreal }
                     ) is
      Nothing -> return real
    getPhiValue phi n = do
      blk <- phiNodeGetIncomingBlock phi n
      if blk==src
        then phiNodeGetIncomingValue phi n
        else getPhiValue phi (n+1)

realizeInstruction :: Ptr Instruction
                      -> (Inputs -> SMTExpr Bool)
                      -> Realization
                      -> Map (Ptr Instruction) (RealizedValue Inputs)
                      -> IO (Inputs -> SMTExpr Bool,
                             Map (Ptr Instruction) (RealizedValue Inputs),
                             Realization)
realizeInstruction i@(castDown -> Just (phi::Ptr PHINode)) act real defs = do
  tp <- getType i >>= translateType
  return (act,defs,real)
realizeInstruction (castDown -> Just brInst) act real defs = do
  src <- instructionGetParent brInst
  srcName <- getNameString src
  is_cond <- branchInstIsConditional brInst
  if is_cond
    then (do
             ifTrue <- terminatorInstGetSuccessor brInst 0
             ifTrueName <- getNameString ifTrue
             ifFalse <- terminatorInstGetSuccessor brInst 1
             ifFalseName <- getNameString ifFalse
             cond <- branchInstGetCondition brInst
             (vcond,real1) <- realizeValue cond real defs
             let vcond' = asSMTValue vcond
                 condTrue inp = app and' $ [act inp,vcond' inp]
                 condFalse inp = app and' $ [act inp,not' $ vcond' inp]
                 (condTrue',gates1) = addGate (gates real1)
                                      (Gate { gateTransfer = condTrue
                                            , gateAnnotation = ()
                                            , gateName = Just $ srcName++"."++ifTrueName
                                            })
                 (condFalse',gates2) = addGate gates1
                                       (Gate { gateTransfer = condFalse
                                             , gateAnnotation = ()
                                             , gateName = Just $ srcName++"."++ifFalseName
                                             })
                 real2 = real1 { outputBlocks = Map.insertWith (++)
                                                ifTrue [const condTrue'] $
                                                Map.insertWith (++)
                                                ifFalse [const condFalse'] $
                                                outputBlocks real1
                               , gates = gates2
                               }
             real3 <- realizePhis src (const condTrue') ifTrue real2 defs
             real4 <- realizePhis src (const condFalse') ifFalse real3 defs
             return (const (constant False),defs,real4))
    else (do
             trg <- terminatorInstGetSuccessor brInst 0
             trgName <- getNameString trg
             let (cond,gates1) = addGate (gates real)
                                 (Gate { gateTransfer = act
                                       , gateAnnotation = ()
                                       , gateName = Just $ srcName++"."++trgName
                                       })
                 real1 = real { outputBlocks = Map.insertWith (++)
                                               trg [const cond] $
                                               outputBlocks real
                              , gates = gates1
                              }
             real2 <- realizePhis src (const cond) trg real1 defs
             return (const (constant False),defs,real2))
realizeInstruction i@(castDown -> Just call) act real defs = do
  fname <- getFunctionName call
  case fname of
   '_':'_':'u':'n':'d':'e':'f':_ -> do
     tp <- getType i >>= translateType
     withProxyArgValue tp $
       \(_::a) ann
       -> return (act,
                  Map.insert i (NormalValue ann
                                (\(_,_,inps)
                                 -> castUntypedExprValue (inps Map.! i)::SMTExpr a)
                               ) defs,
                  real { inputs = Map.insert i tp (inputs real) })
   "assert" -> do
     cond' <- callInstGetArgOperand call 0
     (cond,real1) <- realizeValue cond' real defs
     let rcond = asSMTValue cond
         (cond',gates1) = addGate (gates real1)
                          (Gate { gateTransfer = \inp -> act inp .&&. rcond inp
                                , gateAnnotation = ()
                                , gateName = Just "assertion"
                                })
         (ncond,gates2) = addGate gates1
                          (Gate { gateTransfer = \inp -> act inp .&&. (not' $ rcond inp)
                                , gateAnnotation = ()
                                , gateName = Just "failure"
                                })
     return (const cond',
             defs,
             real1 { outputBlocks = Map.insertWith (++)
                                    nullPtr [const ncond] $
                                    outputBlocks real1
                   , gates = gates2 })
   "assume" -> do
     cond' <- callInstGetArgOperand call 0
     (cond,real1) <- realizeValue cond' real defs
     return (act,defs,real1 { assumes = (\inp -> (act inp) .=>. (asSMTValue cond inp)):
                                        (assumes real1) })
   _ -> error $ "Unknown function "++fname
realizeInstruction (castDown -> Just ret) acts real defs = do
  rval <- returnInstGetReturnValue ret
  return (acts,defs,real)
realizeInstruction (castDown -> Just sw) act real defs = do
  src <- switchInstGetDefaultDest sw
  srcName <- getNameString src
  cond' <- switchInstGetCondition sw
  (cond'',real1) <- realizeValue cond' real defs
  let cond = asSMTValue cond''
  def <- switchInstGetDefaultDest sw
  defName <- getNameString def
  cases <- switchInstGetCases sw >>=
           mapM (\(val,trg) -> do
                    APInt _ val' <- constantIntGetValue val >>= peek
                    return (val',trg))
  let (defEdge,ngates) = addGate (gates real1)
                         (Gate { gateTransfer = \inp -> app and' ((act inp):
                                                                  [ not' $
                                                                    (cond inp)
                                                                    .==.
                                                                    (constant val)
                                                                  | (val,_) <- cases ])
                               , gateAnnotation = ()
                               , gateName = Just $ srcName++"."++defName
                               })
  real2 <- realizePhis src (const defEdge) def
           (real1 { gates = ngates
                  , outputBlocks = Map.insertWith (++)
                                   def [const defEdge] $
                                   outputBlocks real1
                  }) defs
  real3 <- foldlM (\real (val,trg) -> do
                      trgName <- getNameString trg
                      let (edge,ngates) = addGate (gates real)
                                          (Gate { gateTransfer = \inp -> (act inp) .&&.
                                                                         ((cond inp)
                                                                          .==.
                                                                          (constant val))
                                                , gateAnnotation = ()
                                                , gateName = Just $ srcName++"."++trgName })
                      nreal <- realizePhis src (const edge) trg (real { gates = ngates }) defs
                      return $ nreal { outputBlocks = Map.insertWith (++)
                                                      trg [const edge] $
                                                      outputBlocks nreal
                                     }
                  ) real2 cases
  return (const (constant False),defs,real3)
realizeInstruction i@(castDown -> Just opInst) act real defs = do
  lhs <- getOperand opInst 0
  rhs <- getOperand opInst 1
  op <- binOpGetOpCode opInst
  tp <- valueGetType lhs >>= translateType
  (flhs,real1) <- realizeValue lhs real defs
  (frhs,real2) <- realizeValue rhs real1 defs
  val <- case op of
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
  mkGate i val act real2 defs
realizeInstruction i@(castDown -> Just icmp) act real defs = do
  op <- getICmpOp icmp
  lhs' <- getOperand icmp 0
  rhs' <- getOperand icmp 1
  (lhs,real1) <- realizeValue lhs' real defs
  (rhs,real2) <- realizeValue rhs' real1 defs
  let val = case op of
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
             I_UGT -> case rhs of
               IntConst n -> NormalValue () $
                             \inp -> app or' [(asSMTValue lhs inp) .>.
                                              (constant n)
                                             ,(asSMTValue lhs inp :: SMTExpr Integer) .<. 0]
               _ -> NormalValue () $
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
  mkGate i val act real2 defs
realizeInstruction i@(castDown -> Just (zext::Ptr ZExtInst)) act real defs = do
  op <- getOperand zext 0
  tp <- valueGetType op >>= translateType
  (fop,real1) <- realizeValue op real defs
  let val = if tp==(ProxyArgValue (undefined::Bool) ())
            then ExtBool (asSMTValue fop)
            else (withProxyArgValue tp $
                  \(_::a) ann -> NormalValue ann $
                                 \inp -> asSMTValue fop inp :: SMTExpr a)
  mkGate i val act real1 defs
realizeInstruction i@(castDown -> Just (trunc::Ptr TruncInst)) act real defs = do
  op <- getOperand trunc 0
  tp <- valueGetType i >>= translateType
  (fop,real1) <- realizeValue op real defs
  let val = if tp==(ProxyArgValue (undefined::Bool) ())
            then NormalValue () $
                 \inp -> (asSMTValue fop inp) .==. (constant (1::Integer))
            else fop
  mkGate i val act real1 defs
realizeInstruction i@(castDown -> Just select) act real defs = do
  cond' <- selectInstGetCondition select
  (cond,real1) <- realizeValue cond' real defs
  tVal' <- selectInstGetTrueValue select
  (tVal,real2) <- realizeValue tVal' real1 defs
  fVal' <- selectInstGetFalseValue select
  (fVal,real3) <- realizeValue fVal' real2 defs
  tp <- valueGetType tVal' >>= translateType
  let val = withProxyArgValue tp $
            \(_::a) ann
            -> NormalValue ann $
               \inp -> ite (asSMTValue cond inp)
                       (asSMTValue tVal inp :: SMTExpr a)
                       (asSMTValue fVal inp)
  mkGate i val act real3 defs

realizeFunction :: Ptr Function -> IO Realization
realizeFunction fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  foldlM (\real blk -> do
             instrs <- getInstList blk >>= ipListToList
             let act (acts,_,_) = acts Map.! blk
             (_,defs,nreal) <- foldlM (\(cact,cdefs,creal) instr
                                        -> realizeInstruction instr cact creal cdefs
                                      ) (act,Map.empty,real) instrs
             return $ nreal { blocks = Map.insert blk () (blocks nreal)
                            , outputInstrs = Map.union (outputInstrs nreal) defs
                            }
         ) (Realization { blocks = Map.singleton nullPtr ()
                        , latches = Map.empty
                        , inputs = Map.empty
                        , gates = emptyGateMap
                        , outputBlocks = Map.empty
                        , outputInstrs = Map.empty
                        , outputPhis = Map.empty
                        , assumes = []
                        , initBlk = head blks
                        }) blks >>= finalizeRealization

finalizeRealization :: Realization -> IO Realization
finalizeRealization real = do
  let blks1 = Map.union (outputBlocks real) (fmap (const []) (blocks real))
  (blks2,gates1) <- runStateT
                    (Map.traverseWithKey
                     (\blk acts -> do
                         gates <- get
                         name <- if blk==nullPtr
                                 then return "err"
                                 else liftIO $ getNameString blk
                         let (nact,ngates) = addGate gates
                                             (Gate { gateTransfer = case acts of
                                                      [] -> const (constant False)
                                                      [act] -> act
                                                      _ -> \inp -> app or' [ act inp
                                                                           | act <- acts ]
                                                   , gateAnnotation = ()
                                                   , gateName = Just name })
                         put ngates
                         return [const nact]
                     ) blks1
                    ) (gates real)
  let instrs1 = Map.intersection (outputInstrs real) (latches real)
  (instrs2,gates2) <- runStateT
                      (Map.traverseWithKey
                       (\instr val
                        -> withSMTValue val $
                           \ann fun -> do
                             blk <- liftIO $ instructionGetParent instr
                             gts <- get
                             name <- liftIO $ getNameString instr
                             let nfun inp@(blks,latch,_) = ite (blks Map.! blk)
                                                           (fun inp)
                                                           (castUntypedExprValue $
                                                            latch Map.! instr)
                                 (nval,ngts) = addGate gts
                                               (Gate { gateTransfer = nfun
                                                     , gateAnnotation = ann
                                                     , gateName = Just $ "O."++name
                                                     })
                             put ngts
                             return (NormalValue ann (const nval))
                       ) instrs1
                      ) gates1
  (phis1,gates3) <- runStateT
                    (Map.traverseWithKey
                     (\instr ((c1,val1):rest)
                      -> withSMTValue val1 $
                         \ann f -> do
                           gates <- get
                           name <- liftIO $ getNameString instr
                           let buildITE [] (_,latch,_) = castUntypedExprValue $
                                                         latch Map.! instr
                               buildITE ((c,val):rest) inp
                                 = ite (c inp) (asSMTValue val inp)
                                   (buildITE rest inp)
                               (ncond,ngates) = addGate gates
                                                (Gate { gateTransfer = case rest of
                                                         [] -> f
                                                         _ -> \inp -> ite (c1 inp)
                                                                      (f inp)
                                                                      (buildITE rest inp)
                                                      , gateAnnotation = ann
                                                      , gateName = Just name
                                                      })
                           put ngates
                           return (NormalValue ann (const ncond))
                     ) (outputPhis real)
                    ) gates2
  return $ real { outputBlocks = blks2
                , outputInstrs = Map.union instrs2 phis1
                , gates = gates3 }

translateType :: Ptr Type -> IO ProxyArgValue
translateType (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return (ProxyArgValue (undefined::Bool) ())
    _ -> return (ProxyArgValue (undefined::Integer) ())
translateType tp = do
  typeDump tp
  error "Can't translate type"

instance TransitionRelation Realization where
  type State Realization = (Map (Ptr BasicBlock) (SMTExpr Bool),
                            Map (Ptr Instruction) (SMTExpr UntypedValue))
  type Input Realization = Map (Ptr Instruction) (SMTExpr UntypedValue)
  type RevState Realization = Map Integer (Either (Ptr BasicBlock) (Ptr Instruction))
  type PredicateExtractor Realization = RSMState (Ptr BasicBlock) (Ptr Instruction)
  createStateVars pre st = do
    blks <- sequence $ Map.mapWithKey
            (\blk _ -> do
                name <- if blk==nullPtr
                        then return "err"
                        else liftIO $ getNameString blk
                varNamed (pre++"L."++name)
            ) (blocks st)
    instrs <- sequence $ Map.mapWithKey
              (\instr tp -> do
                  name <- liftIO $ do
                    hn <- hasName instr
                    n <- if hn
                         then getNameString instr
                         else return "instr"
                    return (pre++"L."++n)
                  varNamedAnn name tp
              ) (latches st)
    return (blks,instrs)
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
      ) (inputs st)
  initialState real (blks,_) = app and' [ if blk==initBlk real
                                          then act
                                          else not' act
                                        | (blk,act) <- Map.toList blks ]
  stateInvariant real (blks,_)
    = app or' $
      fmap (app and') $
      exactlyOne [] (Map.elems blks)
    where
      exactlyOne prev [x] = [prev++[x]]
      exactlyOne prev (x:xs)
        = (prev++(x:(fmap not' xs))):
          (exactlyOne (prev++[not' x]) xs)
  declareNextState real (blks,latch) inp _ gts = do
    (nblks,gts1) <- runStateT
                    (Map.traverseWithKey
                     (\trg [act] -> do
                         gt <- get
                         (expr,ngt) <- lift $ declareGate (act inp') gt
                                       (gates real) inp'
                         put ngt
                         return expr
                     ) (outputBlocks real)
                    ) gts
    (ninstrs,gts2) <- runStateT
                      (Map.traverseWithKey
                       (\instr val -> withSMTValue val $
                                      \ann fun -> do
                                        gt <- get
                                        (expr,ngt) <- lift $ declareGate (fun inp') gt
                                                      (gates real) inp'
                                        put ngt
                                        return (UntypedExprValue expr)
                       ) (outputInstrs real)
                      ) gts1
    return ((nblks,ninstrs),gts2)
    where
      inp' = (blks,latch,inp)
  declareAssertions _ (blks,_) inp gts
    = return ([not' $ blks Map.! nullPtr],gts)
  declareAssumptions real (blks,latch) inp gts
    = runStateT (traverse (\ass -> do
                              gt <- get
                              (expr,ngt) <- lift $ declareGate (ass inp') gt
                                            (gates real) inp'
                              put ngt
                              return expr
                          ) (assumes real)
                ) gts
    where
      inp' = (blks,latch,inp)
  annotationState real = (blocks real,latches real)
  annotationInput real = inputs real
  defaultPredicateExtractor _ = return emptyRSM
  extractPredicates real rsm full lifted = do
    let blk = case [ blk | (blk,True) <- Map.toList (fst full) ] of
          [b] -> b
        nrsm = addRSMState blk (Map.mapMaybe id $ snd lifted) rsm
    (nrsm',props) <- mineStates (createSMTPipe "z3" ["-smt2","-in"]) nrsm
    return (nrsm',fmap (\prop (_,vals) -> prop vals) props)
  createRevState pre st = do
    (blks,instrs) <- createStateVars pre st
    let rmp1 = Map.foldlWithKey
               (\rmp blk (Var idx _)
                 -> Map.insert idx (Left blk) rmp
               ) Map.empty blks
        rmp2 = Map.foldlWithKey
               (\rmp instr (Var idx _)
                 -> Map.insert idx (Right instr) rmp
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
                                  -> case entypeValue cast (instrs Map.! instr) of
                                      Just r -> r
                              _ -> expr)
                     ) () trm
  renderPartialState _ (blks,instrs) = do
    blk <- case [ () | (_,Nothing) <- Map.toList blks ] of
      [] -> case [ blk | (blk,Just True) <- Map.toList blks ] of
        [blk] -> if blk==nullPtr
                 then return "err"
                 else liftIO $ getNameString blk
      _ -> findBlk [ (blk,act)
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
  suggestedPredicates mdl = blkPredicates (blocks mdl)++
                            splitPredicates (cmpPredicates (latches mdl))
