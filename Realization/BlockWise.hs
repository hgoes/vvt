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

import System.IO.Unsafe

type Inputs = (Map (Ptr BasicBlock) (SMTExpr Bool), -- Blocks
               Map (Ptr Instruction) SymInstr, -- Latches
               Map (Ptr Instruction) SymInstr) -- Inputs

data Realization = Realization { blocks :: Map (Ptr BasicBlock) ()
                               , latches :: Map (Ptr Instruction) InstrType
                               , inputs :: Map (Ptr Instruction) InstrType
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
       let val = NormalValue tp (\(_,l,_) -> case Map.lookup instr l of
                                  Nothing -> error $ "Instruction "++show (unsafePerformIO $ getNameString instr)++" not found."
                                  Just i -> i)
       return (val,
               real { latches = Map.insert instr tp (latches real)
                    })
realizeValue (castDown -> Just i) real _ = do
  tp <- getType i
  bw <- getBitWidth tp
  v <- constantIntGetValue i
  rv <- apIntGetSExtValue v
  if bw==1
    then return (NormalValue TpBool (const $ SymBool $ constant $ rv/=0),real)
    else return (IntConst (fromIntegral rv),real)
realizeValue (castDown -> Just undef) real _ = do
  tp <- getType (undef::Ptr UndefValue)
  defaultValue tp
  where
    defaultValue (castDown -> Just itp) = do
      bw <- getBitWidth itp
      if bw==1
        then return (NormalValue TpBool (const $ SymBool $ constant False),real)
        else return (IntConst 0,real)

mkGate :: Ptr Instruction -> RealizedValue Inputs
          -> (Inputs -> SMTExpr Bool)
          -> Realization
          -> Map (Ptr Instruction) (RealizedValue Inputs)
          -> IO (Inputs -> SMTExpr Bool,
                 Map (Ptr Instruction) (RealizedValue Inputs),
                 Realization)
mkGate instr (NormalValue ann fun) act real defs = do
  name <- getNameString instr
  let (rexpr,ngates) = addSymGate (gates real) ann fun (Just name)
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
             let vcond' = symBool . asSMTValue vcond EncInt
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
   '_':'_':'n':'o':'n':'d':'e':'t':_ -> do
     tp <- getType i >>= translateType
     return (act,
             Map.insert i (NormalValue tp
                           (\(_,_,inps)
                            -> case Map.lookup i inps of
                                Nothing -> error $ "Input "++show (unsafePerformIO $ getNameString i)++" not found."
                                Just i' -> i')
                          ) defs,
             real { inputs = Map.insert i tp (inputs real) })
   "assert" -> do
     cond' <- callInstGetArgOperand call 0
     (cond,real1) <- realizeValue cond' real defs
     let rcond = symBool . asSMTValue cond EncInt
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
     return (act,defs,real1 { assumes = (\inp -> (act inp) .=>. (symBool $ asSMTValue cond EncInt inp)):
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
  let cond = asInteger' EncInt cond''
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
   Add -> return $ NormalValue tp $
          \inp -> SymInteger $ (asInteger' EncInt flhs inp) +
                  (asInteger' EncInt frhs inp)
   Sub -> return $ NormalValue tp $
          \inp -> SymInteger $ (asInteger' EncInt flhs inp) -
                  (asInteger' EncInt frhs inp)
   Mul -> return $ NormalValue tp $
          \inp -> SymInteger $ (asInteger' EncInt flhs inp) *
                  (asInteger' EncInt frhs inp)
   And -> if tp==TpBool
          then return $ NormalValue TpBool $
               \inp -> SymBool $ (symBool $ asSMTValue flhs EncInt inp) .&&.
                       (symBool $ asSMTValue frhs EncInt inp)
          else error "And operator can't handle non-bool inputs."
   Or -> if tp==TpBool
         then return $ NormalValue TpBool $
              \inp -> SymBool $ (symBool $ asSMTValue flhs EncInt inp) .||.
                      (symBool $ asSMTValue frhs EncInt inp)
         else (if tp==TpInteger
               then return (case flhs of
                             OrList xs -> case frhs of
                               OrList ys -> OrList $ xs++ys
                               _ -> OrList $ xs++[asSMTValue frhs EncInt]
                             _ -> case frhs of
                               OrList ys -> OrList $ [asSMTValue flhs EncInt]++ys
                               _ -> OrList [asSMTValue flhs EncInt,
                                            asSMTValue frhs EncInt])
               else error "Or operator can only handle bool and int inputs.")
   Xor -> case (flhs,frhs) of
     (ExtBool l,ExtBool r) -> return $ ExtBool (\inp -> app xor
                                                        [l inp
                                                        ,r inp])
     (ExtBool l,IntConst 1) -> return $ ExtBool (\inp -> not' $ l inp)
     _ -> if tp==TpBool
          then return $ NormalValue TpBool $
               \inp -> SymBool $ app xor
                       [symBool $ asSMTValue flhs EncInt inp
                       ,symBool $ asSMTValue frhs EncInt inp]
          else error "Xor operator can't handle non-bool inputs."
   Shl -> case frhs of
     IntConst rv
       -> return $ NormalValue TpInteger $
          \inp -> SymInteger $ (asInteger' EncInt flhs inp)*
                  (constant $ 2^rv)
   LShr -> case frhs of
     IntConst rv
       -> return $ NormalValue TpInteger $
          \inp -> SymInteger $ (asInteger' EncInt flhs inp) `div'` (constant $ 2^rv)
   _ -> error $ "Unknown operator: "++show op
  mkGate i val act real2 defs
realizeInstruction i@(castDown -> Just icmp) act real defs = do
  op <- getICmpOp icmp
  lhs' <- getOperand icmp 0
  rhs' <- getOperand icmp 1
  (lhs,real1) <- realizeValue lhs' real defs
  (rhs,real2) <- realizeValue rhs' real1 defs
  let val = encodeCmpOp EncInt op lhs rhs
  mkGate i (NormalValue TpBool (SymBool . val)) act real2 defs
realizeInstruction i@(castDown -> Just (zext::Ptr ZExtInst)) act real defs = do
  op <- getOperand zext 0
  tp <- valueGetType op >>= translateType
  (fop,real1) <- realizeValue op real defs
  let val = if tp==TpBool
            then ExtBool (symBool . asSMTValue fop EncInt)
            else NormalValue tp $
                 \inp -> asSMTValue fop EncInt inp
  mkGate i val act real1 defs
realizeInstruction i@(castDown -> Just (trunc::Ptr TruncInst)) act real defs = do
  op <- getOperand trunc 0
  tp <- valueGetType i >>= translateType
  (fop,real1) <- realizeValue op real defs
  let val = if tp==TpBool
            then NormalValue TpBool $
                 \inp -> SymBool $ (asInteger' EncInt fop inp) .==. (constant 1)
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
  let val = NormalValue tp $
            \inp -> symITE (symBool $ asSMTValue cond EncInt inp)
                    (asSMTValue tVal EncInt inp)
                    (asSMTValue fVal EncInt inp)
  mkGate i val act real3 defs

realizeFunction :: Ptr Function -> IO Realization
realizeFunction fun = do
  blks <- getBasicBlockList fun >>= ipListToList
  foldlM (\real blk -> do
             instrs <- getInstList blk >>= ipListToList
             let act (acts,_,_) = case Map.lookup blk acts of
                   Nothing -> error $ "Activation for block "++(show $ unsafePerformIO $ getNameString blk)++" not found."
                   Just a -> a
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
                        -> do
                          let (tp,fun) = toSMTValue val EncInt
                          blk <- liftIO $ instructionGetParent instr
                          gts <- get
                          name <- liftIO $ getNameString instr
                          let nfun inp@(blks,latch,_) = case Map.lookup blk blks of
                                Nothing -> error $ "Activation for block "++show (unsafePerformIO $ getNameString blk)++" not found."
                                Just act -> case Map.lookup instr latch of
                                  Nothing -> error $ "Latch variable "++show (unsafePerformIO $ getNameString instr)++" not found."
                                  Just i ->  symITE act (fun inp) i
                              (nval,ngts) = addSymGate gts tp nfun (Just $ "O."++name)
                          put ngts
                          return (NormalValue tp (const nval))
                       ) instrs1
                      ) gates1
  (phis1,gates3) <- runStateT
                    (Map.traverseWithKey
                     (\instr ((c1,val1):rest)
                      -> do
                        let (tp,f) = toSMTValue val1 EncInt
                        gates <- get
                        name <- liftIO $ getNameString instr
                        let buildITE [(_,val)] inp
                              | not $ Map.member instr (latches real) = asSMTValue val EncInt inp
                            buildITE [] (_,latch,_) = case Map.lookup instr latch of
                              Nothing -> error $ "Latch variable "++show (unsafePerformIO $ getNameString instr)++" not found."
                              Just i -> i
                            buildITE ((c,val):rest) inp
                              = symITE (c inp) (asSMTValue val EncInt inp)
                                (buildITE rest inp)
                            (ncond,ngates) = addSymGate gates tp
                                             (case rest of
                                               [] -> f
                                               _ -> \inp -> symITE (c1 inp)
                                                            (f inp)
                                                            (buildITE rest inp))
                                             (Just name)
                        put ngates
                        return (NormalValue tp (const ncond))
                     ) (outputPhis real)
                    ) gates2
  return $ real { outputBlocks = blks2
                , outputInstrs = Map.union instrs2 phis1
                , gates = gates3 }

translateType :: Ptr Type -> IO InstrType
translateType (castDown -> Just itp) = do
  bw <- getBitWidth itp
  case bw of
    1 -> return TpBool
    _ -> return TpInteger
translateType tp = do
  typeDump tp
  error "Can't translate type"

instance TransitionRelation Realization where
  type State Realization = (Map (Ptr BasicBlock) (SMTExpr Bool),
                            Map (Ptr Instruction) SymInstr)
  type Input Realization = Map (Ptr Instruction) SymInstr
  type RevState Realization = Map Integer (Either (Ptr BasicBlock) (Ptr Instruction))
  type PredicateExtractor Realization = RSMState (Ptr BasicBlock) (Ptr Instruction)
  type RealizationProgress Realization = RealizedGates
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
                  argVarsAnnNamed name tp
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
          argVarsAnnNamed name ann
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
                       (\instr val -> do
                           let fun = asSMTValue val EncInt
                           gt <- get
                           (expr,ngt) <- lift $ declareSymGate (fun inp') gt
                                         (gates real) inp'
                           put ngt
                           return expr
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
        nrsm = addRSMState blk (Map.mapMaybe (\el -> do
                                                 rel <- el
                                                 case rel of
                                                  ValInteger v -> Just v
                                                  _ -> Nothing
                                             ) $ snd lifted) rsm
    (nrsm',props) <- mineStates (createSMTPipe "z3" ["-smt2","-in"]) nrsm
    return (nrsm',fmap (\prop (_,vals) -> prop (symInt . (vals Map.!))) props)
  createRevState pre st = do
    (blks,instrs) <- createStateVars pre st
    let rmp1 = Map.foldlWithKey
               (\rmp blk (Var idx _)
                 -> Map.insert idx (Left blk) rmp
               ) Map.empty blks
        rmp2 = Map.foldlWithKey
               (\rmp instr e -> case e of
                 SymInteger (Var idx _) -> Map.insert idx (Right instr) rmp
                 SymBool (Var idx _) -> Map.insert idx (Right instr) rmp
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
                                      SymInteger v -> case cast v of
                                        Just r -> r
                                      SymBool v -> case cast v of
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
  suggestedPredicates mdl = fmap (\p -> (True,p)) $
                            blkPredicates (blocks mdl)++
                            splitPredicates (cmpPredicates (latches mdl))
  startingProgress _ = Map.empty
