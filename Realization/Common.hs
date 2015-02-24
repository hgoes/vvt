{-# LANGUAGE ExistentialQuantification,RankNTypes,ViewPatterns,ScopedTypeVariables,
             PackageImports,DeriveDataTypeable,TypeFamilies #-}
module Realization.Common where

import Gates
import PartialArgs

import LLVM.FFI hiding (Vector)
import Language.SMTLib2
import Language.SMTLib2.Internals
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.C.String
import Data.Typeable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Linear
import "mtl" Control.Monad.State (StateT,runStateT,get,put,lift)
import Prelude hiding (mapM)
import Data.Traversable (mapM,mapAccumL)
import qualified Data.Text as T
import Data.AttoLisp (Lisp,lisp)
import Language.SMTLib2.Pipe
import Data.Fix
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Attoparsec
import System.IO
import Data.Maybe (catMaybes)

data RealizedValue inp = NormalValue InstrType (inp -> SymInstr)
                       | IntConst Integer
                       | OrList [inp -> SymInstr]
                       | ExtBool (inp -> SMTExpr Bool)

data SymInstr = SymBool { symBool :: SMTExpr Bool }
              | SymInteger { symInt :: SMTExpr Integer }
              | SymLinear (Vector (SMTExpr Integer)) (SMTExpr Integer)
              deriving (Eq,Ord,Show,Typeable)

data ValInstr = ValBool Bool
              | ValInteger Integer
              | ValLinear (Vector Integer) Integer
              deriving (Eq,Ord,Show,Typeable)

data InstrType = TpBool
               | TpInteger
               | TpLinear Int
               deriving (Eq,Ord,Show,Typeable)

data IntegerEncoding inp = EncInt
                         | EncLin (Vector (Ptr Instruction)) (inp -> [SMTExpr Integer])

toSMTValue :: RealizedValue inp
             -> IntegerEncoding inp
             -> (InstrType,inp -> SymInstr)
toSMTValue (NormalValue tp f) _ = (tp,f)
toSMTValue (IntConst x) EncInt = (TpInteger,const $ SymInteger $ constant x)
toSMTValue (IntConst x) (EncLin vars extr)
  = (TpLinear $ Vec.length vars,
     const $ SymLinear (fmap (const 0) vars) (constant x))
toSMTValue (OrList _) _ = error "Or operator can only be applied to boolean values."
toSMTValue (ExtBool f) EncInt = (TpInteger,
                                 \inp -> SymInteger $ ite (f inp) (constant 1) (constant 0))
toSMTValue (ExtBool f) (EncLin vars extr)
  = (TpLinear $ Vec.length vars,
     \inp -> SymLinear (fmap (const 0) vars)
             (ite (f inp) (constant 1) (constant 0)))

asSMTValue :: RealizedValue inp -> IntegerEncoding inp -> inp -> SymInstr
asSMTValue val enc = snd (toSMTValue val enc)

asInteger :: IntegerEncoding inp -> SymInstr -> inp -> SMTExpr Integer
asInteger EncInt (SymInteger v) _ = v
asInteger (EncLin _ extr) (SymLinear vec c) inp
  = app plus $ c:zipWith (*) (Vec.toList vec) (extr inp)

asInteger' :: IntegerEncoding inp -> RealizedValue inp -> inp -> SMTExpr Integer
asInteger' enc val inp = asInteger enc (asSMTValue val enc inp) inp

asSMTUntyped :: SymInstr -> SMTExpr Untyped
asSMTUntyped (SymBool x) = UntypedExpr x
asSMTUntyped (SymInteger x) = UntypedExpr x

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

getProgram :: Bool -> Bool -> String -> String -> IO (Ptr Module,Ptr Function)
getProgram dump optimize entry file = do
  loadRes <- getFileMemoryBufferSimple file
  buf <- case loadRes of
    Left err -> error $ "Error while loading bitcode file: "++show err
    Right b -> return b
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  applyOptimizations optimize mod entry
  if dump
    then moduleDump mod
    else return ()
  fun <- moduleGetFunctionString mod entry
  return (mod,fun)

applyOptimizations :: Bool -> Ptr Module -> String -> IO ()
applyOptimizations optimize mod entry = do
  pm <- newPassManager
  mapM (\(APass c) -> do
           pass <- c
           passManagerAdd pm pass) (passes optimize entry)
  passManagerRun pm mod
  deletePassManager pm

data APass = forall p. PassC p => APass (IO (Ptr p))

passes :: Bool -> String -> [APass]
passes optimize entry
  = if optimize
    then [internalizer
         ,APass createTypeBasedAliasAnalysisPass
          --,APass createScopedNoAliasAAPass
         ,APass createBasicAliasAnalysisPass
         ,APass createIPSCCPPass
         ,APass createGlobalOptimizerPass
         ,APass createDeadArgEliminationPass
         ,APass createInstructionCombiningPass
         ,APass createCFGSimplificationPass
         ,APass createPruneEHPass
         ,APass (createFunctionInliningPass 100000)
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
         ,APass createIndVarSimplifyPass
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
    else [APass createPromoteMemoryToRegisterPass
         ,internalizer
         ,APass createInstructionNamerPass]
  where
    internalizer = APass (do
                             m <- newCString entry
                             arr <- newArray [m]
                             export_list <- newArrayRef arr 1
                             --export_list <- newArrayRefEmpty
                             createInternalizePass export_list)

splitPredicates :: [p -> SMTExpr Bool]
                   -> [(a,p) -> SMTExpr Bool]
splitPredicates = fmap (\pred (_,vs) -> pred vs)

cmpPredicates :: Ord i => Map i InstrType
                 -> [Map i SymInstr -> SMTExpr Bool]
cmpPredicates instrs = mkCmps (Map.toList instrs)
  where
    mkCmps [] = []
    mkCmps [x] = []
    mkCmps ((i,TpInteger):xs)
      = (mkCmps' i xs)++
        (mkCmps xs)
    mkCmps (_:xs) = mkCmps xs

    mkCmps' i [] = []
    mkCmps' i ((j,TpInteger):xs)
      = (\instrs
         -> (symInt (instrs Map.! i))
            .<.
            (symInt (instrs Map.! j))
        ):
        (\instrs
         -> (symInt (instrs Map.! i))
            .>.
            (symInt (instrs Map.! j))
        ):
        (\instrs
         -> (symInt (instrs Map.! i))
            .<=.
            (symInt (instrs Map.! j))
        ):
        (mkCmps' i xs)
    mkCmps' i (_:xs) = mkCmps' i xs

blkPredicates :: Map (Ptr BasicBlock) ()
                 -> [(Map (Ptr BasicBlock) (SMTExpr Bool),a) -> SMTExpr Bool]
blkPredicates blks = mkActs (Map.keys blks) []
  where
    mkActs [] _ = []
    mkActs (blk:xs) ys = (\(acts,_) -> app and'
                                       ((acts Map.! blk):
                                        [ not' $ acts Map.! blk'
                                        | blk' <- xs++ys ])
                         ):(mkActs xs (blk:ys))

symITE :: SMTExpr Bool -> SymInstr -> SymInstr -> SymInstr
symITE cond (SymBool x) (SymBool y) = SymBool (ite cond x y)
symITE cond (SymInteger x) (SymInteger y) = SymInteger (ite cond x y)
symITE cond (SymLinear v1 c1) (SymLinear v2 c2)
  = SymLinear (Vec.zipWith (ite cond) v1 v2) (ite cond c1 c2)

realizedValueITE :: IntegerEncoding inp -> (inp -> SMTExpr Bool)
                 -> RealizedValue inp -> RealizedValue inp -> RealizedValue inp
realizedValueITE enc cond (ExtBool x) (ExtBool y)
  = ExtBool (\inp -> ite (cond inp) (x inp) (y inp))
realizedValueITE enc cond x y
  = NormalValue xtp (\inp -> symITE (cond inp) (x' inp) (y' inp))
  where
    (xtp,x') = toSMTValue x enc
    (ytp,y') = toSMTValue y enc

symEq :: IntegerEncoding inp -> SymInstr -> SymInstr -> inp -> SMTExpr Bool
symEq _ (SymBool x) (SymBool y) _ = x.==.y
symEq EncInt (SymInteger x) (SymInteger y) _ = x.==.y
symEq (EncLin vars extr) (SymLinear v1 c1) (SymLinear v2 c2) inp
  = lhs .==. rhs
  where
    lhs = app plus $ c1:(zipWith (*) (Vec.toList v1) (extr inp))
    rhs = app plus $ c2:(zipWith (*) (Vec.toList v2) (extr inp))

symAdd :: SymInstr -> SymInstr -> SymInstr
symAdd (SymInteger x) (SymInteger y) = SymInteger $ x+y
symAdd (SymLinear v1 c1) (SymLinear v2 c2) = SymLinear (v1 ^+^ v2) (c1+c2)
symAdd l r = error $ "Cannot add "++show l++" and "++show r

symSub :: SymInstr -> SymInstr -> SymInstr
symSub (SymInteger x) (SymInteger y) = SymInteger $ x-y
symSub (SymLinear v1 c1) (SymLinear v2 c2) = SymLinear (v1 ^-^ v2) (c1-c2)

addSymGate :: Args inp => GateMap inp -> InstrType -> (inp -> SymInstr) -> Maybe String
              -> (SymInstr,GateMap inp)
addSymGate gts TpBool f name
  = let (expr,ngts) = addGate gts (Gate { gateTransfer = symBool.f
                                        , gateAnnotation = ()
                                        , gateName = name })
    in (SymBool expr,ngts)
addSymGate gts TpInteger f name
  = let (expr,ngts) = addGate gts (Gate { gateTransfer = symInt.f
                                        , gateAnnotation = ()
                                        , gateName = name })
    in (SymInteger expr,ngts)
addSymGate gts (TpLinear len) f name
  = (SymLinear nvec nc,gts2)
  where
    (gts1,nvec) = mapAccumL (\cgts i -> let (expr,ngts) = addGate cgts
                                                          (Gate { gateTransfer = extr i
                                                                , gateAnnotation = ()
                                                                , gateName = name })
                                        in (ngts,expr)
                            ) gts (Vec.enumFromN 0 len)
    (nc,gts2) = addGate gts1
                (Gate { gateTransfer = \inp -> let ~(SymLinear _ c) = f inp
                                               in c
                      , gateAnnotation = ()
                      , gateName = name })
    extr i inp = let ~(SymLinear vec _) = f inp
                 in vec Vec.! i

declareSymGate :: (Args inp,Monad m) => SymInstr -> RealizedGates -> GateMap inp -> inp -> SMT' m (SymInstr,RealizedGates)
declareSymGate (SymBool e) gts mp inp = do
  (e',mp') <- declareGate e gts mp inp
  return (SymBool e',mp')
declareSymGate (SymInteger e) gts mp inp = do
  (e',mp') <- declareGate e gts mp inp
  return (SymInteger e',mp')
declareSymGate (SymLinear vec c) gts mp inp = do
  (vec',gts1) <- runStateT
                 (mapM (\el -> do
                           cgts <- get
                           (el',ngts) <- lift $ declareGate el cgts mp inp
                           put ngts
                           return el'
                       ) vec) gts
  (c',gts2) <- declareGate c gts1 mp inp
  return (SymLinear vec' c',gts2)

encodeCmpOp :: IntegerEncoding inp -> ICmpOp -> RealizedValue inp -> RealizedValue inp
               -> inp -> SMTExpr Bool
encodeCmpOp enc I_EQ (OrList xs) (IntConst 0) inp
  = app and' [ asInteger enc (x inp) inp .==. 0
             | x <- xs ]
encodeCmpOp enc I_EQ (IntConst 0) (OrList xs) inp
  = app and' [ asInteger enc (x inp) inp .==. 0
             | x <- xs ]
encodeCmpOp enc I_EQ lhs rhs inp
  = symEq enc lhs' rhs' inp
  where
    lhs' = asSMTValue lhs enc inp
    rhs' = asSMTValue rhs enc inp
encodeCmpOp enc I_NE (OrList xs) (IntConst 0) inp
  = not' $ app and' [ asInteger enc (x inp) inp .==. 0
                    | x <- xs ]
encodeCmpOp enc I_NE (IntConst 0) (OrList xs) inp
  = not' $ app and' [ asInteger enc (x inp) inp .==. 0
                    | x <- xs ]
encodeCmpOp enc I_NE lhs rhs inp
  = not' $ symEq enc lhs' rhs' inp
  where
    lhs' = asSMTValue lhs enc inp
    rhs' = asSMTValue rhs enc inp
encodeCmpOp enc I_SGE lhs rhs inp
  = (asInteger' enc lhs inp) .>=.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_UGE lhs rhs inp
  = (asInteger' enc lhs inp) .>=.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_SGT lhs rhs inp
  = (asInteger' enc lhs inp) .>.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_UGT lhs (IntConst n) inp
  = app or' [(asInteger' enc lhs inp) .>.
             (constant n)
            ,(asInteger' enc lhs inp) .<. 0]
encodeCmpOp enc I_UGT lhs rhs inp
  = (asInteger' enc lhs inp) .>.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_SLE lhs rhs inp
  = (asInteger' enc lhs inp) .<=.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_ULE lhs rhs inp
  = (asInteger' enc lhs inp) .<=.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_SLT (OrList xs) (IntConst 0) inp
  = app and' [ asInteger enc (x inp) inp .<. 0
             | x <- xs ]
encodeCmpOp enc I_SLT lhs rhs inp
  = (asInteger' enc lhs inp) .<.
    (asInteger' enc rhs inp)
encodeCmpOp enc I_ULT lhs rhs inp
  = (asInteger' enc lhs inp) .<.
    (asInteger' enc rhs inp)

instance Args SymInstr where
  type ArgAnnotation SymInstr = InstrType
  foldExprs f s ~(SymBool expr) TpBool = do
    (s',expr') <- f s expr ()
    return (s',SymBool expr')
  foldExprs f s ~(SymInteger expr) TpInteger = do
    (s',expr') <- f s expr ()
    return (s',SymInteger expr')
  foldExprs f s ~(SymLinear vec c) (TpLinear len) = do
    (vec',s1) <- runStateT (Vec.generateM len
                            (\i -> do
                                cs <- get
                                (ns,el') <- lift $ f s (vec Vec.! i) ()
                                put ns
                                return el')
                           ) s
    (s2,c') <- f s1 c ()
    return (s2,SymLinear vec' c')
  foldsExprs f s lst TpBool = do
    let lst' = fmap (\(~(SymBool x),y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ()
    return (ns,fmap SymBool rlst,SymBool res)
  foldsExprs f s lst TpInteger = do
    let lst' = fmap (\(~(SymInteger x),y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ()
    return (ns,fmap SymInteger rlst,SymInteger res)
  foldsExprs f s lst (TpLinear len) = do
    (nlst,s1) <- runStateT
                 (mapM (\i -> do
                           cs <- get
                           let els = fmap (\(~(SymLinear vec _),x) -> (vec Vec.! i,x)) lst
                           (ns,nels,nel) <- lift $ foldsExprs f cs els ()
                           put ns
                           return (nels,nel)
                       ) [0..(len-1)]
                 ) s
    (s2,ncs,nc) <- foldsExprs f s1 (fmap (\(~(SymLinear _ c),x) -> (c,x)) lst) ()
    let resVec = SymLinear (Vec.fromList (fmap snd nlst)) nc
        resVecs = buildVecs (fmap fst nlst) ncs
        buildVecs _ [] = []
        buildVecs lst (c:cs) = (SymLinear (Vec.fromList $ fmap head lst) c):
                               (buildVecs (fmap tail lst) cs)
    return (s2,resVecs,resVec)
  extractArgAnnotation (SymBool _) = TpBool
  extractArgAnnotation (SymInteger _) = TpInteger
  extractArgAnnotation (SymLinear vec _) = TpLinear (Vec.length vec)
  toArgs TpBool es = case es of
    [] -> Nothing
    e:es -> do
      e' <- entype cast e
      return (SymBool e',es)
  toArgs TpInteger es = case es of
    [] -> Nothing
    e:es -> do
      e' <- entype cast e
      return (SymInteger e',es)
  toArgs (TpLinear len) es = do
    (vec,c,rest) <- getEls len es
    return (SymLinear (Vec.fromList vec) c,rest)
    where
      getEls _ [] = Nothing
      getEls 0 (e:es) = do
        e' <- entype cast e
        return ([],e',es)
      getEls n (e:es) = do
        e' <- entype cast e
        (vec,c,rest) <- getEls (n-1) es
        return (e':vec,c,rest)
  fromArgs (SymBool e) = [UntypedExpr e]
  fromArgs (SymInteger e) = [UntypedExpr e]
  fromArgs (SymLinear vec c) = fmap UntypedExpr (Vec.toList vec ++ [c])
  getTypes _ TpBool = [ProxyArg (undefined::Bool) ()]
  getTypes _ TpInteger = [ProxyArg (undefined::Integer) ()]
  getTypes _ (TpLinear n) = replicate (n+1) (ProxyArg (undefined::Integer) ())

instance LiftArgs SymInstr where
  type Unpacked SymInstr = ValInstr
  liftArgs ~(ValBool c) TpBool = SymBool (constant c)
  liftArgs ~(ValInteger c) TpInteger = SymInteger (constant c)
  liftArgs ~(ValLinear vec c) (TpLinear sz) = SymLinear (fmap constant vec) (constant c)
  unliftArgs (SymBool e) unp = do
    e' <- unp e
    return $ ValBool e'
  unliftArgs (SymInteger e) unp = do
    e' <- unp e
    return $ ValInteger e'
  unliftArgs (SymLinear vec c) unp = do
    vec' <- mapM unp vec
    c' <- unp c
    return (ValLinear vec' c')

instance PartialArgs SymInstr where
  type PartialValue SymInstr = Maybe ValInstr
  maskValue _ val (x:xs) = (if x
                            then val
                            else Nothing,xs)
  unmaskValue _ val = Just val
  assignPartial _ Nothing = [Nothing]
  assignPartial (SymBool c) (Just (ValBool v)) = [Just $ c.==.(constant v)]
  assignPartial (SymInteger c) (Just (ValInteger v)) = [Just $ c.==.(constant v)]

parseLLVMPreds :: Handle -> [Ptr BasicBlock] -> [Ptr Instruction]
               -> (a -> Ptr Instruction -> SymInstr)
               -> (a -> Ptr BasicBlock -> SMTExpr Bool)
               -> IO [a -> SMTExpr Bool]
parseLLVMPreds h bbs instrs getInstr getBB = do
  instrLst <- mapM (\instr -> do
                       iHasName <- hasName instr
                       if iHasName
                         then (do
                                  name <- getNameString instr
                                  return $ Just (T.pack name,instr))
                         else return Nothing) instrs
  bbLst <- mapM (\bb -> if bb==nullPtr
                        then return $ Just (T.pack "err",bb)
                        else (do
                                 bHasName <- hasName bb
                                 if bHasName
                                   then (do
                                            name <- getNameString bb
                                            return $ Just (T.pack name,bb))
                                   else return Nothing)) bbs
  let instrMp = Map.fromList $ catMaybes instrLst
      bbMp = Map.fromList $ catMaybes bbLst
  doParse instrMp bbMp
  where
    doParse instrMp bbMp = do
      isEnd <- hIsEOF h
      if isEnd
        then return []
        else (do
                 ln <- BS.hGetLine h
                 let continue (Done _ r) = return r
                     continue res@(Partial _) = do
                       line <- BS.hGetLine h
                       continue (feed (feed res line) (BS8.singleton '\n'))
                     continue (Fail str' ctx msg) = error $ "Error parsing extra predicate in "++show ctx++" "++show str'++": "++msg
                 lsp <- continue $ parse lisp (BS8.snoc ln '\n')
                 let pred = parseLLVMPred
                            (\name -> case Map.lookup name instrMp of
                                       Just i -> Left i
                                       Nothing -> case Map.lookup name bbMp of
                                         Just b -> Right b
                                         Nothing -> error $ "Unknown instruction or basic block in extra predicates: "++show name)
                            getInstr getBB lsp
                 preds <- doParse instrMp bbMp
                 return (pred:preds))

parseLLVMPred :: (T.Text -> Either (Ptr Instruction) (Ptr BasicBlock))
              -> (a -> Ptr Instruction -> SymInstr)
              -> (a -> Ptr BasicBlock -> SMTExpr Bool)
              -> Lisp
              -> a -> SMTExpr Bool
parseLLVMPred lookup getInstr getBB lsp arg
  = case lispToExpr commonFunctions (\name -> Just $ case lookup name of
                                      Left instr -> asSMTUntyped (getInstr arg instr)
                                      Right bb -> UntypedExpr $ getBB arg bb
                                    ) emptyDataTypeInfo
         (\expr -> case cast expr of
           Just e -> e)
         (Just (Fix BoolSort)) 0 lsp of
     Just r -> r
