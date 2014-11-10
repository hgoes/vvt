{-# LANGUAGE ExistentialQuantification,RankNTypes,ViewPatterns,ScopedTypeVariables #-}
module Realization.Common where

import LLVM.FFI
import Language.SMTLib2
import Language.SMTLib2.Internals
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.C.String
import Data.Typeable
import Data.Map (Map)
import qualified Data.Map as Map

data RealizedValue inp = forall a. SMTValue a => NormalValue (SMTAnnotation a) (inp -> SMTExpr a)
                       | IntConst Integer
                       | OrList [inp -> SMTExpr Integer]
                       | ExtBool (inp -> SMTExpr Bool)

asSMTValue :: (SMTValue a,Typeable inp) => RealizedValue inp -> inp -> SMTExpr a
asSMTValue val = withSMTValue val (\_ f -> case cast f of
                                    Just f' -> f')

withSMTValue :: RealizedValue inp
             -> (forall a. SMTValue a => SMTAnnotation a -> (inp -> SMTExpr a) -> b)
             -> b
withSMTValue (NormalValue ann f) app = app ann f
withSMTValue (IntConst x) app = app () (const $ constant x)
withSMTValue (OrList _) _ = error "Or operator can only be applied to boolean values."
withSMTValue (ExtBool f) app = app () (\inp -> ite (f inp)
                                               (constant (1::Integer))
                                               (constant 0))

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

getProgram :: Bool -> String -> String -> IO (Ptr Function)
getProgram optimize entry file = do
  loadRes <- getFileMemoryBufferSimple file
  buf <- case loadRes of
    Left err -> error $ "Error while loading bitcode file: "++show err
    Right b -> return b
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  applyOptimizations optimize mod entry
  --moduleDump mod
  moduleGetFunctionString mod entry

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

cmpPredicates :: Ord i => Map i ProxyArgValue
                 -> [Map i (SMTExpr UntypedValue) -> SMTExpr Bool]
cmpPredicates instrs = mkCmps (Map.toList instrs)
  where
    intP = ProxyArgValue (undefined::Integer) ()
    
    mkCmps [] = []
    mkCmps [x] = []
    mkCmps ((i,x):xs)
      | x == intP = (mkCmps' i xs)++
                    (mkCmps xs)
      | otherwise = mkCmps xs

    mkCmps' i [] = []
    mkCmps' i ((j,y):xs)
      | y == intP = (\instrs
                     -> (castUntypedExprValue (instrs Map.! i) :: SMTExpr Integer)
                        .<.
                        (castUntypedExprValue (instrs Map.! j))
                    ):
                    (\instrs
                     -> (castUntypedExprValue (instrs Map.! i) :: SMTExpr Integer)
                        .>.
                        (castUntypedExprValue (instrs Map.! j))
                    ):
                    (\instrs
                     -> (castUntypedExprValue (instrs Map.! i) :: SMTExpr Integer)
                        .<=.
                        (castUntypedExprValue (instrs Map.! j))
                    ):
                    (mkCmps' i xs)
      | otherwise = mkCmps' i xs

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
