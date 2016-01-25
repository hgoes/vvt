{-# LANGUAGE ExistentialQuantification,RankNTypes,ViewPatterns,ScopedTypeVariables,
             PackageImports,DeriveDataTypeable,TypeFamilies #-}
module Realization.Common where

import LLVM.FFI hiding (Vector)
import Foreign.Ptr
import Foreign.C
import Foreign.Marshal.Array

getFunctionName :: Ptr CallInst -> IO String
getFunctionName ci = do
  val <- callInstGetCalledValue ci
  getFunctionName' val
  where
    getFunctionName' (castDown -> Just (f::Ptr Function))
      = getNameString f
    getFunctionName' (castDown -> Just (c::Ptr ConstantExpr)) = do
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
