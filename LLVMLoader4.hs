{-# LANGUAGE ScopedTypeVariables,ViewPatterns,GADTs,PackageImports,RankNTypes,
             FlexibleInstances,MultiParamTypeClasses,MultiWayIf #-}
module LLVMLoader4 where

import Gates
import Affine
import ExprPreprocess
import Karr
import Realization

import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value)
import Language.SMTLib2.Pipe
import Language.SMTLib2.Internals.Optimize
import Language.SMTLib2.Internals.Instances (quantify,dequantify)
import Language.SMTLib2.Debug
import LLVM.FFI

import Prelude hiding (foldl,mapM_,mapM,concat)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntMap as IMap
import Foreign.Ptr
import Foreign.C.String
import Data.Foldable
import Data.Traversable
import System.Environment (getArgs)
import Foreign.Marshal.Array
import "mtl" Control.Monad.State (StateT,runStateT,get,put,lift)
import "mtl" Control.Monad.Trans (liftIO)
import Data.Typeable
import qualified Data.Vector as Vec
import Data.Maybe (catMaybes)
import Debug.Trace
import Data.Graph.Inductive.Graphviz
import System.IO

traceThis :: Show a => a -> a
traceThis = traceWith show

traceWith :: (a -> String) -> a -> a
traceWith f x = trace (f x) x

declareOutputActs :: (Monad m,Functor m) => RealizationSt -> RealizedGates -> LLVMInput
                     -> SMT' m (Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (SMTExpr Bool))
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

getOutput :: RealizationSt -> LLVMInput -> LLVMOutput
getOutput st inp
  = let acts = fmap (fmap (\act -> translateGateExpr (act inp) (gates st) inp)) (backwardEdges st)
        latchs = fmap (\(UntypedExpr xs)
                       -> UntypedExpr $ translateGateExpr xs (gates st) inp) $
                 Map.intersection (prevInstrs st) (latchInstrs st)
    in (acts,latchs)

declareOutputInstrs :: (Monad m,Functor m) => RealizationSt -> RealizedGates -> LLVMInput
                       -> SMT' m (Map (Ptr Instruction) UntypedExpr
                                 ,RealizedGates)
declareOutputInstrs st real inp
  = runStateT (Map.traverseWithKey
               (\instr (UntypedExpr val) -> do
                   real <- get
                   (expr,nreal) <- lift $ declareGate val real (gates st) inp
                   put nreal
                   return (UntypedExpr expr)) (Map.intersection (prevInstrs st) (latchInstrs st))
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

allLatchBlockAssigns :: RealizationSt
                        -> [(Ptr BasicBlock,Ptr BasicBlock,
                             Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (SMTExpr Bool)))]
allLatchBlockAssigns st
  = [ (src,trg,Map.mapWithKey
               (\trg'
                -> Map.mapWithKey
                   (\src' () -> constant $ trg==trg' && src==src')
               ) (latchBlks st))
    | (trg,srcs) <- Map.toList (latchBlks st)
    , (src,()) <- Map.toList srcs ]

getKarr :: RealizationSt -> Map (Ptr BasicBlock) (Map (Ptr BasicBlock) [ValueMap -> SMTExpr Bool])
getKarr st
  = {-trace (graphviz' (renderKarrTrans init_karr)) $-}
    fmap (fmap (\n -> let diag = {-traceWith (\diag' -> show n++": "++show diag') $-} (karrNodes final_karr) IMap.! n
                          pvecs = {-traceThis $-} extractPredicateVec diag
                      in [ \vals -> (constant c) .==. (case catMaybes [ case f of
                                                                           0 -> Nothing
                                                                           1 -> Just expr
                                                                           -1 -> Just $ app neg expr
                                                                           _ -> Just $ (constant f) * expr
                                                                      | (i,f) <- zip [0..] facs
                                                                      , let expr = castUntypedExpr $ vals Map.! (rev_mp Map.! i)
                                                                      ] of
                                                         [] -> constant 0
                                                         [x] -> x
                                                         xs -> app plus xs)
                         | pvec <- pvecs
                         , let c:facs = Vec.toList pvec ])) node_mp
  where
    final_karr = finishKarr init_karr
    init_karr = initKarr sz
                ((node_mp Map.! (initBlk st)) Map.! nullPtr)
                (\from to -> (trans_mp Map.! from) Map.! to)
                (\from -> case Map.lookup from trans_mp of
                    Nothing -> []
                    Just mp -> Map.keys mp)
    (sz_vals,int_vals,inp_vals,rev_mp)
      = Map.foldlWithKey
        (\(n,imp,amp,tmp) instr (ProxyArg (u::a) ann)
         -> case cast u of
           Just (_::Integer)
             -> (n+1,Map.insert instr n imp,
                 Map.insert instr (UntypedExpr (Var n ann::SMTExpr a)) amp,
                 Map.insert n instr tmp)
           Nothing -> (n,imp,
                       Map.insert instr (UntypedExpr (InternalObj () ann::SMTExpr a)) amp,
                       tmp)
        ) (0,Map.empty,Map.empty,Map.empty) (latchInstrs st)
    output = \acts (inps,latchs) -> getOutput st (acts,inps,latchs)
    transitions = [ (src,trg,trans5)
                  | (src,trg,acts) <- allLatchBlockAssigns st
                  , let (used,_,trans1) = quantify [(0::Integer)..] (inputInstrs st,latchInstrs st) (output acts)
                  , (_,trans2) <- removeArgGuards trans1
                  , let trans3 = dequantify used (inputInstrs st,latchInstrs st) trans2
                        trans4 = \inps -> trans3 (inps::ValueMap,inp_vals)
                  , trans5 <- removeInputs (inputInstrs st) (latchBlks st,latchInstrs st) trans4
                  ]
    (sz,node_mp) = Map.mapAccum
                   (Map.mapAccum (\n _ -> (n+1,n))) 0 (latchBlks st)
    trans_mp = foldl (\cmp (src,trg,(act_latch,var_latch))
                       -> let from_nd = (node_mp Map.! trg) Map.! src
                              tos = [ (to_src,to_trg)
                                    | (to_trg,to_trgs) <- Map.toList act_latch
                                    , (to_src,cond) <- Map.toList to_trgs
                                    , cond /= constant False ]
                              vals = mapM (\(instr,n) -> do
                                              res <- affineFromExpr $ castUntypedExpr $
                                                     var_latch Map.! instr
                                              return (n,res::AffineExpr Integer)
                                          ) (Map.toList int_vals)
                          in case vals of
                            Nothing -> cmp
                            Just vals'
                              -> let mat = Vec.fromList $
                                           [ Vec.generate (fromIntegral sz_vals)
                                             (\i' -> case Map.lookup (fromIntegral i') (affineFactors aff) of
                                                 Nothing -> 0
                                                 Just x -> x)
                                           | (i,aff) <- vals' ]
                                     vec = Vec.fromList
                                           [ affineConstant aff
                                           | (i,aff) <- vals' ]
                                     suc = foldl (\cmp (to_src,to_trg)
                                                   -> let rto = (node_mp Map.! to_trg) Map.! to_src
                                                      in Map.insertWith (++) rto [(mat,vec)] cmp
                                                 ) Map.empty tos
                                 in Map.insertWith (Map.unionWith (++)) from_nd suc cmp
                     ) Map.empty transitions

data LoaderBackend = LoaderBackend

instance Monad m => SMTBackend LoaderBackend (StateT [(String,TypeRep,String)] m) where
  smtHandle _ st (SMTDefineFun finfo [] (expr::SMTExpr a)) = do
    funs <- get
    case funInfoName finfo of
      Just (name,0) -> put (funs++[(name,typeOf (undefined::a),renderExpr' st expr)])
  smtHandle _ _ (SMTDeclareFun _) = return ()
  smtHandle _ _ (SMTComment _) = return ()
  smtHandle _ _ SMTExit = return ()

main = do
  [mod,entry] <- getArgs
  fun <- getProgram entry mod
  st <- realizeFunction fun
  latch_blk_names <- Map.traverseWithKey
                     (\trg
                      -> Map.traverseWithKey
                         (\src _
                          -> do
                            trg' <- liftIO $ getNameString trg
                            src' <- if src==nullPtr
                                    then return ""
                                    else liftIO $ getNameString src
                            return (src'++"."++trg'))) (latchBlks st)
  latch_var_names <- Map.traverseWithKey
                     (\instr prx -> do
                         name <- liftIO $ getNameString instr
                         return (name++"'",prx)
                     ) (latchInstrs st)
  input_names <- Map.traverseWithKey
                 (\instr prx -> do
                     name <- liftIO $ getNameString instr
                     return (name,prx)
                 ) (inputInstrs st)
  let act = withSMTBackend LoaderBackend
            (do
                comment "activation latches:"
                inp_gates <- mapM (mapM varNamed) latch_blk_names
                comment "inputs:"
                inp_inps <- mapM
                            (\(name,ProxyArg (_::a) ann) -> do
                                res <- varNamedAnn name ann
                                return (UntypedExpr (res::SMTExpr a))
                            ) input_names
                comment "variable latches:"
                inp_vals <- Map.traverseWithKey
                            (\instr (name,ProxyArg (_::a) ann) -> do
                                res <- varNamedAnn name ann
                                return (UntypedExpr (res::SMTExpr a))
                            ) latch_var_names
                comment "gates:"
                let inps = (inp_gates,inp_inps,inp_vals)
                (latch_blks,real0) <- declareOutputActs st Map.empty inps
                (latch_vals,real1) <- declareOutputInstrs st real0 inps
                (asserts,real2) <- declareAssertions st real1 inps
                (assumes,real3) <- declareAssumptions st real2 inps
                latch_blks' <- mapM (mapM renderExpr) latch_blks
                latch_vals' <- mapM (\(UntypedExpr e) -> renderExpr e) latch_vals
                asserts' <- mapM renderExpr asserts
                init <- renderExpr (((inp_gates Map.! (initBlk st)) Map.! nullPtr) .==. constant True)
                assumes0 <- mapM renderExpr assumes
                assumes1 <- Map.traverseWithKey
                            (\trg -> Map.traverseWithKey
                                     (\src expr
                                      -> renderExpr (expr .=>. app and' [ not' expr'
                                                                        | (trg',mp') <- Map.toList inp_gates
                                                                        , (src',expr') <- Map.toList mp'
                                                                        , trg/=trg' || src/=src' ])
                                     )
                            ) inp_gates
                fixp <- mapM renderExpr [ fix inp_vals
                                        | mp <- Map.elems (getKarr st)
                                        , lst <- Map.elems mp
                                        , fix <- lst ]
                return (latch_blks',latch_vals',asserts',init,assumes0++(concat $ fmap Map.elems (Map.elems assumes1))++fixp)
            )
  ((latch_blks,latch_vals,asserts,init,assumes),gates) <- runStateT act ([]::[(String,TypeRep,String)])
  withFile (mod++".nondet") WriteMode $ \h -> do
    mapM (\(name,ProxyArg u ann) -> do
             let tpname = case cast u of
                   Just (_::Integer) -> "int"
                   Nothing -> case cast u of
                     Just (_::Bool) -> "bool"
             hPutStrLn h (name++";"++tpname)
         ) input_names
  withFile (mod++".vars") WriteMode $ \h -> do
    mapM_ (mapM_ (\(name,nexpr) -> do
                     hPutStrLn h (name++";bool;"++nexpr)
                 )) (Map.intersectionWith
                     (Map.intersectionWith (\x y -> (x,y))) latch_blk_names latch_blks)
    mapM_ (\((name,ProxyArg u ann),nexpr) -> do
              let tpname = case cast u of
                    Just (_::Integer) -> "int"
                    Nothing -> case cast u of
                      Just (_::Bool) -> "bool"
              hPutStrLn h (name++";"++tpname++";"++nexpr)
          ) (Map.intersectionWith (\x y -> (x,y)) latch_var_names latch_vals)
  withFile (mod++".tr") WriteMode $
    \h -> mapM_ (\(name,tp,expr)
                 -> let tpname = if | tp==typeOf (undefined::Integer) -> "int"
                                    | tp==typeOf (undefined::Bool) -> "bool"
                    in hPutStrLn h (name ++ ";"++tpname++";"++expr)
                ) gates
  withFile (mod++".asrts") WriteMode $
    \h -> mapM_ (\ass -> hPutStrLn h ass) asserts
  withFile (mod++".init") WriteMode $
    \h -> hPutStrLn h init
  withFile (mod++".assum") WriteMode $
    \h -> mapM_ (\ass -> hPutStrLn h ass) assumes

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

applyOptimizations :: Ptr Module -> String -> IO ()
applyOptimizations mod entry = do
  pm <- newPassManager
  mapM (\(APass c) -> do
           pass <- c
           passManagerAdd pm pass) (passes entry)
  passManagerRun pm mod
  deletePassManager pm

getProgram :: String -> String -> IO (Ptr Function)
getProgram entry file = do
  Just buf <- getFileMemoryBufferSimple file
  diag <- newSMDiagnostic
  ctx <- newLLVMContext
  mod <- parseIR buf diag ctx
  applyOptimizations mod entry
  moduleDump mod
  moduleGetFunctionString mod entry
