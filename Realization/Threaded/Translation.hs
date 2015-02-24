{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,ViewPatterns,GADTs #-}
module Realization.Threaded.Translation where

import Realization.Threaded
import Realization.Threaded.State
import Realization.Threaded.Value
import qualified Realization.Lisp as L
import Gates

import qualified Data.AttoLisp as L
import Data.Map (Map)
import qualified Data.Map as Map
import Language.SMTLib2
import Language.SMTLib2.Internals
import Data.Fix
import qualified Data.Text as T
import Control.Monad.State (evalStateT,get,put)
import LLVM.FFI
import Data.Foldable
import Data.Traversable
import Foreign.Ptr (Ptr)
import Prelude hiding (mapM,mapM_,foldl,sequence)
import Data.Typeable

toLispProgram :: Realization (ProgramState,ProgramInput)
              -> IO L.LispProgram
toLispProgram real = do
  threadNames <- evalStateT (mapM (\_ -> do
                                      n <- get
                                      put (n+1)
                                      return $ "thread"++show n
                                  ) (threadStateDesc $ stateAnnotation real)) 1
  st1 <- foldlM (\mp blk -> do
                    name <- blockName blk
                    return $ Map.insert (T.append "main-" name) (Fix BoolSort,Map.singleton "pc" (L.Symbol "true")) mp
                ) Map.empty (Map.keys $ latchBlockDesc $ mainStateDesc $ stateAnnotation real)
  st2 <- foldlM (\mp (thread,thSt) -> do
                    let tName = threadNames Map.! thread
                    foldlM (\mp blk -> do
                               name <- blockName blk
                               return $ Map.insert (T.append (T.pack $ tName++"-") name)
                                 (Fix BoolSort,Map.singleton "pc" (L.Symbol "true")) mp
                           ) mp (Map.keys $ latchBlockDesc thSt)
                ) st1 (Map.toList $ threadStateDesc $ stateAnnotation real)
  st3 <- foldlM (\mp (instr,tp) -> do
                    name <- instrName instr
                    return $ fst $ foldl
                      (\(mp,n) tp -> (Map.insert (T.append "main-" $
                                                  if n==0
                                                  then name
                                                  else T.append name (T.pack $ "$"++show n))
                                      tp mp,n+1)
                      ) (mp,0) (toLispType tp)
                ) st2 (Map.toList $ latchValueDesc $ mainStateDesc $ stateAnnotation real)
  st4 <- foldlM (\mp (thread,thSt) -> do
                    let tName = threadNames Map.! thread
                    foldlM (\mp (instr,tp) -> do
                               name <- instrName instr
                               let name1 = T.append (T.pack $ tName++"-") name
                               return $ fst $ foldl
                                 (\(mp,n) tp -> (Map.insert (if n==0
                                                             then name1
                                                             else T.append name1 (T.pack $ "$"++show n))
                                                 tp mp,n+1)
                                 ) (mp,0) (toLispType tp)
                           ) mp (Map.toList $ latchValueDesc thSt)
                ) st3 (Map.toList $ threadStateDesc $ stateAnnotation real)
  let inp1 = foldl (\mp thName
                    -> Map.insert (T.pack $ "step-"++thName) (Fix BoolSort,Map.empty) mp
                   ) (Map.singleton "step-main" (Fix BoolSort,Map.empty)) threadNames
  st5 <- foldlM (\mp (loc,tp) -> do
                    name <- memLocName loc
                    return $ fst $ foldl
                      (\(mp,n) tp -> (Map.insert (if n==0
                                                  then name
                                                  else T.append name (T.pack $ "$"++show n))
                                      tp mp,n+1)
                      ) (mp,0) (toLispType tp)
                ) st4 (Map.toList $ memoryDesc $ stateAnnotation real)
  st6 <- foldlM (\mp thread -> do
                    let tName = threadNames Map.! thread
                    return $ Map.insert (T.pack $ "run-"++tName) (Fix BoolSort,Map.empty) mp
                ) st5 (Map.keys $ threadStateDesc $ stateAnnotation real)
  inp2 <- foldlM (\mp (instr,tp) -> do
                     name <- instrName instr
                     let name1 = T.append "main-" name
                     return $ fst $ foldl
                       (\(mp,n) tp -> (Map.insert (if n==0
                                                   then name1
                                                   else T.append name1 (T.pack $ "$"++show n))
                                       tp mp,n+1)
                       ) (mp,0) (toLispType tp)
                 ) inp1 (Map.toList $ nondetTypes $ mainInputDesc $ inputAnnotation real)
  inp3 <- foldlM (\mp (thread,thInp) -> do
                     let tName = threadNames Map.! thread
                     foldlM (\mp (instr,tp) -> do
                               name <- instrName instr
                               let name1 = T.append (T.pack $ tName++"-") name
                               return $ fst $ foldl
                                 (\(mp,n) tp -> (Map.insert (if n==0
                                                             then name1
                                                             else T.append name1 (T.pack $ "$"++show n))
                                                 tp mp,n+1)
                                 ) (mp,0) (toLispType tp)
                           ) mp (Map.toList $ nondetTypes thInp)
                 ) inp2 (Map.toList $ threadInputDesc $ inputAnnotation real)
  input <- makeProgramInput threadNames real
  let gateTrans = Map.foldlWithKey
                  (\gts tp (_,AnyGateArray arr)
                   -> Map.foldlWithKey
                      (\gts (GateExpr n) gate
                       -> translateGate n gate gts
                      ) gts arr
                  ) (GateTranslation Map.empty Map.empty Map.empty) (gateMp real)
      gates = Map.foldlWithKey
              (\gts tp (_,AnyGateArray arr)
               -> Map.foldlWithKey
                  (\gts (GateExpr n) (gate::Gate (ProgramState,ProgramInput) outp)
                   -> let expr = gateTransfer gate input
                          sort = getSort (undefined::outp) (gateAnnotation gate)
                      in Map.insert ((nameMapping gateTrans) Map.! (tp,n))
                         (sort,UntypedExpr $ toLispExpr gateTrans expr) gts
                  ) gts arr
              ) Map.empty (gateMp real)
  nxt1 <- foldlM (\mp blk -> do
                     name <- blockName blk
                     let name1 = T.append "main-" name
                     cond0 <- if snd blk==0
                              then return []
                              else case Map.lookup (Nothing,fst blk,snd blk) (yieldEdges real) of
                                              Just edge -> return [ toLispExpr gateTrans $
                                                                    edgeActivation cond input
                                                                  | cond <- edgeConditions edge ]
                     let cond1 = case Map.lookup (Nothing,fst blk,snd blk) (edges real) of
                           Nothing -> []
                           Just edge -> [ toLispExpr gateTrans $
                                          edgeActivation cond input
                                        | cond <- edgeConditions edge ]
                         step = InternalObj (L.LispVar "step-main" L.State L.NormalAccess) ()
                         old = InternalObj (L.LispVar name1 L.State L.NormalAccess) ()
                     return $ Map.insert name1 (UntypedExpr $ case cond0++cond1 of
                                                 [] -> (not' step) .&&. old
                                                 [x] -> ite step x old
                                                 xs -> ite step (app or' xs) old) mp
                 ) Map.empty (Map.keys $ latchBlockDesc $ mainStateDesc $ stateAnnotation real)
  nxt2 <- foldlM (\mp (thread,thSt) -> do
                     let tName = threadNames Map.! thread
                     foldlM (\mp blk -> do
                               name <- blockName blk
                               let name1 = T.append (T.pack $ tName++"-") name
                               cond0 <- if snd blk==0
                                        then return []
                                        else case Map.lookup (Just thread,fst blk,snd blk) (yieldEdges real) of
                                              Just edge -> return [ toLispExpr gateTrans $
                                                                    edgeActivation cond input
                                                                  | cond <- edgeConditions edge ]
                               let cond1 = case Map.lookup (Just thread,fst blk,snd blk) (edges real) of
                                     Nothing -> []
                                     Just edge -> [ toLispExpr gateTrans $
                                                    edgeActivation cond input
                                                  | cond <- edgeConditions edge ]
                                   step = InternalObj (L.LispVar (T.pack $ "step-"++tName)
                                                       L.State L.NormalAccess) ()
                                   old = InternalObj (L.LispVar name1 L.State L.NormalAccess) ()
                               return $ Map.insert name1
                                 (UntypedExpr $ case cond0++cond1 of
                                   [] -> (not' step) .&&. old
                                   [x] -> ite step x old
                                   xs -> ite step (app or' xs) old) mp
                           ) mp (Map.keys $ latchBlockDesc thSt)
                 ) nxt1 (Map.toList $ threadStateDesc $ stateAnnotation real)
  let outValues = outputValues real
  nxt3 <- foldlM (\mp ((th,instr),val) -> do
                     name <- instrName instr
                     let tName = case th of
                           Nothing -> "main-"
                           Just th' -> T.pack $ (threadNames Map.! th')++"-"
                         name1 = T.append tName name
                         expr = val input
                     return $ foldl (\mp (i,expr)
                                     -> Map.insert (if i==0
                                                    then name1
                                                    else T.append name1 (T.pack $ "$"++show i))
                                        expr mp
                                    ) mp (toLispExprs gateTrans expr)
                 ) nxt2 (Map.toList outValues)
  nxt4 <- foldlM (\mp (loc,val) -> do
                     name <- memLocName loc
                     return $ foldl (\mp (i,expr)
                                     -> Map.insert (if i==0
                                                    then name
                                                    else T.append name (T.pack $ "$"++show i))
                                        expr mp
                                    ) mp (toLispExprs gateTrans val)
                 ) nxt3 (Map.toList $ outputMem real input)
  nxt5 <- foldlM (\mp th -> do
                     let name = threadNames Map.! th
                         conds = case Map.lookup th (spawnEvents real) of
                           Nothing -> []
                           Just xs -> [ x input | x <- xs ]
                         old = InternalObj (L.LispVar (T.pack $ "run-"++name) L.State L.NormalAccess) ()
                         act = case conds of
                           [] -> old
                           [x] -> x .||. old
                           xs -> (app and' xs) .||. old
                         term = case Map.lookup th (termEvents real) of
                           Nothing -> act
                           Just [x] -> act .&&. (not' (x input))
                           Just xs -> act .&&. (not' $ app and' [ x input | x <- xs])
                     return $ Map.insert (T.pack $ "run-"++name) (UntypedExpr $ toLispExpr gateTrans term) mp
                 ) nxt4 (Map.keys $ threadStateDesc $ stateAnnotation real)
  init1 <- mapM (\(glob,val) -> do
                    name <- memLocName (Right glob)
                    case fmap (\(i,UntypedExpr expr)
                               -> (InternalObj (L.LispVar (if i==0
                                                           then name
                                                           else T.append name (T.pack $ "$"++show i)) L.State L.NormalAccess) (extractAnnotation expr))
                                  .==. expr
                              ) (toLispExprs gateTrans val) of
                         [e] -> return e
                         xs -> return $ app and' xs
                ) (Map.toList $ memoryInit real)
  init2 <- mapM (\th -> do
                    let name = threadNames Map.! th
                    return $ not' (InternalObj (L.LispVar (T.pack $ "run-"++name) L.State L.NormalAccess) ())
                ) (Map.keys $ threadStateDesc $ stateAnnotation real)
  init3 <- mapM (\blk -> do
                    name <- blockName blk
                    let var = InternalObj (L.LispVar (T.append "main-" name)
                                           L.State L.NormalAccess) ()
                    if blk==(mainBlock real,0)
                      then return var
                      else return (not' var)
                ) (Map.keys $ latchBlockDesc $ mainStateDesc $ stateAnnotation real)
  init4 <- mapM (\(th,blk) -> do
                    let tName = threadNames Map.! th
                    blks <- mapM (\blk' -> do
                                     name <- blockName blk'
                                     let var = InternalObj (L.LispVar
                                                            (T.append (T.pack $ tName++"-") name)
                                                            L.State L.NormalAccess) ()
                                     if blk'==(blk,0)
                                       then return var
                                       else return (not' var)
                                 ) (Map.keys $ latchBlockDesc $
                                    (threadStateDesc $ stateAnnotation real) Map.! th)
                    return $ app and' blks
                ) (Map.toList $ threadBlocks real)
  let asserts = fmap (\cond -> toLispExpr gateTrans (cond input)) (assertions real)
  inv1 <- do
    blks <- mapM (\blk -> do
                     name <- blockName blk
                     return $ InternalObj (L.LispVar (T.append "main-" name) L.State L.NormalAccess) ()
                 ) (Map.keys $ latchBlockDesc $ mainStateDesc $ stateAnnotation real)
    return $ app L.exactlyOne blks
  inv2 <- mapM (\(th,thSt) -> do
                   let tName = threadNames Map.! th
                   blks <- mapM (\blk -> do
                                    name <- blockName blk
                                    return $ InternalObj
                                      (L.LispVar (T.append (T.pack $ tName++"-") name)
                                       L.State L.NormalAccess) ()
                                ) (Map.keys $ latchBlockDesc thSt)
                   return $ app L.exactlyOne blks
               ) (Map.toList $ threadStateDesc $ stateAnnotation real)
  let inv3 = app L.exactlyOne $
             (InternalObj (L.LispVar "step-main" L.Input L.NormalAccess) ()):
             fmap (\th -> let tName = threadNames Map.! th
                          in InternalObj (L.LispVar (T.pack $ "step-"++tName) L.Input L.NormalAccess) ()
                  ) (Map.keys $ threadStateDesc $ stateAnnotation real)
      --constr = fmap (\cond -> toLispExpr gateTrans (cond input)) (constraints real)
  return L.LispProgram { L.programAnnotation = Map.empty
                       , L.programDataTypes = emptyDataTypeInfo
                       , L.programState = st6
                       , L.programInput = inp3
                       , L.programGates = gates
                       , L.programNext = nxt5
                       , L.programProperty = asserts
                       , L.programInitial = init1++init2++init3++init4
                       , L.programInvariant = [inv3] --inv1:inv3:inv2
                       , L.programAssumption = [] --constr
                       , L.programPredicates = []
                       }

toLispType :: SymType -> [(Sort,L.Annotation)]
toLispType TpBool = [(Fix BoolSort,Map.empty)]
toLispType TpInt = [(Fix IntSort,Map.empty)]
toLispType (TpPtr dest) = [ (Fix BoolSort,Map.empty)
                          | dest <- Map.keys dest ]
toLispType (TpThreadId ths) = [ (Fix BoolSort,Map.empty)
                              | th <- Map.keys ths ]

blockName :: (Ptr BasicBlock,Int) -> IO T.Text
blockName (blk,sblk) = do
  blkName <- getNameString blk
  if sblk==0
    then return $ T.pack blkName
    else return $ T.pack (blkName++"."++show sblk)

threadName :: Ptr CallInst -> IO T.Text
threadName call = do
  thFun <- getOperand call 2
  name <- getNameString thFun
  return $ T.pack name

instrName :: Ptr Instruction -> IO T.Text
instrName instr = do
  name <- getNameString instr
  return $ T.pack name

memLocName :: MemoryLoc -> IO T.Text
memLocName (Left alloc) = do
  name <- getNameString alloc
  return $ T.pack $ "alloc-"++name
memLocName (Right glob) = do
  name <- getNameString glob
  return $ T.pack name

data GateTranslation = GateTranslation { nameMapping :: Map (TypeRep,Int) T.Text
                                       , reverseNameMapping :: Map T.Text (TypeRep,Int)
                                       , nameUsage :: Map String Int }

translateGate :: Typeable outp => Int -> Gate inp outp -> GateTranslation -> GateTranslation
translateGate gtN (gt::Gate inp outp) trans
  = trans { nameMapping = Map.insert (tp,gtN) tName
                          (nameMapping trans)
          , reverseNameMapping = Map.insert tName (tp,gtN)
                                 (reverseNameMapping trans)
          , nameUsage = Map.insert name (usage+1)
                        (nameUsage trans)
          }
  where
    name = case gateName gt of
      Nothing -> "gt"
      Just n -> n
    rname = "gt-"++if usage==0
                   then name
                   else name++"$"++show usage
    tName = T.pack rname
    tp = typeOf (undefined::outp)
    usage = case Map.lookup name (nameUsage trans) of
      Nothing -> 0
      Just n -> n

toLispExpr :: GateTranslation -> SMTExpr a -> SMTExpr a
toLispExpr trans (InternalObj (cast -> Just (GateExpr n)) ann::SMTExpr a)
  = case Map.lookup (typeOf (undefined::a),n) (nameMapping trans) of
  Just r -> InternalObj (L.LispVar r L.Gate L.NormalAccess) ann
toLispExpr trans (App fun arg)
  = App fun (snd $ foldExprsId (\_ expr _ -> ((),toLispExpr trans expr)
                               ) () arg (extractArgAnnotation arg))
toLispExpr _ e = e

makeProgramInput :: Map (Ptr CallInst) String -> Realization (ProgramState,ProgramInput)
                 -> IO (ProgramState,ProgramInput)
makeProgramInput threadNames real = do
  mainBlocks <- sequence $ Map.mapWithKey
                (\blk _ -> do
                    name <- blockName blk
                    return $ InternalObj (L.LispVar (T.append "main-" name) L.State L.NormalAccess) ()
                ) (latchBlockDesc $ mainStateDesc $ stateAnnotation real)
  mainInstrs <- sequence $ Map.mapWithKey
                (\instr tp -> do
                    name <- instrName instr
                    return $ makeVar (T.append "main-" name) L.State tp
                ) (latchValueDesc $ mainStateDesc $ stateAnnotation real)
  threads <- sequence $ Map.mapWithKey
             (\th thd -> do
                 let thName = threadNames Map.! th
                     run = InternalObj (L.LispVar (T.pack $ "run-"++thName) L.State L.NormalAccess) ()
                 blocks <- sequence $ Map.mapWithKey
                           (\blk _ -> do
                               name <- blockName blk
                               let name' = T.append (T.pack $ thName++"-") name
                               return $ InternalObj (L.LispVar name' L.State L.NormalAccess) ()
                           ) (latchBlockDesc thd)
                 instrs <- sequence $ Map.mapWithKey
                           (\instr tp -> do
                               name <- instrName instr
                               let name' = T.append (T.pack $ thName++"-") name
                               return $ makeVar name' L.State tp
                           ) (latchValueDesc thd)
                 return (run,ThreadState { latchBlocks = blocks
                                         , latchValues = instrs })
             ) (threadStateDesc $ stateAnnotation real)
  mem <- sequence $ Map.mapWithKey
         (\loc tp -> do
             name <- memLocName loc
             return $ makeVar name L.State tp
         ) (memoryDesc $ stateAnnotation real)
  mainNondet <- sequence $ Map.mapWithKey
                (\instr tp -> do
                    name <- instrName instr
                    return $ makeVar (T.append "main-" name) L.Input tp
                ) (nondetTypes $ mainInputDesc $ inputAnnotation real)
  thInps <- sequence $ Map.mapWithKey
            (\th thd -> do
                let thName = threadNames Map.! th
                nondet <- sequence $ Map.mapWithKey
                          (\instr tp -> do
                              name <- instrName instr
                              return $ makeVar (T.append (T.pack $ thName++"-") name) L.Input tp
                          ) (nondetTypes thd)
                return ThreadInput { step = InternalObj (L.LispVar (T.pack $ "step-"++thName) L.Input L.NormalAccess) ()
                                   , nondets = nondet }
            ) (threadInputDesc $ inputAnnotation real)
  return (ProgramState { mainState = ThreadState { latchBlocks = mainBlocks
                                                 , latchValues = mainInstrs }
                       , threadState = threads
                       , memory = mem },
          ProgramInput { mainInput = ThreadInput { step = InternalObj (L.LispVar "step-main" L.Input L.NormalAccess) ()
                                                 , nondets = mainNondet }
                       , threadInput = thInps })


makeVar :: T.Text -> L.LispVarCat -> SymType -> SymVal
makeVar name cat TpBool = ValBool $ InternalObj (L.LispVar name cat L.NormalAccess) ()
makeVar name cat TpInt = ValInt $ InternalObj (L.LispVar name cat L.NormalAccess) ()
makeVar name cat (TpPtr locs)
  = ValPtr $ snd $ Map.mapAccum
    (\n _ -> (n+1,InternalObj (L.LispVar
                               (if n==0
                                then name
                                else T.append name (T.pack $ "$"++show n))
                               cat L.NormalAccess) ())
    ) 0 locs
makeVar name cat (TpThreadId ths)
  = ValThreadId $ snd $ Map.mapAccum
    (\n _ -> (n+1,InternalObj (L.LispVar
                               (if n==0
                                then name
                                else T.append name (T.pack $ "$"++show n))
                               cat L.NormalAccess) ())
    ) 0 ths

toLispExprs :: GateTranslation -> SymVal -> [(Int,SMTExpr Untyped)]
toLispExprs trans (ValBool x) = [(0,UntypedExpr $ toLispExpr trans x)]
toLispExprs trans (ValInt x) = [(0,UntypedExpr $ toLispExpr trans x)]
toLispExprs trans (ValPtr trgs)
  = [ (n,UntypedExpr $ toLispExpr trans trg)
    | (n,trg) <- zip [0..] (Map.elems trgs) ]
toLispExprs trans (ValThreadId ths)
  = [ (n,UntypedExpr $ toLispExpr trans th)
    | (n,th) <- zip [0..] (Map.elems ths) ]
