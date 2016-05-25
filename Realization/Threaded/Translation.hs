{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,ViewPatterns #-}
module Realization.Threaded.Translation where

import Args
import Realization.Threaded
import Realization.Threaded.State
import Realization.Threaded.Value hiding (Struct(..))
import qualified Realization.Threaded.Value as Th
import qualified Realization.Lisp.Value as L
import qualified Realization.Lisp as L
import qualified Realization.Lisp.Array as L

import Language.SMTLib2
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Struct (Struct(..),Tree(..))
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import qualified Language.SMTLib2.Internals.Expression as E

import LLVM.FFI hiding (GetType,getType,And)

import qualified Data.AttoLisp as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Control.Monad.State (get,put,execState)
import Data.Traversable
import Prelude hiding (foldl,sequence,mapM,mapM_,concat)
import qualified Data.Text as T
import Foreign.Ptr (Ptr)
import Data.Functor.Identity
import Data.GADT.Compare

import Debug.Trace

newtype TransGate tp = TransGate (L.LispName '( '[],Leaf tp))

toLispProgram :: LLVMTransRel -> L.LispProgram
toLispProgram rel = trace ("Reverse state: "++show stateSt) $
                    L.LispProgram { L.programAnnotation = Map.empty
                                  , L.programState = DMap.insert errorName
                                                     (L.Annotation (Map.singleton "pc"
                                                                    (L.Symbol "true"))
                                                     ) state
                                  , L.programInput = inps
                                  , L.programGates = gts
                                  , L.programNext = DMap.insert errorName nextError next
                                  , L.programProperty = [L.LispExpr
                                                         (E.App E.Not ((L.LispRef
                                                                        (L.NamedVar errorName
                                                                         L.State) Nil
                                                                       ) ::: Nil))]
                                  , L.programInit = DMap.insert errorName
                                                    (L.LispInit $ L.LispValue (L.Size Nil Nil) $
                                                     Singleton $ L.Sized $ L.LispExpr
                                                     (E.Const $ BoolValue False))
                                                    init
                                  , L.programInvariant = inv
                                  , L.programAssumption = []
                                  , L.programPredicates = []
                                  }
  where
    init = reverseInit threadNames (llvmInit rel)
    (inps,inpSt) = reverseInput threadNames (llvmInputDesc rel)
    (state,stateSt) = reverseState threadNames (llvmStateDesc rel)
    gtTrans = DMap.fromList
              [ defE :=> (TransGate
                          (L.LispName Nil (Singleton tp) (T.pack $ "gate-"++defName def)))
              | defE@(DefExpr n tp) :=> def <- DMap.toList (llvmDefinitions rel) ]
    gts = DMap.fromList
          [ (L.LispName Nil (Singleton tp) (T.pack $ "gate-"++defName def))
            :=> (L.LispGate (L.LispConstr $ L.LispValue (L.Size Nil Nil)
                             (Singleton (L.Sized $ translateLLVMExpr inpSt stateSt gtTrans (defExpr def))))
                 (L.Annotation Map.empty))
          | defE@(DefExpr n tp) :=> def <- DMap.toList (llvmDefinitions rel) ]
    next = reverseNext threadNames inpSt stateSt gtTrans (llvmNext rel)
    nextError = L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                Singleton $ L.Sized $ runIdentity $ do
      notAsserts <- mapM (\e -> let ne = translateLLVMExpr inpSt stateSt gtTrans e
                                in not' ne
                         ) (llvmAssertions rel)
      case notAsserts of
        [] -> false
        [x] -> return x
        _ -> or' notAsserts
    threadNames = Map.fromList [ (th,"thread"++show n)
                               | (th,n) <- zip (Map.keys $ threadStateDesc $ llvmStateDesc rel)
                                           [1..] ]
    inv = [L.AtMostOne [ L.LispRef (L.NamedVar (mainBlkName blk) L.State) Nil
                       | blk <- Map.keys $ latchBlockDesc $
                                mainStateDesc $ llvmStateDesc rel ]]++
          [L.AtMostOne [ L.LispRef (L.NamedVar (threadBlkName tname blk) L.State) Nil
                       | blk <- Map.keys $ latchBlockDesc thd ]
          | (th,thd) <- Map.toList $ threadStateDesc $ llvmStateDesc rel
          , let Just tname = Map.lookup th threadNames ]++
          [L.ExactlyOne $ [ L.LispRef (L.NamedVar (stepName Nothing) L.Input) Nil ] ++
           [ L.LispRef (L.NamedVar (stepName (Just tname)) L.Input) Nil
           | th <- Map.keys $ threadStateDesc $ llvmStateDesc rel
           , let Just tname = Map.lookup th threadNames ]] ++
          [ L.LispExpr (E.App (E.Logic E.Implies (Succ (Succ Zero)))
                        (List.list2 yieldAct step))
          | (th,blk,sblk) <- llvmInternalYields rel
          , let yieldAct = case th of
                  Nothing -> L.LispRef (L.NamedVar (mainBlkName (blk,sblk)) L.State) Nil
                  Just th' -> let Just tname = Map.lookup th' threadNames
                              in L.LispRef (L.NamedVar (threadBlkName tname (blk,sblk)) L.State) Nil
                step = case th of
                  Nothing -> L.LispRef (L.NamedVar (stepName Nothing) L.Input) Nil
                  Just th' -> let Just tname = Map.lookup th' threadNames
                              in L.LispRef (L.NamedVar (stepName (Just tname)) L.Input) Nil
          ] ++
          (case llvmInternalYields rel of
              [] -> []
              [_] -> []
              _ -> [L.AtMostOne [ yieldAct
                                | (th,blk,sblk) <- llvmInternalYields rel
                                , let yieldAct = case th of
                                        Nothing -> L.LispRef (L.NamedVar (mainBlkName (blk,sblk)) L.State) Nil
                                        Just th' -> let Just tname = Map.lookup th' threadNames
                                                    in L.LispRef (L.NamedVar (threadBlkName tname (blk,sblk)) L.State) Nil
                                      step = case th of
                                        Nothing -> L.LispRef (L.NamedVar (stepName Nothing) L.Input) Nil
                                        Just th' -> let Just tname = Map.lookup th' threadNames
                                                    in L.LispRef (L.NamedVar (stepName (Just tname)) L.Input) Nil ]])
          

-- Naming conventions
errorName :: L.LispName '( '[],Leaf BoolType)
errorName = L.LispName Nil (Singleton bool) (T.pack "error")

mainBlkName :: (Ptr BasicBlock,Int) -> L.LispName '( '[],Leaf BoolType)
mainBlkName blk = L.LispName Nil (Singleton bool) (T.pack $ "main-"++showBlock blk "")

threadBlkName :: String -> (Ptr BasicBlock,Int) -> L.LispName '( '[],Leaf BoolType)
threadBlkName tname blk = L.LispName Nil (Singleton bool) (T.pack $ tname++"-"++showBlock blk "")

runningName :: String -> L.LispName '( '[],Leaf BoolType)
runningName tname = L.LispName Nil (Singleton bool) (T.pack $ "running-"++tname)

mainInstrName :: Ptr Instruction -> Struct Repr tps -> L.LispName '( '[],tps)
mainInstrName instr tp = L.LispName Nil tp (T.pack $ "main-"++showValue instr "")

threadInstrName :: String -> Ptr Instruction -> Struct Repr tps -> L.LispName '( '[],tps)
threadInstrName tname instr tp = L.LispName Nil tp (T.pack $ tname ++ "-" ++ showValue instr "")

argName :: String -> Struct Repr tps -> L.LispName '( '[],tps)
argName tname tp = L.LispName Nil tp (T.pack $ "arg-"++tname)

returnName :: String -> Struct Repr tps -> L.LispName '( '[],tps)
returnName tname tp = L.LispName Nil tp (T.pack $ "return-"++tname)

globalName :: List Repr sz -> Struct Repr tps -> MemoryLoc -> L.LispName '(sz,tps)
globalName sz tps loc = L.LispName sz tps (T.pack $ case loc of
                                            Left alloc -> "alloc-"++showValue alloc ""
                                            Right glob -> "global-"++showValue glob "")

localName :: Maybe String -> List Repr sz -> Struct Repr tps -> Ptr GlobalVariable -> L.LispName '(sz,tps)
localName tname sz tps g = L.LispName sz tps
                           (case tname of
                             Nothing -> T.pack $ "local-"++showValue g ""
                             Just name -> T.pack $ name++"-local-"++showValue g "")
                           
stepName :: Maybe String -> L.LispName '( '[],Leaf BoolType)
stepName th = L.LispName Nil (Singleton bool)
              (case th of
                Nothing -> "step"
                Just th' -> T.pack $ "step-"++th')

                           
reverseInit :: Map (Ptr CallInst) String
            -> ProgramState LLVMInit
            -> DMap L.LispName L.LispInit
reverseInit threadNames init
  = DMap.fromList $
    mainBlks++thBlks++
    mainVals++thVals++
    thActs++
    globals
  where
    mainBlks = [ (mainBlkName blk)
                 :=> (L.LispInit $ L.LispValue (L.Size Nil Nil) $
                      Singleton $ L.Sized $ translate def)
               | (blk,Init def) <- Map.toList $ latchBlocks $ mainState init ]
    thBlks = [ (threadBlkName tname blk)
               :=> (L.LispInit $ L.LispValue (L.Size Nil Nil) $
                    Singleton $ L.Sized $ translate def)
             | (th,(_,thd)) <- Map.toList $ threadState init
             , let Just tname = Map.lookup th threadNames
             , (blk,Init def) <- Map.toList $ latchBlocks thd ]
    mainVals = [ fromSymVal def $
                 \tp val -> (mainInstrName i tp)
                            :=> (L.LispInit $ L.LispValue (L.Size Nil Nil) $
                                 runIdentity $ Struct.mapM
                                 (\(Init val') -> return $ L.Sized $ translate val') val)
               | (i,def) <- Map.toList $ latchValues $ mainState init
               , allInit def == Just True ]
    thVals = [ fromSymVal def $
               \tp val -> (threadInstrName tname i tp)
                          :=> (L.LispInit $ L.LispValue (L.Size Nil Nil) $
                               runIdentity $ Struct.mapM
                               (\(Init val') -> return $ L.Sized $ translate val') val)
             | (th,(_,thS)) <- Map.toList $ threadState init
             , let Just tname = Map.lookup th threadNames
             , (i,def) <- Map.toList $ latchValues thS
             , allInit def == Just True ]
    thActs = [ (runningName tname) :=>
               (L.LispInit $ L.LispValue (L.Size Nil Nil) $
                Singleton $ L.Sized $ translate act)
             | (th,(Init act,_)) <- Map.toList $ threadState init
             , let Just tname = Map.lookup th threadNames]
    globals = [ fromAllocVal' def $
                \val' -> let (sz,tps) = L.lispValueType val'
                             rval = runIdentity $ foldExprs
                                    (\_ (Init v) -> return $ translate v) val'
                         in (globalName sz tps loc) :=>
                            (L.LispInit rval)
              | (loc,def) <- Map.toList $ memory init
              , allInit def == Just True ]
    translate = translateLLVMExpr
                (error "Init expression references input variables")
                (error "Init expression references state variables")
                (error "Init expression references gate variables")
    allInit :: Composite a => a LLVMInit -> Maybe Bool
    allInit arg = execState (foldExprs (\_ e -> do
                                           cur <- get
                                           case e of
                                             Init _ -> case cur of
                                               Just False -> error $ "Internal error: LLVM value is non-uniformly initialized."
                                               _ -> put (Just True)
                                             NoInit _ -> case cur of
                                               Just True -> error $ "Internal error: LLVM value is non-uniformly initialized."
                                               _ -> put (Just False)
                                           return e) arg) Nothing

reverseNext :: Map (Ptr CallInst) String
            -> ProgramInput L.LispExpr
            -> ProgramState L.LispExpr
            -> DMap DefExpr TransGate
            -> ProgramState (RExpr ProgramInput ProgramState)
            -> DMap L.LispName (L.LispVar L.LispExpr)
reverseNext threadNames inp st gts next
  = DMap.fromList $
    mainBlks++thBlks++
    mainVals++thVals++
    thActs++thArgs++thRets++
    globals++mainLocals++thLocals
  where
    mainBlks = [ (mainBlkName blk)
                 :=> (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                      Singleton $ L.Sized $ translateLLVMExpr inp st gts def)
               | (blk,def) <- Map.toList $ latchBlocks $ mainState next ]
    thBlks = [ (threadBlkName tname blk)
               :=> (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                    Singleton $ L.Sized $ translateLLVMExpr inp st gts def)
             | (th,(_,thd)) <- Map.toList $ threadState next
             , let Just tname = Map.lookup th threadNames
             , (blk,def) <- Map.toList $ latchBlocks thd ]
    mainVals = [ fromSymVal def $
                 \tp val -> (mainInstrName i tp)
                            :=> (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                                 runIdentity $ Struct.mapM
                                 (return . L.Sized . translateLLVMExpr inp st gts) val)
               | (i,def) <- Map.toList $ latchValues $ mainState next ]
    thVals = [ fromSymVal def $
               \tp val -> (threadInstrName tname i tp)
                          :=> (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                               runIdentity $ Struct.mapM
                               (return . L.Sized . translateLLVMExpr inp st gts) val)
             | (th,(_,thS)) <- Map.toList $ threadState next
             , let Just tname = Map.lookup th threadNames
             , (i,def) <- Map.toList $ latchValues thS ]
    thActs = [ (runningName tname) :=>
               (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                Singleton $ L.Sized $ translateLLVMExpr inp st gts act)
             | (th,(act,_)) <- Map.toList $ threadState next
             , let Just tname = Map.lookup th threadNames]
    thArgs = [ fromSymVal def $
               \tp val -> (argName tname tp)
                          :=> (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                               runIdentity $ Struct.mapM
                               (return . L.Sized . translateLLVMExpr inp st gts) val)
             | (th,(_,thS)) <- Map.toList $ threadState next
             , let Just tname = Map.lookup th threadNames
             , (arg,def) <- case threadArgument thS of
               Just x -> [x]
               Nothing -> [] ]
    thRets = [ fromSymVal def $
               \tp val -> (returnName tname tp)
                          :=> (L.LispConstr $ L.LispValue (L.Size Nil Nil) $
                               runIdentity $ Struct.mapM
                               (return . L.Sized . translateLLVMExpr inp st gts) val)
             | (th,(_,thS)) <- Map.toList $ threadState next
             , let Just tname = Map.lookup th threadNames
             , def <- case threadReturn thS of
               Just x -> [x]
               Nothing -> [] ]
    globals = [ fromAllocVal' val $
                \val' -> let (sz,tps) = L.lispValueType val'
                             rval = runIdentity $ foldExprs
                                    (\_ -> return . translateLLVMExpr inp st gts) val'
                         in (globalName sz tps loc) :=>
                            (L.LispConstr rval)
              | (loc,val) <- Map.toList $ memory next ]
    mainLocals = [ fromAllocVal' val $
                   \val' -> let (sz,tps) = L.lispValueType val'
                                rval = runIdentity $ foldExprs
                                       (\_ -> return . translateLLVMExpr inp st gts) val'
                            in (localName Nothing sz tps loc) :=>
                               (L.LispConstr rval)
                 | (loc,val) <- Map.toList $ threadGlobals $ mainState next ]
    thLocals = [ fromAllocVal' val $
                 \val' -> let (sz,tps) = L.lispValueType val'
                              rval = runIdentity $ foldExprs
                                     (\_ -> return . translateLLVMExpr inp st gts) val'
                          in (localName (Just tname) sz tps loc) :=>
                             (L.LispConstr rval)
               | (th,(_,thD)) <- Map.toList $ threadState next
               , let Just tname = Map.lookup th threadNames
               , (loc,val) <- Map.toList $ threadGlobals thD ]

reverseState :: Map (Ptr CallInst) String -> ProgramStateDesc
             -> (DMap L.LispName L.Annotation,ProgramState L.LispExpr)
reverseState threadNames desc = (DMap.fromList $
                                 mainBlks++thBlks ++
                                 mainVals++thVals ++
                                 thArgs++thRets ++
                                 mainLocals++thLocals++
                                 thRun++
                                 globals,st)
  where
    mainDesc = mainStateDesc desc
    mainBlks = [ (mainBlkName blk)
                 :=> (L.Annotation (Map.singleton "pc" (L.Symbol "true")))
               | (blk,_) <- Map.toList $ latchBlockDesc mainDesc ]
    thBlks = [ (threadBlkName tname blk)
               :=> (L.Annotation (Map.singleton "pc" (L.Symbol "true")))
             | (th,desc) <- Map.toList $ threadStateDesc desc
             , let Just tname = Map.lookup th threadNames
             , blk <- Map.keys $ latchBlockDesc desc ]
    mainVals = [ toLispType tp $
                 \tp' -> (mainInstrName instr tp')
                         :=> (L.Annotation Map.empty)
               | (instr,tp) <- Map.toList $ latchValueDesc mainDesc ]
    thVals = [ toLispType tp $
               \tp' -> (threadInstrName tname instr tp')
                       :=> (L.Annotation Map.empty)
             | (th,desc) <- Map.toList $ threadStateDesc desc
             , let Just tname = Map.lookup th threadNames
             , (instr,tp) <- Map.toList $ latchValueDesc desc ]
    thArgs = [ toLispType tp $
               \tp' -> (argName tname tp') :=> (L.Annotation Map.empty)
             | (th,desc) <- Map.toList $ threadStateDesc desc
             , let Just tname = Map.lookup th threadNames
             , tp <- case threadArgumentDesc desc of
               Nothing -> []
               Just (_,t) -> [t] ]
    thRets = [ toLispType tp $
               \tp' -> (L.LispName Nil tp' (T.pack $ "return-"++tname))
                       :=> (L.Annotation Map.empty)
             | (th,desc) <- Map.toList $ threadStateDesc desc
             , let Just tname = Map.lookup th threadNames
             , tp <- case threadReturnDesc desc of
               Nothing -> []
               Just t -> [t] ]
    mainLocals = [ toLispAllocType tp $
                   \sz tps -> (localName Nothing sz tps glob)
                              :=> (L.Annotation Map.empty)
                 | (glob,tp) <- Map.toList $ threadGlobalDesc mainDesc ]
    thRun = [ (runningName tname)
              :=> (L.Annotation Map.empty)
            | (th,desc) <- Map.toList $ threadStateDesc desc
            , let Just tname = Map.lookup th threadNames ]
    thLocals = [ toLispAllocType tp $
                 \sz tps -> (localName (Just tname) sz tps glob)
                            :=> (L.Annotation Map.empty)
               | (th,desc) <- Map.toList $ threadStateDesc desc
               , let Just tname = Map.lookup th threadNames
               , (glob,tp) <- Map.toList $ threadGlobalDesc desc ]
    globals = [ toLispAllocType tp $
                \sz tps -> (globalName sz tps loc)
                           :=> (L.Annotation Map.empty)
              | (loc,tp) <- Map.toList $ memoryDesc desc ]
    st = ProgramState
         { mainState = ThreadState
                       { latchBlocks = Map.mapWithKey
                                       (\blk _
                                        -> L.LispRef (L.NamedVar
                                                      (mainBlkName blk)
                                                      L.State) Nil
                                       ) (latchBlockDesc mainDesc)
                       , latchValues = Map.mapWithKey
                                       (\i tp
                                        -> reverseValue
                                              (\tps rev
                                               -> let name = mainInstrName i tps
                                                  in case rev of
                                                  L.RevVar idx
                                                    -> L.LispRef (L.NamedVar name L.State) idx
                                                  L.RevSize idx
                                                    -> L.LispSize (L.NamedVar name L.State) idx
                                              ) tp
                                       ) (latchValueDesc mainDesc)
                       , threadReturn = Nothing
                       , threadArgument = Nothing
                       , threadGlobals = Map.mapWithKey
                                         (\g tp
                                          -> reverseAlloc
                                             (\sz tps rev
                                              -> let name = localName Nothing sz tps g
                                                 in case rev of
                                                 L.RevVar idx
                                                   -> L.LispRef (L.NamedVar name L.State) idx
                                                 L.RevSize idx
                                                   -> L.LispSize (L.NamedVar name L.State) idx
                                             ) tp
                                         ) (threadGlobalDesc mainDesc)
                       }
         , threadState = Map.mapWithKey
                         (\th thd
                          -> let Just tname = Map.lookup th threadNames
                             in (L.LispRef (L.NamedVar (runningName tname) L.State) Nil,
                                 ThreadState
                                 { latchBlocks = Map.mapWithKey
                                                 (\blk _
                                                  -> L.LispRef (L.NamedVar
                                                                (threadBlkName tname blk)
                                                                L.State) Nil
                                                 ) (latchBlockDesc thd)
                                 , latchValues = Map.mapWithKey
                                                 (\i tp
                                                  -> reverseValue
                                                     (\tps rev
                                                      -> let name = threadInstrName tname i tps
                                                         in case rev of
                                                         L.RevVar idx
                                                           -> L.LispRef (L.NamedVar name L.State) idx
                                                         L.RevSize idx
                                                           -> L.LispSize (L.NamedVar name L.State) idx
                                                     ) tp
                                                 ) (latchValueDesc thd)
                                 , threadReturn = case threadReturnDesc thd of
                                   Nothing -> Nothing
                                   Just tp -> Just $ reverseValue
                                              (\tps rev -> let name = returnName tname tps
                                                           in case rev of
                                                           L.RevVar idx
                                                             -> L.LispRef (L.NamedVar name L.State) idx
                                                           L.RevSize idx
                                                             -> L.LispSize (L.NamedVar name L.State) idx
                                              ) tp
                                 , threadArgument = case threadArgumentDesc thd of
                                   Nothing -> Nothing
                                   Just (arg,tp)
                                     -> Just (arg,reverseValue
                                                  (\tps rev -> let name = argName tname tps
                                                               in case rev of
                                                               L.RevVar idx
                                                                 -> L.LispRef (L.NamedVar name L.State) idx
                                                               L.RevSize idx
                                                                 -> L.LispSize (L.NamedVar name L.State) idx
                                                  ) tp)
                                 , threadGlobals = Map.mapWithKey
                                                   (\g tp
                                                    -> reverseAlloc
                                                       (\sz tps rev
                                                        -> let name = localName (Just tname) sz tps g
                                                           in case rev of
                                                           L.RevVar idx
                                                             -> L.LispRef (L.NamedVar name L.State) idx
                                                           L.RevSize idx
                                                             -> L.LispSize (L.NamedVar name L.State) idx
                                                       ) tp
                                                   ) (threadGlobalDesc thd)
                                 })) (threadStateDesc desc)
         , memory = Map.mapWithKey
                    (\loc tp
                     -> reverseAlloc (\sz tps rev
                                      -> let name = globalName sz tps loc
                                         in case rev of
                                         L.RevVar idx -> L.LispRef (L.NamedVar name L.State) idx
                                         L.RevSize idx
                                           -> L.LispSize (L.NamedVar name L.State) idx
                                     ) tp
                    ) (memoryDesc desc)
         }

reverseInput :: Map (Ptr CallInst) String -> ProgramInputDesc
             -> (DMap L.LispName L.Annotation,ProgramInput L.LispExpr)
reverseInput threadNames desc = (DMap.unions [mp1,mp2,mp3],st)
  where
    mp1 = DMap.fromList $
          ((stepName Nothing) :=> (L.Annotation Map.empty)):
          [ (stepName (Just thName)) :=> (L.Annotation Map.empty)
          | (th,thName) <- Map.toList threadNames ]
    mp2 = DMap.fromList [ toLispType tp $
                          \tps -> (L.LispName Nil tps
                                   (T.pack $ "input-main-"++showValue i ""))
                                  :=> (L.Annotation Map.empty)
                        | (i,tp) <- Map.toList (nondetTypes $ mainInputDesc desc)]
    mp3 = DMap.fromList [ toLispType tp $
                          \tps -> (L.LispName Nil tps
                                   (T.pack $ "input-"++tname++"-"++showValue i ""))
                                  :=> (L.Annotation Map.empty)
                        | (th,thd) <- Map.toList $ threadInputDesc desc
                        , let Just tname = Map.lookup th threadNames
                        , (i,tp) <- Map.toList (nondetTypes thd) ]
    ctrue = L.LispExpr (E.Const $ BoolValue True)
    st = ProgramInput
         { mainInput = ThreadInput
                       { step = L.LispRef (L.NamedVar (stepName Nothing) L.Input) Nil
                       , nondets = Map.mapWithKey
                                   (\i tp
                                    -> reverseValue
                                       (\(tps::Struct Repr tps) rev
                                        -> let var :: L.LispVar L.LispExpr '( '[],tps)
                                               var = L.NamedVar (L.LispName Nil tps
                                                                 (T.pack $ "input-main-"++
                                                                  showValue i "")) L.Input
                                           in case rev of
                                           L.RevVar idx
                                             -> L.LispRef var idx
                                           L.RevSize idx
                                             -> L.LispSize var idx
                                       ) tp
                                   ) (nondetTypes $ mainInputDesc desc)
                       }
         , threadInput = Map.mapWithKey
                         (\th thd -> let Just tname = Map.lookup th threadNames
                                     in ThreadInput
                                        { step = L.LispRef (L.NamedVar
                                                            (stepName (Just tname)) L.Input)
                                                 Nil
                                        , nondets = Map.mapWithKey
                                                    (\i tp
                                                     -> reverseValue
                                                        (\(tps::Struct Repr tps) rev
                                                         -> let var :: L.LispVar L.LispExpr '( '[],tps)
                                                                var = L.NamedVar
                                                                      (L.LispName Nil tps
                                                                       (T.pack $ "input-"++tname++"-"++
                                                                        showValue i "")) L.Input
                                                            in case rev of
                                                            L.RevVar idx
                                                              -> L.LispRef var idx
                                                            L.RevSize idx
                                                              -> L.LispSize var idx
                                                        ) tp
                                                    ) (nondetTypes thd) }
                         ) (threadInputDesc desc)
         }

translateLLVMExpr :: ProgramInput L.LispExpr
                  -> ProgramState L.LispExpr
                  -> DMap DefExpr TransGate
                  -> LLVMExpr tp
                  -> L.LispExpr tp
translateLLVMExpr inp st gt
  = runIdentity . translateExpr
    (\irev -> return $ accessComposite irev inp)
    (\srev -> return $ accessComposite srev st)
    (\def -> case DMap.lookup def gt of
      Just (TransGate name) -> return $ L.LispRef (L.NamedVar name L.Gate) Nil)

translateExpr :: Monad m
              => (forall tp. RevComp inp tp -> m (L.LispExpr tp))
              -> (forall tp. RevComp st tp -> m (L.LispExpr tp))
              -> (forall tp. DefExpr tp -> m (L.LispExpr tp))
              -> RExpr inp st tp
              -> m (L.LispExpr tp)
translateExpr f g h (RExpr e) = do
  ne <- E.mapExpr undefined undefined undefined undefined undefined
        (translateExpr f g h) e
  return $ L.LispExpr ne
translateExpr f g h (RInput rev) = f rev
translateExpr f g h (RState rev) = g rev
translateExpr f g h (RRef def) = h def

reverseAlloc :: forall e. (GetType e)
             => (forall sz tps tp. List Repr sz -> Struct Repr tps
                 -> L.RevValue '(sz,tps) tp -> e tp)
             -> AllocType
             -> AllocVal e
reverseAlloc f tp
  = toLispAllocType tp $
    \(sz :: List Repr sz) (tp' :: Struct Repr tps)
    -> let revLisp :: L.LispValue '(sz,tps) e
           revLisp = runIdentity $ createComposite
                     (\_ rev -> return $ f sz tp' rev) (sz,tp')
       in case revLisp of
       L.LispValue sz' val' -> toAllocVal tp sz' val'

reverseValue :: forall e. (GetType e)
             => (forall tps tp. Struct Repr tps -> L.RevValue '( '[],tps) tp -> e tp)
             -> SymType
             -> SymVal e
reverseValue f tp
  = toLispType tp
    (\(tp' :: Struct Repr tps)
     -> let revLisp :: L.LispValue '( '[],tps) e
            revLisp = runIdentity $ createComposite
                      (\_ rev -> return $ f tp' rev) (Nil,tp')
        in case revLisp of
        L.LispValue _ val -> toSymVal tp $
                             runIdentity $ Struct.mapM
                             (\(L.Sized e) -> return e) val)

toAllocVal :: forall e sz tps. GetType e
           => AllocType -> L.Size e sz -> Struct (L.Sized e sz) tps
           -> AllocVal e
toAllocVal (TpStatic 1 tp) (L.Size Nil Nil) x = ValStatic [toStructVal tp nx]
  where
    nx = runIdentity (Struct.mapM (\(L.Sized e) -> return e) x)
toAllocVal (TpStatic len tp) (L.Size Nil Nil) (Struct xs)
  = ValStatic (toStatic' len xs)
  where
    toStatic' :: Int -> List (Struct (L.Sized e sz)) tps' -> [Th.Struct (SymVal e)]
    toStatic' 0 Nil = []
    toStatic' n (x ::: xs) = (toStructVal tp nx):(toStatic' (n-1) xs)
      where
        nx = runIdentity (Struct.mapM (\(L.Sized e) -> return e) x)
toAllocVal (TpDynamic tp) (L.Size (IntRepr ::: Nil) (e ::: Nil)) x
  = case getType e of
  IntRepr -> ValDynamic (toStructArray tp x) e

toStructArray :: forall tps e. GetType e => Th.Struct SymType -> Struct (L.Sized e '[IntType]) tps
              -> Th.Struct (SymArray e)
toStructArray (Th.Singleton tp) x = Th.Singleton (toSymArray tp x)
toStructArray (Th.Struct tps) (Struct xs) = Th.Struct (toStructArr' tps xs)
  where
    toStructArr' :: forall tps'. [Th.Struct SymType] -> List (Struct (L.Sized e '[IntType])) tps'
                 -> [Th.Struct (SymArray e)]
    toStructArr' [] Nil = []
    toStructArr' (x:xs) (tp ::: tps) = (toStructArray x tp):(toStructArr' xs tps)

toStructVal :: forall tps e. GetType e => Th.Struct SymType -> Struct e tps
            -> Th.Struct (SymVal e)
toStructVal (Th.Singleton tp) x = Th.Singleton (toSymVal tp x)
toStructVal (Th.Struct tps) (Struct xs) = Th.Struct (toStructVal' tps xs)
  where
    toStructVal' :: forall tps'. [Th.Struct SymType] -> List (Struct e) tps'
                 -> [Th.Struct (SymVal e)]
    toStructVal' [] Nil = []
    toStructVal' (x:xs) (tp ::: tps) = (toStructVal x tp):(toStructVal' xs tps)

fromSymVal :: GetType e => SymVal e -> (forall tps. Struct Repr tps -> Struct e tps -> a) -> a
fromSymVal val f = fromSymVal' val
                   (\e -> f (runIdentity $ Struct.mapM (return.getType) e) e)

fromSymVal' :: SymVal e -> (forall tps. Struct e tps -> a) -> a
fromSymVal' (ValBool e) f = f (Singleton e)
fromSymVal' (ValInt e) f = f (Singleton e)
fromSymVal' (ValBounded e) f = f (Singleton e)
fromSymVal' (ValPtr trgs tp) f
  = List.reifyList
    (\(cond,idx) g -> case idx of
      [] -> g (Singleton cond)
      _ -> reifyList
           (\el h -> h (Singleton el))
           idx
           (\idx' -> g (Struct ((Singleton cond) ::: idx')))
    ) (Map.elems trgs)
    (\xs -> f (Struct xs))
fromSymVal' (ValThreadId trgs) f
  = List.reifyList
    (\c g -> g (Singleton c)) (Map.elems trgs) $
    \xs -> f (Struct xs)
fromSymVal' (ValCondition trgs) f
  = List.reifyList
    (\c g -> g (Singleton c)) (Map.elems trgs) $
    \xs -> f (Struct xs)
fromSymVal' (ValVector vals) f
  = List.reifyList fromSymVal' vals $
    \xs -> f (Struct xs)

fromSymArray' :: SymArray e -> (forall tps. Struct (L.Sized e '[IntType]) tps -> a) -> a
fromSymArray' (ArrBool e) f = f (Singleton (L.Sized e))
fromSymArray' (ArrInt e) f = f (Singleton (L.Sized e))
fromSymArray' (ArrPtr trgs tp) f
  = List.reifyList
    (\(cond,idx) g -> case idx of
      [] -> g (Singleton (L.Sized cond))
      _ -> reifyList
           (\el h -> h (Singleton (L.Sized el)))
           idx
           (\idx' -> g (Struct idx'))
    ) (Map.elems trgs)
    (\xs -> f (Struct xs))
fromSymArray' (ArrThreadId trgs) f
  = List.reifyList
    (\c g -> g (Singleton (L.Sized c))) (Map.elems trgs) $
    \xs -> f (Struct xs)
fromSymArray' (ArrCondition trgs) f
  = List.reifyList
    (\c g -> g (Singleton (L.Sized c))) (Map.elems trgs) $
    \xs -> f (Struct xs)
fromSymArray' (ArrVector vals) f
  = List.reifyList fromSymArray' vals $
    \xs -> f (Struct xs)

fromSymStruct' :: Th.Struct (SymVal e) -> (forall tps. Struct e tps -> a) -> a
fromSymStruct' (Th.Singleton v) f = fromSymVal' v f
fromSymStruct' (Th.Struct xs) f
  = List.reifyList fromSymStruct' xs $ f . Struct

fromSymStructArray' :: Th.Struct (SymArray e)
                    -> (forall tps. Struct (L.Sized e '[IntType]) tps -> a) -> a
fromSymStructArray' (Th.Singleton x) f = fromSymArray' x f
fromSymStructArray' (Th.Struct xs) f
  = List.reifyList fromSymStructArray' xs $ f . Struct

fromAllocVal' :: AllocVal e
              -> (forall sz tps. L.LispValue '(sz,tps) e -> a) -> a
fromAllocVal' (ValStatic [x]) f
  = fromSymStruct' x $
    \val -> f $ L.LispValue (L.Size Nil Nil) (runIdentity $ Struct.mapM (return . L.Sized) val)
fromAllocVal' (ValStatic xs) f
  = List.reifyList
    (\x g -> fromSymStruct' x $
             \val -> g (runIdentity $ Struct.mapM (return . L.Sized) val)) xs $
    \vals -> f $ L.LispValue (L.Size Nil Nil) (Struct vals)
fromAllocVal' (ValDynamic arr sz) f
  = fromSymStructArray' arr $
    \arr' -> f $ L.LispValue (L.Size (List.list1 int) (List.list1 sz)) arr'

toSymVal :: forall e tps. GetType e => SymType -> Struct e tps -> SymVal e
toSymVal TpBool (Singleton e) = case getType e of
  BoolRepr -> ValBool e
toSymVal TpInt (Singleton e) = case getType e of
  IntRepr -> ValInt e
toSymVal (TpBounded bw1) (Singleton e) = case getType e of
  BitVecRepr bw2 -> case geq bw1 bw2 of
    Just Refl -> ValBounded e
toSymVal (TpPtr trgs tp) (Struct lst)
  = ValPtr (Map.fromList $ zip
            (Map.keys trgs)
            (runIdentity $ List.toList
             (\e -> case e of
               Singleton c -> case getType c of
                 BoolRepr -> return (c,[])
               Struct ((Singleton c) ::: idx) -> case getType c of
                 BoolRepr -> do
                   idx' <- List.toList (\i -> case i of
                                         Singleton i' -> case getType i' of
                                           IntRepr -> return i') idx
                   return (c,idx')) lst)
            ) tp
toSymVal (TpThreadId trgs) (Struct lst)
  = ValThreadId $ Map.fromList $ zip
    (Map.keys trgs)
    (runIdentity $ List.toList
     (\e -> case e of
       Singleton c -> case getType c of
         BoolRepr -> return c) lst)
toSymVal (TpCondition trgs) (Struct lst)
  = ValCondition $ Map.fromList $ zip
    (Map.keys trgs)
    (runIdentity $ List.toList
     (\e -> case e of
       Singleton c -> case getType c of
         BoolRepr -> return c) lst)
toSymVal (TpVector tps) (Struct lst)
  = ValVector $ toVector tps lst
  where
    toVector :: forall tps. [SymType] -> List (Struct e) tps -> [SymVal e]
    toVector [] Nil = []
    toVector (tp:tps) (e ::: es) = (toSymVal tp e):toVector tps es

toSymArray :: forall e tps. GetType e => SymType -> Struct (L.Sized e '[IntType]) tps
           -> SymArray e
toSymArray TpBool (Singleton (L.Sized e)) = case getType e of
  ArrayRepr (IntRepr ::: Nil) BoolRepr -> ArrBool e
toSymArray TpInt (Singleton (L.Sized e)) = case getType e of
  ArrayRepr (IntRepr ::: Nil) IntRepr -> ArrInt e
toSymArray (TpPtr trgs tp) (Struct lst)
  = ArrPtr (Map.fromList $ zip
            (Map.keys trgs)
            (runIdentity $ List.toList
             (\e -> case e of
               Singleton (L.Sized c) -> case getType c of
                 ArrayRepr (IntRepr ::: Nil) BoolRepr -> return (c,[])
               Struct ((Singleton (L.Sized c)) ::: idx) -> case getType c of
                 ArrayRepr (IntRepr ::: Nil) BoolRepr -> do
                   idx' <- List.toList (\i -> case i of
                                         Singleton (L.Sized i') -> case getType i' of
                                           ArrayRepr (IntRepr ::: Nil) IntRepr
                                             -> return i') idx
                   return (c,idx')) lst)
            ) tp
toSymArray (TpThreadId trgs) (Struct lst)
  = ArrThreadId $ Map.fromList $ zip
    (Map.keys trgs)
    (runIdentity $ List.toList
     (\e -> case e of
       Singleton (L.Sized c) -> case getType c of
         ArrayRepr (IntRepr ::: Nil) BoolRepr -> return c) lst)
toSymArray (TpCondition trgs) (Struct lst)
  = ArrCondition $ Map.fromList $ zip
    (Map.keys trgs)
    (runIdentity $ List.toList
     (\e -> case e of
       Singleton (L.Sized c) -> case getType c of
         ArrayRepr (IntRepr ::: Nil) BoolRepr -> return c) lst)
toSymArray (TpVector tps) (Struct lst)
  = ArrVector $ toVector tps lst
  where
    toVector :: forall tps. [SymType] -> List (Struct (L.Sized e '[IntType])) tps -> [SymArray e]
    toVector [] Nil = []
    toVector (tp:tps) (e ::: es) = (toSymArray tp e):toVector tps es

toLispType :: SymType -> (forall tps. Struct Repr tps -> a) -> a
toLispType TpBool f = f (Singleton bool)
toLispType TpInt f = f (Singleton int)
toLispType (TpBounded bw) f = f (Singleton $ bitvec bw)
toLispType (TpPtr trgs tp) f
  = List.reifyList (\ptr g -> case [ () | DynamicAccess <- offsetPattern ptr] of
                     [] -> g (Singleton bool)
                     xs -> List.reifyList (\_ g -> g (Singleton int)) xs $
                           \idx -> g (Struct ((Singleton bool) ::: idx))
                   ) (Map.keys trgs) $
    \lst -> f (Struct lst)
toLispType (TpThreadId trgs) f
  = List.reifyList (\_ g -> g (Singleton bool)) (Map.keys trgs) $
    \lst -> f (Struct lst)
toLispType (TpCondition trgs) f
  = List.reifyList (\_ g -> g (Singleton bool)) (Map.keys trgs) $
    \lst -> f (Struct lst)
toLispType (TpVector tps) f
  = List.reifyList (\tp g -> toLispType tp g) tps $
    \lst -> f (Struct lst)

toLispStructType :: Th.Struct SymType -> (forall tps. Struct Repr tps -> a) -> a
toLispStructType (Th.Singleton tp) f
  = toLispType tp f
toLispStructType (Th.Struct tps) f
  = List.reifyList toLispStructType tps $
    \lst -> f (Struct lst)

toLispAllocType :: AllocType -> (forall sz tps. List Repr sz -> Struct Repr tps -> a) -> a
toLispAllocType (TpStatic 1 tp) f
  = toLispStructType tp (f Nil)
toLispAllocType (TpStatic n tp) f = toLispStructType tp $
                                    \tp' -> reifyList (\_ g -> g tp') (replicate n ()) $
                                            \lst -> f Nil (Struct lst)
toLispAllocType (TpDynamic tp) f
  = toLispStructType tp $
    \tp' -> f (List.list1 int) tp'
