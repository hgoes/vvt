{-# LANGUAGE OverloadedStrings,DeriveDataTypeable,RankNTypes,TypeFamilies,ViewPatterns,
             ScopedTypeVariables#-}
module Realization.Lisp where

import Realization

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Pipe
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.AttoLisp as L
import Data.Attoparsec
import qualified Data.Text as T
import qualified Data.ByteString as BS
import System.IO (Handle)
import Data.Typeable
import Data.Fix
import Prelude hiding (sequence,mapM)
import Data.Traversable
import Control.Monad.State (runStateT,get,put,lift)
import Data.List (genericLength)

data LispProgram
  = LispProgram { programAnnotation :: Annotation
                , programDataTypes :: DataTypeInfo
                , programState :: Map T.Text (Sort,Annotation)
                , programInput :: Map T.Text (Sort,Annotation)
                , programGates :: Map T.Text (Sort,SMTExpr Untyped)
                , programNext :: Map T.Text (SMTExpr UntypedValue)
                , programProperty :: [SMTExpr Bool]
                , programInitial :: [SMTExpr Bool]
                , programInvariant :: [SMTExpr Bool]
                , programAssumption :: [SMTExpr Bool]
                , programPredicates :: [SMTExpr Bool]
                }

type Annotation = Map T.Text L.Lisp

data LispVar = Input T.Text
             | State T.Text
             | Gate T.Text
             deriving (Eq,Ord,Show,Typeable)

data CArray a = CArray { cArrayEntries :: [a] } deriving (Eq,Ord,Show,Typeable)

readLispFile :: Handle -> IO L.Lisp
readLispFile h = do
  str <- BS.hGet h 1024
  let parseAll (Done _ r) = return r
      parseAll (Partial f) = do
        str <- BS.hGet h 1024
        parseAll (f str)
      parseAll (Fail _ _ err) = error $ "Couldn't parse lisp program: "++err
  parseAll $ parse L.lisp str

parseLispProgram :: L.Lisp -> LispProgram
parseLispProgram descr = case descr of
  L.List (L.Symbol "program":elems)
    -> let (ann,elems') = parseAnnotation elems Map.empty
           mp = Map.fromList [ (key,defs) | L.List (L.Symbol key:defs) <- elems ]
           dts = addDataTypeStructure tcCArray emptyDataTypeInfo
           state = case Map.lookup "state" mp of
                    Just sts -> parseVarMap sts
                    Nothing -> Map.empty
           inp = case Map.lookup "input" mp of
                  Just sts -> parseVarMap sts
                  Nothing -> Map.empty
           gates = case Map.lookup "gates" mp of
             Just gts -> let gts' = fmap (\gt -> case gt of
                                           L.List [L.Symbol name,sort,def]
                                             -> (name,case lispToSort sort of
                                                       Nothing -> error $ "Failed to parse sort "++show sort
                                                       Just srt -> (srt,parseLispExpr state inp gates dts srt def UntypedExpr))
                                           _ -> error $ "Failed to parse gate: "++show gt
                                         ) gts
                         in Map.fromList gts'
           next = case Map.lookup "next" mp of
             Just nxts -> let nxts' = fmap (\nxt -> case nxt of
                                             L.List [L.Symbol name,def]
                                               -> case Map.lookup name state of
                                                   Just (sort,_)
                                                     -> (name,parseLispExpr state inp gates dts sort def
                                                              (\(expr::SMTExpr a) -> case asValueType (undefined::a) undefined
                                                                                          (\(_::b) _ -> case cast expr of
                                                                                            Just expr' -> UntypedExprValue (expr'::SMTExpr b)) of
                                                                                      Just res -> res))
                                             _ -> error $ "Failed to parse next expression: "++show nxt
                                           ) nxts
                          in Map.fromList nxts'
           prop = case Map.lookup "property" mp of
             Nothing -> []
             Just xs -> fmap (\x -> parseLispExpr state inp gates dts (Fix BoolSort) x (\y -> case cast y of
                                                                                                       Just y' -> y')
                             ) xs
           init = case Map.lookup "initial" mp of
             Nothing -> []
             Just xs -> fmap (\x -> parseLispExpr state Map.empty Map.empty dts
                                    (Fix BoolSort) x (\y -> case cast y of
                                                             Just y' -> y')
                             ) xs
           invar = case Map.lookup "invariant" mp of
             Nothing -> []
             Just xs -> fmap (\x -> parseLispExpr state Map.empty Map.empty dts
                                    (Fix BoolSort) x (\y -> case cast y of
                                                             Just y' -> y')
                             ) xs
           assume = case Map.lookup "assumption" mp of
             Nothing -> []
             Just xs -> fmap (\x -> parseLispExpr state inp gates dts (Fix BoolSort) x (\y -> case cast y of
                                                                                                       Just y' -> y')
                             ) xs
           preds = case Map.lookup "predicate" mp of
             Nothing -> []
             Just xs -> fmap (\x -> parseLispExpr state Map.empty Map.empty dts (Fix BoolSort) x (\y -> case cast y of
                                                                                                         Just y' -> y')
                             ) xs
       in LispProgram { programAnnotation = ann
                      , programDataTypes = dts
                      , programState = state
                      , programInput = inp
                      , programGates = gates
                      , programNext = next
                      , programProperty = prop
                      , programInitial = init
                      , programInvariant = invar
                      , programAssumption = assume
                      , programPredicates = preds
                      }
  where
    parseVarMap lst = Map.fromList $
                      fmap (\st -> case st of
                                    L.List def -> case parseAnnotation def Map.empty of
                                      (ann,[L.Symbol name,sort])
                                        -> case lispToSort sort of
                                            Nothing -> error $ "Failed to parse sort "++show sort
                                            Just srt -> (name,(srt,ann))
                           ) lst
    parseAnnotation :: [L.Lisp] -> Annotation -> (Annotation,[L.Lisp])
    parseAnnotation [] cur = (cur,[])
    parseAnnotation (x:xs) cur = case x of
      L.Symbol (T.uncons -> Just (':',name)) -> case xs of
        y:ys -> parseAnnotation ys (Map.insert name y cur)
        [] -> error $ "Key "++show name++" is missing a value"
      _ -> let (res,unparsed) = parseAnnotation xs cur
           in (res,x:unparsed)


parseLispExpr :: Map T.Text (Sort,Annotation) -> Map T.Text (Sort,Annotation) -> Map T.Text (Sort,SMTExpr Untyped) -> DataTypeInfo -> Sort -> L.Lisp
              -> (forall a. SMTType a => SMTExpr a -> b) -> b
parseLispExpr state inps gates dts sort expr app
  = case lispToExpr commonFunctions
         (\txt -> case Map.lookup txt state of
                   Just (sort',_) -> withSort dts sort' $ \u ann -> Just (InternalObj (State txt) (ProxyArg u ann))
                   Nothing -> case Map.lookup txt inps of
                     Just (sort',_) -> withSort dts sort' $ \u ann -> Just (InternalObj (Input txt) (ProxyArg u ann))
                     Nothing -> case Map.lookup txt gates of
                       Just (sort',_) -> withSort dts sort' $ \u ann -> Just (InternalObj (Gate txt) (ProxyArg u ann))
                       Nothing -> Nothing)
         dts app
         (Just sort) 0 expr of
     Just expr' -> expr'
     Nothing -> error $ "Failed to parse expression "++show expr

relativize :: SMTType a => Map T.Text (SMTExpr UntypedValue)
           -> Map T.Text (SMTExpr UntypedValue)
           -> Map T.Text (SMTExpr UntypedValue)
           -> SMTExpr a
           -> SMTExpr a
relativize state inps gates e
  = snd $ foldExpr (\_ (e1::SMTExpr t)
                    -> ((),case asValueType (undefined::t) undefined
                                (\(_::p) _ -> case cast e1 of
                                  Just (e2::SMTExpr p) -> case cast $ relativize' state inps gates e2 of
                                    Just e3 -> e3) of
                            Just r -> r)
                   ) () e
  where
    relativize' state inps gates (InternalObj (cast -> Just obj) ann) = case obj of
      State v -> castUntypedExprValue $ state Map.! v
      Input v -> castUntypedExprValue $ inps Map.! v
      Gate v -> castUntypedExprValue $ gates Map.! v
    relativize' _ _ _ e = e

instance TransitionRelation LispProgram where
  type State LispProgram = Map T.Text (SMTExpr UntypedValue)
  type Input LispProgram = Map T.Text (SMTExpr UntypedValue)
  type RevState LispProgram = Map Integer T.Text
  type PredicateExtractor LispProgram = ()
  type RealizationProgress LispProgram = Map T.Text (SMTExpr Untyped)
  createStateVars pre prog
    = sequence $ Map.mapWithKey
      (\name (sort,_)
       -> case withSort (programDataTypes prog) sort $
               \u ann -> asValueType u ann $
                         \u' ann' -> varNamedAnn (pre++T.unpack name) (ProxyArgValue u' ann') of
           Just r -> r
      ) (programState prog)
  createInputVars pre prog
    = sequence $ Map.mapWithKey
      (\name (sort,_)
       -> case withSort (programDataTypes prog) sort $
               \u ann -> asValueType u ann $
                         \u' ann' -> varNamedAnn (pre++T.unpack name) (ProxyArgValue u' ann') of
           Just r -> r
      ) (programInput prog)
  initialState prog st = let expr = case programInitial prog of
                                     [e] -> e
                                     [] -> constant True
                                     xs -> app and' xs
                         in relativize st Map.empty Map.empty expr
  stateInvariant prog st = let expr = case programInvariant prog of
                                     [e] -> e
                                     [] -> constant True
                                     xs -> app and' xs
                           in relativize st Map.empty Map.empty expr
  startingProgress _ = Map.empty
  declareNextState prog st inp grp gates
    = runStateT (mapM (\expr -> do
                          cgates <- get
                          (expr',ngates) <- lift $ declareExpr prog st inp cgates expr
                          put ngates
                          return expr'
                      ) (programNext prog)
                ) gates
  declareAssertions prog st inp gates
    = runStateT (mapM (\expr -> do
                          cgates <- get
                          (expr',ngates) <- lift $ declareExpr prog st inp cgates expr
                          put ngates
                          return expr'
                      ) (programProperty prog)
                ) gates
  declareAssumptions prog st inp gates
    = runStateT (mapM (\expr -> do
                          cgates <- get
                          (expr',ngates) <- lift $ declareExpr prog st inp cgates expr
                          put ngates
                          return expr'
                      ) (programAssumption prog)
                ) gates
  renderPartialState prog st = return $ show st
  defaultPredicateExtractor _ = return ()
  extractPredicates _ _ _ _ = return ((),[])
  annotationState prog = fmap (\(s,_) -> withSort (programDataTypes prog) s $
                                         \u ann -> case asValueType u ann ProxyArgValue of
                                                    Just r -> r
                              ) (programState prog)
  annotationInput prog = fmap (\(s,_) -> withSort (programDataTypes prog) s $
                                         \u ann -> case asValueType u ann ProxyArgValue of
                                                    Just r -> r
                              ) (programInput prog)
  createRevState pre prog = do
    st <- createStateVars pre prog
    return (st,Map.fromList [ (i,name) | (name,Var i _) <- Map.toList st ])
  relativizeExpr prog rev expr st = snd $ foldExpr (\_ e -> case e of
                                                     Var i ann -> case Map.lookup i rev of
                                                       Just name -> ((),castUntypedExprValue $ st Map.! name)
                                                     _ -> ((),e)
                                                   ) () expr
  suggestedPredicates prog = [(False,\st -> relativize st Map.empty Map.empty expr)
                             | expr <- programPredicates prog ]

declareExpr :: (Monad m,SMTType a)
               => LispProgram
               -> Map T.Text (SMTExpr UntypedValue)
               -> Map T.Text (SMTExpr UntypedValue)
               -> Map T.Text (SMTExpr Untyped)
               -> SMTExpr a
               -> SMT' m (SMTExpr a,Map T.Text (SMTExpr Untyped))
declareExpr prog state inps gates expr = do
  (ngates,[res]) <- foldExprM (\cgates e -> do
                                  (res,ngates) <- declareExpr' cgates e
                                  return (ngates,[res])
                              ) gates expr
  return (res,ngates)
  where
    declareExpr' :: (Monad m,SMTType a) => Map T.Text (SMTExpr Untyped) -> SMTExpr a -> SMT' m (SMTExpr a,Map T.Text (SMTExpr Untyped))
    declareExpr' gates (InternalObj (cast -> Just obj) _) = case obj of
      State s -> return (castUntypedExprValue $ state Map.! s,gates)
      Input i -> return (castUntypedExprValue $ inps  Map.! i,gates)
      Gate  g -> case Map.lookup g (programGates prog) of
        Just (s,def) -> do
          (ndef,ngates) <- declareExpr prog state inps gates (castUntypedExpr def)
          ndef' <- defConstNamed (T.unpack g) ndef
          return (ndef',ngates)
    declareExpr' gates e = return (e,gates)
          
programToLisp :: LispProgram -> L.Lisp
programToLisp prog = L.List ([L.Symbol "program"]++
                             annLst++
                             defLst)
  where
    renderAnnotation mp = concat [ [L.Symbol $ T.cons ':' key,entr]
                                 | (key,entr) <- Map.toList mp ]
    derel obj = case cast obj of
                 Just (State n) -> L.Symbol n
                 Just (Input n) -> L.Symbol n
                 Just (Gate n) -> L.Symbol n
    annLst = renderAnnotation (programAnnotation prog)
    defLst = [L.List $ [L.Symbol "state"]++stateLst
             ,L.List $ [L.Symbol "input"]++inputLst
             ,L.List $ [L.Symbol "gates"]++gatesLst
             ,L.List $ [L.Symbol "next"]++nextLst
             ,L.List $ [L.Symbol "property"]++propLst
             ,L.List $ [L.Symbol "initial"]++initLst
             ,L.List $ [L.Symbol "invariant"]++invarLst
             ,L.List $ [L.Symbol "assumption"]++assumpLst
             ,L.List $ [L.Symbol "predicate"]++predLst]
    stateLst = [ L.List $ [L.Symbol name
                          ,sortToLisp sort]++renderAnnotation ann
               | (name,(sort,ann)) <- Map.toList (programState prog) ]
    inputLst = [ L.List $ [L.Symbol name
                          ,sortToLisp sort]++renderAnnotation ann
               | (name,(sort,ann)) <- Map.toList (programInput prog) ]
    gatesLst = [ L.List [L.Symbol name
                        ,sortToLisp sort
                        ,exprToLispWith derel
                         gate Map.empty (programDataTypes prog)]
               | (name,(sort,gate)) <- Map.toList (programGates prog) ]
    nextLst = [ L.List [L.Symbol name
                       ,exprToLispWith derel def Map.empty (programDataTypes prog)]
              | (name,def) <- Map.toList (programNext prog) ]
    propLst = [ exprToLispWith derel prop Map.empty (programDataTypes prog)
              | prop <- programProperty prog ]
    initLst = [ exprToLispWith derel prop Map.empty (programDataTypes prog)
              | prop <- programInitial prog ]
    invarLst = [ exprToLispWith derel prop Map.empty (programDataTypes prog)
               | prop <- programInvariant prog ]
    assumpLst = [ exprToLispWith derel prop Map.empty (programDataTypes prog)
                | prop <- programAssumption prog ]
    predLst = [ exprToLispWith derel prop Map.empty (programDataTypes prog)
              | prop <- programPredicates prog ]

addPredicate :: LispProgram -> SMTExpr Bool -> LispProgram
addPredicate prog pred
  = if elem pred (programPredicates prog)
    then prog
    else prog { programPredicates = pred:programPredicates prog }

instance SMTType a => SMTType (CArray a) where
  type SMTAnnotation (CArray a) = SMTAnnotation a
  getSort (_::CArray a) ann = Fix (NamedSort "CArray" [getSort (undefined::a) ann])
  asDataType (_::CArray a) ann = Just ("CArray",tcCArray)
  asValueType (arr::CArray a) ann f = asValueType (undefined::a) ann $
                                      \(_::b) ann' -> case cast arr of
                                      Just arr' -> f (arr'::CArray b) ann'
  getProxyArgs (_::CArray a) ann = [ProxyArg (undefined::a) ann]
  annotationFromSort (_::CArray a) (Fix (NamedSort "CArray" [s]))
    = annotationFromSort (undefined::a) s

tcCArray :: TypeCollection
tcCArray = TypeCollection 1 [dtCArray]

dtCArray :: DataType
dtCArray = DataType { dataTypeName = "CArray"
                    , dataTypeConstructors = [conCArray]
                    , dataTypeGetUndefined = \tps f -> case tps of
                                                        [ProxyArg (_::t) ann]
                                                          -> f (undefined::CArray t) ann
                    }

conCArray :: Constr
conCArray = Constr { conName = "CArray"
                   , conFields = [fieldSize,fieldEntries]
                   , construct = \tps vals f
                                 -> error "Cannot create instance of CArray"
                   , conTest = \_ _ -> True
                   }

fieldSize :: DataField
fieldSize = DataField { fieldName = "size"
                      , fieldSort = Fix $ NormalSort IntSort
                      , fieldGet = \tps arg f
                                   -> case tps of
                                       [ProxyArg (_::t) ann]
                                         -> case cast arg of
                                             Just (arr::CArray t)
                                               -> f (genericLength $ cArrayEntries arr
                                                     :: Integer) ()
                      }

fieldEntries :: DataField
fieldEntries = DataField { fieldName = "entries"
                         , fieldSort = Fix $ NormalSort (ArraySort
                                                         [Fix $ NormalSort IntSort]
                                                         (Fix $ ArgumentSort 0))
                         , fieldGet = \tps arr f -> case tps of
                         [ProxyArg (_::t) ann] -> f (error "Cannot extract entries field from CArray"::SMTArray (SMTExpr Integer) t) ((),ann)
                         }

constructorCArray :: SMTType a => SMTAnnotation a -> Constructor (SMTExpr Integer,SMTExpr (SMTArray (SMTExpr Integer) a)) (CArray a)
constructorCArray ann
  = withUndef $ \u -> Constructor [ProxyArg u ann] dtCArray conCArray
  where
    withUndef :: (t -> Constructor (SMTExpr Integer,SMTExpr (SMTArray (SMTExpr Integer) t)) (CArray t))
                 -> Constructor (SMTExpr Integer,SMTExpr (SMTArray (SMTExpr Integer) t)) (CArray t)
    withUndef f = f undefined

instance SMTValue a => SMTValue (CArray a) where
  unmangle = ComplexUnmangling $
             \f (expr::SMTExpr (CArray a)) ann -> do
               sz <- f (App (SMTFieldSel (Field [ProxyArg (undefined::a) ann]
                                          dtCArray conCArray fieldSize))
                        expr) ()
               entrs <- mapM (\idx -> f (App SMTSelect
                                         (App (SMTFieldSel (Field [ProxyArg (undefined::a) ann]
                                                            dtCArray conCArray fieldEntries))
                                          expr,Const (idx::Integer) ())) ann
                             ) [0..sz-1]
               return $ Just (CArray entrs)
  mangle = ComplexMangling $
           \(CArray entrs) ann
           -> let arr = foldl (\arr (idx,entr)
                               -> App SMTStore (arr,Const idx (),Const entr ann)
                              ) (App (SMTConstArray ()) (Const (head entrs) ann))
                        (zip [0..] entrs)
              in App (SMTConstructor $ constructorCArray ann) (Const (genericLength entrs) (),arr)
