{-# LANGUAGE OverloadedStrings,DeriveDataTypeable,RankNTypes,TypeFamilies,ViewPatterns,
             ScopedTypeVariables,GADTs#-}
module Realization.Lisp where

import Realization
import PartialArgs

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
import Data.List (genericLength,intercalate)
import Data.Monoid
import Data.Maybe (mapMaybe)

data LispProgram
  = LispProgram { programAnnotation :: Annotation
                , programDataTypes :: DataTypeInfo
                , programState :: Map T.Text (Sort,Annotation)
                , programInput :: Map T.Text (Sort,Annotation)
                , programGates :: Map T.Text (Sort,SMTExpr Untyped)
                , programNext :: Map T.Text (SMTExpr Untyped)
                , programProperty :: [SMTExpr Bool]
                , programInitial :: [SMTExpr Bool]
                , programInvariant :: [SMTExpr Bool]
                , programAssumption :: [SMTExpr Bool]
                , programPredicates :: [SMTExpr Bool]
                }

type Annotation = Map T.Text L.Lisp

data LispVar = LispVar T.Text LispVarCat LispVarAccess
             deriving (Eq,Ord,Show,Typeable)

data LispVarCat = Input | State | Gate deriving (Eq,Ord,Show,Typeable)

data LispVarAccess = NormalAccess | SizeAccess | EntriesAccess deriving (Eq,Ord,Show,Typeable)

data LispExpr a where
  NormalExpr :: SMTValue a => SMTExpr a -> LispExpr a
  ArrayExpr :: SMTValue a => SMTExpr Integer -> SMTExpr (SMTArray (SMTExpr Integer) a) -> LispExpr (CArray a)
  deriving Typeable

data LispType a where
  NormalType :: SMTValue a => SMTAnnotation a -> LispType a
  ArrayType :: SMTValue a => SMTAnnotation a -> LispType (CArray a)
  deriving Typeable

data LispValue a where
  NormalValue :: SMTValue t => t -> LispValue t
  ArrayValue :: SMTValue t => [t] -> LispValue (CArray t)

data LispPValue a where
  NormalPValue :: SMTValue t => Maybe t -> LispPValue t
  ArrayPValue :: SMTValue t => Bool -> [Maybe t] -> LispPValue (CArray t)
  deriving (Typeable)

data AnyLispExpr = forall a. SMTValue a => AnyLispExpr { anyLispExpr :: LispExpr a }
                   deriving (Typeable)

data AnyLispType = forall a. SMTValue a => AnyLispType (LispType a)
                   deriving (Typeable)

data AnyLispValue = forall a. SMTValue a => AnyLispValue (LispValue a)
                    deriving (Typeable)

data AnyLispPValue = forall a. SMTValue a => AnyLispPValue (LispPValue a)
                     deriving (Typeable)

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
             Nothing -> Map.empty
           next = case Map.lookup "next" mp of
             Just nxts -> let nxts' = fmap (\nxt -> case nxt of
                                             L.List [L.Symbol name,def]
                                               -> let (rname,acc) = case T.stripPrefix "size-" name of
                                                                     Just name -> (name,SizeAccess)
                                                                     Nothing -> case T.stripPrefix "entries-" name of
                                                                       Just name -> (name,EntriesAccess)
                                                                       Nothing -> (name,NormalAccess)
                                                  in case Map.lookup rname state of
                                                      Just (sort,_)
                                                        -> let rsort = case sort of
                                                                 Fix (NamedSort "CArray" [s]) -> case acc of
                                                                   SizeAccess -> Fix IntSort
                                                                   EntriesAccess -> Fix $ ArraySort [Fix IntSort] s
                                                                 _ -> sort
                                                           in (name,parseLispExpr state inp gates dts rsort def
                                                                    (\(expr::SMTExpr a) -> case cast expr of
                                                                                            Just expr' -> UntypedExpr (expr'::SMTExpr a))
                                                              )
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
             Just xs -> fmap (\x -> parseLispExpr state inp Map.empty dts
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

exactlyOne :: SMTFunction [SMTExpr Bool] Bool
exactlyOne = SMTBuiltIn "exactly-one" ()

exactlyOneParser :: FunctionParser
exactlyOneParser
  = FunctionParser $
    \lsp _ _ -> case lsp of
    L.Symbol "exactly-one" -> Just parse
    _ -> Nothing
  where
    parse = OverloadedParser { sortConstraint = all (== Fix BoolSort)
                             , deriveRetSort = \_ -> Just (Fix BoolSort)
                             , parseOverloaded = \_ _ app -> Just (app exactlyOne) }

parseLispExpr :: Map T.Text (Sort,Annotation) -> Map T.Text (Sort,Annotation)
              -> Map T.Text (Sort,SMTExpr Untyped) -> DataTypeInfo -> Sort -> L.Lisp
              -> (forall a. SMTType a => SMTExpr a -> b) -> b
parseLispExpr state inps gates dts sort expr app
  = case lispToExpr (commonFunctions `mappend` exactlyOneParser)
         (\txt -> let (name,acc) = case T.stripPrefix "size-" txt of
                        Nothing -> case T.stripPrefix "entries-" txt of
                          Nothing -> (txt,NormalAccess)
                          Just name' -> (name',EntriesAccess)
                        Just name' -> (name',SizeAccess)
                  in case Map.lookup name state of
                   Just (sort',_) -> withLispSort dts sort' acc $
                                     \u ann -> Just (InternalObj (LispVar name State acc)
                                                     (ProxyArg u ann))
                   Nothing -> case Map.lookup name inps of
                     Just (sort',_) -> withLispSort dts sort' acc $
                                       \u ann -> Just (InternalObj (LispVar name Input acc)
                                                       (ProxyArg u ann))
                     Nothing -> case Map.lookup txt gates of
                       Just (sort',_) -> withLispSort dts sort' acc $
                                         \u ann -> Just (InternalObj (LispVar name Gate acc)
                                                         (ProxyArg u ann))
                       Nothing -> Nothing)
         dts app
         (Just sort) 0 expr of
     Just expr' -> expr'
     Nothing -> error $ "Failed to parse expression "++show expr

relativize :: SMTType a => Map T.Text AnyLispExpr
           -> Map T.Text (SMTExpr UntypedValue)
           -> Map T.Text (SMTExpr UntypedValue)
           -> SMTExpr a
           -> SMTExpr a
relativize state inps gates (InternalObj (cast -> Just (LispVar name cat acc)) ann)
  = case cat of
     State -> case Map.lookup name state of
       Just (AnyLispExpr (NormalExpr e)) -> case cast e of
         Just e' -> e'
       Just (AnyLispExpr (ArrayExpr sz arr)) -> case acc of
         SizeAccess -> case cast sz of
           Just sz' -> sz'
         EntriesAccess -> case cast arr of
           Just arr' -> arr'
     Input -> castUntypedExprValue $ inps Map.! name
     Gate -> castUntypedExprValue $ gates Map.! name
relativize state inps gates (App (SMTBuiltIn "exactly-one" _) xs)
  = case cast xs of
     Just xs' -> case cast (app or' (oneOf [] $ fmap (relativize state inps gates) xs')) of
       Just r -> r
  where
    oneOf _ [] = []
    oneOf xs (y:ys) = (app and' (y:(fmap not' $ xs++ys))):
                      (oneOf (y:xs) ys)
relativize state inps gates (App fun args)
  = let (_,nargs) = foldExprsId (\_ e _ -> ((),relativize state inps gates e)) () args (extractArgAnnotation args)
    in App fun nargs
relativize state inps gates (UntypedExpr e) = UntypedExpr $ relativize state inps gates e
relativize state inps gates (UntypedExprValue e) = UntypedExprValue $ relativize state inps gates e
relativize state inps gates e = e

instance TransitionRelation LispProgram where
  type State LispProgram = Map T.Text AnyLispExpr
  type Input LispProgram = Map T.Text (SMTExpr UntypedValue)
  type RevState LispProgram = Map Integer (T.Text,LispVarAccess)
  type PredicateExtractor LispProgram = ()
  type RealizationProgress LispProgram = Map T.Text (SMTExpr Untyped)
  createStateVars pre prog
    = sequence $ Map.mapWithKey
      (\name (sort,_)
       -> case sort of
           Fix (NamedSort "CArray" [s])
             -> withSort (programDataTypes prog) s $
                \u ann -> case (asValueType u ann $
                                \(_::t) ann' -> do
                                  sz <- varNamedAnn (pre++"size-"++T.unpack name) ()
                                  arr <- varNamedAnn (pre++"entries-"++T.unpack name) ((),ann')
                                  return (AnyLispExpr (ArrayExpr sz arr
                                                       ::LispExpr (CArray t)))) of
                           Just r -> r
           _ -> withSort (programDataTypes prog) sort $
                \u ann -> case (asValueType u ann $
                                \(_::t) ann'
                                -> do
                                  v <- varNamedAnn (pre++T.unpack name) ann'
                                  return (AnyLispExpr (NormalExpr (v::SMTExpr t)))) of
                           Just r -> r
      ) (programState prog)
  createInputVars pre prog
    = sequence $ Map.mapWithKey
      (\name (sort,_)
       -> case withSort (programDataTypes prog) sort $
               \u ann -> asValueType u ann $
                         \(_::t) ann' -> (do
                                             v <- varNamedAnn (pre++T.unpack name) ann'
                                             return (UntypedExprValue (v::SMTExpr t))) of
           Just r -> r
      ) (programInput prog)
  initialState prog st = let expr = case programInitial prog of
                                     [e] -> e
                                     [] -> constant True
                                     xs -> app and' xs
                         in relativize st Map.empty Map.empty expr
  stateInvariant prog inp st = let expr = case programInvariant prog of
                                           [e] -> e
                                           [] -> constant True
                                           xs -> app and' xs
                               in relativize st inp Map.empty expr
  startingProgress _ = Map.empty
  declareNextState prog st inp grp gates
    = runStateT (sequence $ Map.mapWithKey
                 (\name (sort,_)
                   -> case sort of
                       Fix (NamedSort "CArray" [s])
                         -> withSort (programDataTypes prog) s $
                            \u ann -> case (asValueType u ann $
                                            \(_::t) ann' -> do
                                              gts0 <- get
                                              let szName = T.append (T.pack "size-") name
                                                  arrName = T.append (T.pack "entries-") name
                                                  szExpr = case Map.lookup szName (programNext prog) of
                                                    Just e -> castUntypedExpr e
                                                  arrExpr = case Map.lookup arrName (programNext prog) of
                                                    Just e -> castUntypedExpr e
                                              (szExpr',gts1) <- lift $ declareExpr prog st inp gts0 szExpr
                                              szExpr'' <- lift $ defConstNamed (T.unpack szName) szExpr'
                                              (arrExpr',gts2) <- lift $ declareExpr prog st inp gts1 arrExpr
                                              arrExpr'' <- lift $ defConstNamed (T.unpack arrName) arrExpr'
                                              put gts2
                                              return (AnyLispExpr (ArrayExpr szExpr'' arrExpr''
                                                                   ::LispExpr (CArray t)))) of
                                       Just r -> r
                       _ -> do
                         cgates <- get
                         (expr',ngates) <- lift $ entype
                                           (\(e::SMTExpr a) -> case asValueType (undefined::a) (extractAnnotation e)
                                                                    (\(_::b) ann' -> case cast e of
                                                                      Just e' -> do
                                                                        (e1,ngts) <- declareExpr prog st inp cgates (e'::SMTExpr b)
                                                                        e2 <- defConstNamed (T.unpack name) e1
                                                                        return (AnyLispExpr $ NormalExpr e2,ngts)) of
                                                                Just r -> r
                                           ) (case Map.lookup name (programNext prog) of
                                               Just e -> e)
                         put ngates
                         return expr'
                 ) (programState prog)
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
  renderPartialState prog st
    = return $ unlines $
      mapMaybe (\(name,AnyLispPValue val) -> case val of
                 NormalPValue Nothing -> Nothing
                 NormalPValue (Just v) -> Just $ (T.unpack name)++"="++show v
                 ArrayPValue False _ -> Nothing
                 ArrayPValue True lst -> Just $ (T.unpack name)++"=["++
                                         intercalate "," (fmap (\el -> case el of
                                                                 Nothing -> "_"
                                                                 Just v -> show v
                                                               ) lst)
               ) (Map.toList st)
  defaultPredicateExtractor _ = return ()
  extractPredicates _ _ _ _ = return ((),[])
  annotationState prog
    = fmap (\(s,_) -> case s of
             Fix (NamedSort "CArray" [s])
               -> withSort (programDataTypes prog) s $
                  \u ann -> case asValueType u ann
                                 (\(_::t) ann' -> AnyLispType (ArrayType ann'::LispType (CArray t))) of
                             Just r -> r
             _ -> withSort (programDataTypes prog) s $
                  \u ann -> case asValueType u ann
                                 (\(_::t) ann' -> AnyLispType (NormalType ann'::LispType t)) of
                             Just r -> r
           ) (programState prog)
  annotationInput prog = fmap (\(s,_) -> withSort (programDataTypes prog) s $
                                         \u ann -> case asValueType u ann ProxyArgValue of
                                                    Just r -> r
                              ) (programInput prog)
  createRevState pre prog = do
    st <- createStateVars pre prog
    return (st,Map.fromList $ concat $
               fmap (\(name,AnyLispExpr e) -> case e of
                      NormalExpr (Var i _) -> [(i,(name,NormalAccess))]
                      ArrayExpr (Var sz _) (Var arr _) -> [(sz,(name,SizeAccess))
                                                          ,(arr,(name,EntriesAccess))]
                    ) (Map.toList st))
  relativizeExpr prog rev expr st
    = snd $ foldExpr (\_ e -> case e of
                               Var i ann -> case Map.lookup i rev of
                                 Just (name,acc) -> case Map.lookup name st of
                                   Just (AnyLispExpr e) -> case e of
                                     NormalExpr e' -> ((),case cast e' of
                                                           Just e'' -> e'')
                                     ArrayExpr sz arr -> case acc of
                                       SizeAccess -> ((),case cast sz of
                                                          Just sz' -> sz')
                                       EntriesAccess -> ((),case cast arr of
                                                             Just arr' -> arr')
                               _ -> ((),e)
                     ) () expr
  suggestedPredicates prog = [(False,\st -> relativize st Map.empty Map.empty expr)
                             | expr <- programPredicates prog ]

declareExpr :: (Monad m,SMTType a)
               => LispProgram
               -> Map T.Text AnyLispExpr
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
    declareExpr' gates (InternalObj (cast -> Just (LispVar name cat acc)) _) = case cat of
      State -> case Map.lookup name state of
        Just (AnyLispExpr (NormalExpr e))
          -> return (case cast e of
                      Just e' -> e',gates)
        Just (AnyLispExpr (ArrayExpr sz arr)) -> case acc of
          SizeAccess -> case cast sz of
            Just e -> return (e,gates)
          EntriesAccess -> case cast arr of
            Just e -> return (e,gates)
      Input -> return (castUntypedExprValue $ inps  Map.! name,gates)
      Gate -> case Map.lookup name gates of
        Just expr -> return (castUntypedExpr expr,gates)
        Nothing -> case Map.lookup name (programGates prog) of
          Just (s,def) -> do
            (ndef,ngates) <- declareExpr prog state inps gates (castUntypedExpr def)
            ndef' <- defConstNamed (T.unpack name) ndef
            return (ndef',Map.insert name (UntypedExpr ndef') ngates)
    declareExpr' gates e = return (e,gates)
          
programToLisp :: LispProgram -> L.Lisp
programToLisp prog = L.List ([L.Symbol "program"]++
                             annLst++
                             defLst)
  where
    renderAnnotation mp = concat [ [L.Symbol $ T.cons ':' key,entr]
                                 | (key,entr) <- Map.toList mp ]
    derel obj = case cast obj of
      Just (LispVar name _ acc) -> case acc of
        NormalAccess -> L.Symbol name
        SizeAccess -> L.Symbol (T.append (T.pack "size-") name)
        EntriesAccess -> L.Symbol (T.append (T.pack "entries-") name)
      Nothing -> error $ "Cannot derelegate object "++show obj
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
                         gate (error "Internal error") (programDataTypes prog)]
               | (name,(sort,gate)) <- Map.toList (programGates prog) ]
    nextLst = [ L.List [L.Symbol name
                       ,exprToLispWith derel def (error "Internal error") (programDataTypes prog)]
              | (name,def) <- Map.toList (programNext prog) ]
    propLst = [ exprToLispWith derel prop (error "Internal error") (programDataTypes prog)
              | prop <- programProperty prog ]
    initLst = [ exprToLispWith derel prop (error "Internal error") (programDataTypes prog)
              | prop <- programInitial prog ]
    invarLst = [ exprToLispWith derel prop (error "Internal error") (programDataTypes prog)
               | prop <- programInvariant prog ]
    assumpLst = [ exprToLispWith derel prop (error "Internal error") (programDataTypes prog)
                | prop <- programAssumption prog ]
    predLst = [ exprToLispWith derel prop (error "Internal error") (programDataTypes prog)
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
  defaultExpr ann = App (SMTConstructor (constructorCArray ann)) (defaultExpr (),App (SMTConstArray ()) (defaultExpr ann))

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
                   , conUndefinedArgs = \tps f -> case tps of
                                                   [tp] -> withProxyArg tp $
                                                           \(_::t) ann -> f (undefined::(SMTExpr Integer,SMTExpr (SMTArray (SMTExpr Integer) t))) ((),((),ann))
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

carraySize :: SMTType t => SMTAnnotation t -> Field (CArray t) Integer
carraySize ann = withUndef $ \u -> Field [ProxyArg u ann] dtCArray conCArray fieldSize
  where
    withUndef :: (t -> Field (CArray t) Integer) -> Field (CArray t) Integer
    withUndef f = f undefined

carrayEntries :: SMTType t => SMTAnnotation t -> Field (CArray t) (SMTArray (SMTExpr Integer) t)
carrayEntries ann = withUndef $ \u -> Field [ProxyArg u ann] dtCArray conCArray fieldEntries
  where
    withUndef :: (t -> Field (CArray t) (SMTArray (SMTExpr Integer) t))
                 -> Field (CArray t) (SMTArray (SMTExpr Integer) t)
    withUndef f = f undefined

withLispSort :: DataTypeInfo -> Sort -> LispVarAccess
             -> (forall t. SMTType t => t -> SMTAnnotation t -> r)
             -> r
withLispSort dts (Fix (NamedSort "CArray" [s])) NormalAccess f
  = withSort dts s $
    \(u::t) ann -> f (undefined::CArray t) ann
withLispSort dts (Fix (NamedSort "CArray" [s])) SizeAccess f
  = f (undefined::Integer) ()
withLispSort dts (Fix (NamedSort "CArray" [s])) EntriesAccess f
  = withSort dts s $
    \(u::t) ann -> f  (undefined::SMTArray (SMTExpr Integer) t) ((),ann)
withLispSort dts s NormalAccess f
  = withSort dts s f 

instance SMTValue a => SMTValue (CArray a) where
  unmangle = ComplexUnmangling $
             \f s (expr::SMTExpr (CArray a)) ann -> do
               let unmEntries f expr ann s [] = return ([],s)
                   unmEntries f expr ann s (i:is) = do
                     (i',s1) <- f s (App SMTSelect
                                     (App (SMTFieldSel (Field [ProxyArg (undefined::a) ann]
                                                        dtCArray conCArray fieldEntries))
                                      expr,Const (i::Integer) ())) ann
                     (is',s2) <- unmEntries f expr ann s1 is
                     return (i':is',s2)
               (sz,s1) <- f s (App (SMTFieldSel (Field [ProxyArg (undefined::a) ann]
                                                 dtCArray conCArray fieldSize))
                               expr) ()
               (entrs,s2) <- unmEntries f expr ann s1 [0..sz-1]
               return (Just (CArray entrs),s2)
  mangle = ComplexMangling $
           \(CArray entrs) ann
           -> let arr = foldl (\arr (idx,entr)
                               -> App SMTStore (arr,Const idx (),Const entr ann)
                              ) (App (SMTConstArray ()) (defaultExpr ann))
                        (zip [0..] entrs)
              in App (SMTConstructor $ constructorCArray ann) (Const (genericLength entrs) (),arr)

instance SMTType t => Show (LispType t) where
  showsPrec p (_::LispType t) = showsPrec p (typeOf (undefined::t))

instance SMTType t => Eq (LispType t) where
  (NormalType ann1) == (NormalType ann2) = ann1==ann2
  (ArrayType ann1) == (ArrayType ann2) = ann1==ann2
  _ == _ = False

instance SMTType t => Ord (LispType t) where
  compare (NormalType ann1) (NormalType ann2) = compare ann1 ann2
  compare (NormalType _) _ = LT
  compare (ArrayType ann1) (ArrayType ann2) = compare ann1 ann2

instance Show (LispExpr t) where
  showsPrec p (NormalExpr e) = showsPrec p e
  showsPrec p (ArrayExpr idx e) = showsPrec p (idx,e)

instance Eq (LispExpr t) where
  (NormalExpr e1) == (NormalExpr e2) = e1==e2
  (ArrayExpr i1 e1) == (ArrayExpr i2 e2) = i1==i2 && e1==e2
  _ == _ = False

instance Ord (LispExpr t) where
  compare (NormalExpr e1) (NormalExpr e2) = compareExprs e1 e2
  compare (NormalExpr _) _ = LT
  compare (ArrayExpr i1 e1) (ArrayExpr i2 e2) = case compareExprs i1 i2 of
    EQ -> compareExprs e1 e2
    r -> r

instance SMTType a => Args (LispExpr a) where
  type ArgAnnotation (LispExpr a) = LispType a
  foldExprs f s (NormalExpr e) (NormalType ann) = do
    (ns,e') <- f s e ann
    return (ns,NormalExpr e')
  foldExprs f s (ArrayExpr idx arr) (ArrayType ann) = do
    (s1,idx') <- f s idx ()
    (s2,arr') <- f s1 arr ((),ann)
    return (s2,ArrayExpr idx' arr')
  foldsExprs f s lst (NormalType ann) = do
    (ns,exprs,expr) <- foldsExprs f s (fmap (\(NormalExpr x,b) -> (x,b)
                                            ) lst) ann
    return (ns,fmap NormalExpr exprs,NormalExpr expr)
  foldsExprs f s lst (ArrayType ann) = do
    (ns,exprs,(sz,arr)) <- foldsExprs f s (fmap (\(ArrayExpr sz arr,b) -> ((sz,arr),b)
                                                ) lst) ((),((),ann))
    return (ns,fmap (\(sz,arr) -> ArrayExpr sz arr) exprs,ArrayExpr sz arr)
  extractArgAnnotation (NormalExpr e)
    = NormalType (extractAnnotation e)
  extractArgAnnotation (ArrayExpr _ e)
    = ArrayType (snd $ extractAnnotation e)
  toArgs (NormalType _) (x:xs) = Just (NormalExpr (castUntypedExpr x),xs)
  toArgs (ArrayType _) (x:y:xs)
    = Just (ArrayExpr (castUntypedExpr x) (castUntypedExpr y),xs)
  toArgs _ _ = Nothing
  fromArgs (NormalExpr e) = [UntypedExpr e]
  fromArgs (ArrayExpr idx arr) = [UntypedExpr idx,UntypedExpr arr]
  getTypes _ (NormalType ann::LispType t) = [ProxyArg (undefined::t) ann]
  getTypes _ tp@(ArrayType ann)
    = [ProxyArg (undefined::Integer) ()
      ,ProxyArg (getUndef tp) ((),ann)]
    where
      getUndef :: LispType (CArray t) -> SMTArray (SMTExpr Integer) t
      getUndef _ = undefined
  getArgAnnotation _ _ = error "Cannot get arg annotation for lisp expression."

instance SMTValue a => LiftArgs (LispExpr a) where
  type Unpacked (LispExpr a) = LispValue a
  liftArgs (NormalValue v) (NormalType ann)
    = NormalExpr $ liftArgs v ann
  liftArgs (ArrayValue lst) (ArrayType ann)
    = ArrayExpr (liftArgs (genericLength lst) ())
      (foldl (\carr (i,el)
              -> App SMTStore (carr,Const i (),liftArgs el ann)
             ) (App (SMTConstArray ()) (defaultExpr ann))
       (zip [0..] lst))
  unliftArgs (NormalExpr v) unl = do
    rv <- unliftArgs v unl
    return (NormalValue rv)
  unliftArgs (ArrayExpr sz arr) unl = do
    rsz <- unliftArgs sz unl
    lst <- mapM (\i -> unliftArgs (App SMTSelect (arr,Const i ())) unl
                ) [0..rsz-1]
    return (ArrayValue lst)

instance SMTValue a => PartialArgs (LispExpr a) where
  type PartialValue (LispExpr a) = LispPValue a
  maskValue _ (NormalPValue v) (x:xs)
    = (NormalPValue $ if x then v else Nothing,xs)
  maskValue _ (ArrayPValue b lst) (x:xs)
    = (ArrayPValue (if x then b else False) lst',xs')
    where
      (lst',xs') = mask' lst xs
      mask' [] xs = ([],xs)
      mask' (x:xs) (y:ys) = let (xs',ys') = mask' xs ys
                                x' = if y
                                     then x
                                     else Nothing
                            in (x':xs',ys')
  unmaskValue _ (NormalValue v) = NormalPValue (Just v)
  unmaskValue _ (ArrayValue vs) = ArrayPValue True (fmap Just vs)
  assignPartial (NormalExpr e) (NormalPValue val)
    = [case val of
        Just d -> Just $ e .==. (Const d (extractAnnotation e))
        Nothing -> Nothing]
  assignPartial (ArrayExpr sz arr) (ArrayPValue b lst)
    = (if b then Just (sz .==. (Const (genericLength lst) ()))
       else Nothing):
      [ case el of
         Just el' -> Just $ (App SMTSelect (arr,Const i ())) .==. (Const el' ann)
         Nothing -> Nothing
      | (i,el) <- zip [0..] lst ]
    where
      ((),ann) = extractAnnotation arr

instance Show AnyLispExpr where
  showsPrec p (AnyLispExpr e) = showsPrec p e

instance Show AnyLispType where
  showsPrec p (AnyLispType e) = showsPrec p e

instance Eq AnyLispType where
  (AnyLispType tp1) == (AnyLispType tp2) = case cast tp2 of
    Just tp2' -> tp1 == tp2'
    Nothing -> False

instance Ord AnyLispType where
  compare (AnyLispType (tp1::LispType t1)) (AnyLispType (tp2::LispType t2)) = case cast tp2 of
    Just tp2' -> compare tp1 tp2'
    Nothing -> compare (typeOf (undefined::t1)) (typeOf (undefined::t2))

instance Eq AnyLispExpr where
  (AnyLispExpr e1) == (AnyLispExpr e2) = case cast e2 of
    Just e2' -> e1==e2'
    Nothing -> False

instance Ord AnyLispExpr where
  compare (AnyLispExpr (tp1::LispExpr t1)) (AnyLispExpr (tp2::LispExpr t2)) = case cast tp2 of
    Just tp2' -> compare tp1 tp2'
    Nothing -> compare (typeOf (undefined::t1)) (typeOf (undefined::t2))

instance Args AnyLispExpr where
  type ArgAnnotation AnyLispExpr = AnyLispType
  foldExprs f s e (AnyLispType tp) = do
    (ns,ne) <- foldExprs f s (case e of
                               AnyLispExpr e' -> case cast e' of
                                 Just e'' -> e'') tp
    return (ns,AnyLispExpr ne)
  foldsExprs f s lst (AnyLispType (tp::LispType t)) = do
    (ns,exprs,expr) <- foldsExprs f s (fmap (\(AnyLispExpr e,b) -> (case cast e of
                                                                     Just e' -> e'::LispExpr t,b)
                                            ) lst) tp
    return (ns,fmap AnyLispExpr exprs,AnyLispExpr expr)
  extractArgAnnotation (AnyLispExpr e) = AnyLispType (extractArgAnnotation e)
  toArgs (AnyLispType tp) xs = do
    (e,xs') <- toArgs tp xs
    return (AnyLispExpr e,xs')
  fromArgs (AnyLispExpr e) = fromArgs e
  getTypes _ (AnyLispType (tp::LispType t)) = getTypes (undefined::LispExpr t) tp
  getArgAnnotation _ _ = error "Cannot get arg annotation for lisp expression."

instance LiftArgs AnyLispExpr where
  type Unpacked AnyLispExpr = AnyLispValue
  liftArgs (AnyLispValue v) (AnyLispType tp) = case cast tp of
    Just tp' -> AnyLispExpr (liftArgs v tp')
  unliftArgs (AnyLispExpr e) unl = do
    re <- unliftArgs e unl
    return (AnyLispValue re)

instance PartialArgs AnyLispExpr where
  type PartialValue AnyLispExpr = AnyLispPValue
  maskValue _ (AnyLispPValue (pv::LispPValue t)) xs
    = (AnyLispPValue npv,xs')
    where
      (npv,xs') = maskValue (undefined::LispExpr t) pv xs
  unmaskValue _ (AnyLispValue (v::LispValue t))
    = AnyLispPValue (unmaskValue (undefined::LispExpr t) v)
  assignPartial (AnyLispExpr e) (AnyLispPValue v) = case cast v of
    Just v' -> assignPartial e v'
