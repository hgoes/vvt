{-# LANGUAGE DeriveDataTypeable,OverloadedStrings,RankNTypes,ScopedTypeVariables,
             ViewPatterns,GADTs,TypeFamilies,FlexibleContexts #-}
module Realization.Lisp where

import Realization
import Realization.Lisp.Value
--import PartialArgs
import RSM

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Pipe
import Data.Unit

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.AttoLisp as L
import Data.Typeable
import Data.Fix
import Data.Monoid
import qualified Data.ByteString as BS
import System.IO (Handle)
import Data.Attoparsec
import Data.Traversable
import Prelude hiding (mapM,sequence)
import Control.Monad.State (runStateT,get,put,lift)
import Data.List (genericIndex)
import Control.Monad (mplus)
import Control.Exception
import Control.Monad.Trans (liftIO)
import Debug.Trace

data LispProgram
  = LispProgram { programAnnotation :: Annotation
                , programDataTypes :: DataTypeInfo
                , programState :: Map T.Text (LispType,Annotation)
                , programInput :: Map T.Text (LispType,Annotation)
                , programGates :: Map T.Text (LispType,LispVar)
                , programNext :: Map T.Text LispVar
                , programProperty :: [SMTExpr Bool]
                , programInit :: Map T.Text LispValue
                , programInvariant :: [SMTExpr Bool]
                , programAssumption :: [SMTExpr Bool]
                , programPredicates :: [SMTExpr Bool]
                }

type Annotation = Map T.Text L.Lisp

data LispVarCat = Input | State | Gate deriving (Eq,Ord,Show,Typeable)

data LispVar = NamedVar T.Text LispVarCat LispType
             | LispStore LispVar [Integer] [SMTExpr Integer] (SMTExpr Untyped)
             | LispConstr LispValue
             | LispITE (SMTExpr Bool) LispVar LispVar
             deriving (Eq,Ord,Show,Typeable)

data LispVarAccess = LispVarAccess LispVar [Integer] [SMTExpr Integer]
                   | LispSizeAccess LispVar [SMTExpr Integer]
                   | LispSizeArrAccess LispVar Integer
                   | LispEq LispVar LispVar
                   deriving (Eq,Ord,Show,Typeable)

data LispException = LispException LispAction SomeException deriving Typeable

data LispAction = TranslateGate T.Text
                | DeclareNextState T.Text
                | CreateInput T.Text
                | CreateInvariant
                | Parsing L.Lisp
                deriving Typeable

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
           dts = emptyDataTypeInfo
           state = case Map.lookup "state" mp of
                    Just sts -> parseVarMap sts
                    Nothing -> Map.empty
           inp = case Map.lookup "input" mp of
                  Just sts -> parseVarMap sts
                  Nothing -> Map.empty
           gates = case Map.lookup "gates" mp of
             Just gts -> let gts' = fmap (\gt -> case gt of
                                           L.List [L.Symbol name,sort,def]
                                             -> (name,case parseLispType sort of
                                                       Just srt -> case parseLispTopVar state inp gates def of
                                                         Just var -> (srt,var)
                                                         Nothing -> error $ "Failed to parse gate definition: "++show def
                                                       Nothing -> error $ "Failed to parse sort: "++show sort
                                                )
                                           _ -> error $ "Failed to parse gate: "++show gt
                                         ) gts
                         in Map.fromList gts'
             Nothing -> Map.empty
           next = case Map.lookup "next" mp of
             Just nxts -> let nxts' = fmap (\nxt -> case nxt of
                                             L.List [L.Symbol name,def]
                                               -> case parseLispTopVar state inp gates def of
                                                   Just var -> (name,var)
                                                   Nothing -> error $ "Failed to parse next value of "++show name++": "++show def
                                             _ -> error $ "Failed to parse next expression: "++show nxt
                                           ) nxts
                          in Map.fromList nxts'
           prop = case Map.lookup "property" mp of
             Nothing -> []
             Just xs -> fmap (\x -> case parseLispExpr' state inp gates cast x of
                               Just (Just y) -> y
                             ) xs
           initAssign = case Map.lookup "init" mp of
             Nothing -> Map.empty
             Just xs -> Map.fromList [ case parseLispTopVar Map.empty Map.empty Map.empty def of
                                        Just v -> case v of
                                          LispConstr val -> (name,val)
                                          _ -> error $ "Init cannot be an expression: "++show def
                                        Nothing -> error $ "Cannot parse init value: "++show def
                                     | L.List [L.Symbol name,def] <- xs ]
           invar = case Map.lookup "invariant" mp of
             Nothing -> []
             Just xs -> fmap (\x -> case parseLispExpr' state inp Map.empty cast x of
                               Just (Just y) -> y
                               _ -> error $ "Cannot parse invariant: "++show x
                             ) xs
           assume = case Map.lookup "assumption" mp of
             Nothing -> []
             Just xs -> fmap (\x -> case parseLispExpr' state inp gates cast x of
                               Just (Just y) -> y
                               _ -> error $ "Cannot parse assumption: "++show x
                             ) xs
           preds = case Map.lookup "predicate" mp of
             Nothing -> []
             Just xs -> fmap (\x -> case parseLispExpr' state Map.empty Map.empty cast x of
                               Just (Just y) -> y
                               _ -> error $ "Cannot parse predicate: "++show x
                             ) xs
       in LispProgram { programAnnotation = ann
                      , programDataTypes = dts
                      , programState = state
                      , programInput = inp
                      , programGates = gates
                      , programNext = next
                      , programProperty = prop
                      , programInit = initAssign
                      , programInvariant = invar
                      , programAssumption = assume
                      , programPredicates = preds
                      }
  _ -> error $ "Invalid lisp program: "++show descr
  where
    parseVarMap lst = Map.fromList $
                      fmap (\st -> case st of
                                    L.List def -> case parseAnnotation def Map.empty of
                                      (ann,[L.Symbol name,sort])
                                        -> case parseLispType sort of
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

programToLisp :: LispProgram -> L.Lisp
programToLisp prog = L.List ([L.Symbol "program"]++
                             annLst++
                             defLst)
  where
    renderAnnotation mp = concat [ [L.Symbol $ T.cons ':' key,entr]
                                 | (key,entr) <- Map.toList mp ]
    annLst = renderAnnotation (programAnnotation prog)
    defLst = [L.List $ [L.Symbol "state"]++stateLst
             ,L.List $ [L.Symbol "input"]++inputLst
             ,L.List $ [L.Symbol "gates"]++gatesLst
             ,L.List $ [L.Symbol "next"]++nextLst
             ,L.List $ [L.Symbol "property"]++propLst
             ,L.List $ [L.Symbol "init"]++initAssignLst
             ,L.List $ [L.Symbol "invariant"]++invarLst
             ,L.List $ [L.Symbol "assumption"]++assumpLst
             ,L.List $ [L.Symbol "predicate"]++predLst]
    stateLst = [ L.List $ [L.Symbol name
                          ,printLispType sort]++renderAnnotation ann
               | (name,(sort,ann)) <- Map.toList (programState prog) ]
    inputLst = [ L.List $ [L.Symbol name
                          ,printLispType sort]++renderAnnotation ann
               | (name,(sort,ann)) <- Map.toList (programInput prog) ]
    gatesLst = [ L.List [L.Symbol name
                        ,printLispType sort
                        ,printLispVar (programDataTypes prog) gate]
               | (name,(sort,gate)) <- Map.toList (programGates prog) ]
    nextLst = [ L.List [L.Symbol name
                       ,printLispVar (programDataTypes prog) def]
              | (name,def) <- Map.toList (programNext prog) ]
    propLst = fmap (printLispExpr (programDataTypes prog)
                   ) (programProperty prog)
    initAssignLst = [ L.List [L.Symbol name
                             ,printLispValue (programDataTypes prog) def]
                    | (name,def) <- Map.toList (programInit prog) ]
    invarLst = fmap (printLispExpr (programDataTypes prog)
                    ) (programInvariant prog)
    assumpLst = fmap (printLispExpr (programDataTypes prog)
                     ) (programAssumption prog)
    predLst = fmap (printLispExpr (programDataTypes prog)
                   ) (programPredicates prog)

exactlyOne :: SMTFunction [SMTExpr Bool] Bool
exactlyOne = SMTBuiltIn "exactly-one" ()

atMostOne :: SMTFunction [SMTExpr Bool] Bool
atMostOne = SMTBuiltIn "at-most-one" ()

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

atMostOneParser :: FunctionParser
atMostOneParser
  = FunctionParser $
    \lsp _ _ -> case lsp of
    L.Symbol "at-most-one" -> Just parse
    _ -> Nothing
  where
    parse = OverloadedParser { sortConstraint = all (== Fix BoolSort)
                             , deriveRetSort = \_ -> Just (Fix BoolSort)
                             , parseOverloaded = \_ _ app -> Just (app atMostOne) }


parseLispType :: L.Lisp -> Maybe LispType
parseLispType (L.List [L.Symbol "array",
                       L.Number n,
                       tp]) = do
  rtp <- parseLispStructType tp
  return $ LispType (round n) rtp
parseLispType tp = do
  rtp <- parseLispStructType tp
  return $ LispType 0 rtp

parseLispStructType :: L.Lisp -> Maybe (LispStruct Sort)
parseLispStructType (L.List (L.Symbol "struct":tps)) = do
  rtps <- mapM parseLispStructType tps
  return $ Struct rtps
parseLispStructType tp = do
  rtp <- lispToSort tp
  return $ Singleton rtp

printLispType :: LispType -> L.Lisp
printLispType (LispType n tp) = case n of
  0 -> tp'
  _ -> L.List [L.Symbol "array",
               L.Number (fromIntegral n),
               tp']
  where
    tp' = printLispStructType tp
    printLispStructType (Singleton sort) = sortToLisp sort
    printLispStructType (Struct tps) = L.List (L.Symbol "struct":fmap printLispStructType tps)

parseLispVarCat :: Map T.Text (LispType,Annotation)
                -> Map T.Text (LispType,Annotation)
                -> Map T.Text (LispType,LispVar)
                -> L.Lisp
                -> Maybe (T.Text,LispVarCat,LispType)
parseLispVarCat state inps gts (L.Symbol name)
  = case Map.lookup name state of
     Just (tp,_) -> return (name,State,tp)
     Nothing -> case Map.lookup name inps of
       Just (tp,_) -> return (name,Input,tp)
       Nothing -> case Map.lookup name gts of
         Just (tp,_) -> return (name,Gate,tp)
         Nothing -> Nothing
parseLispVarCat _ _ _ _ = Nothing

parseLispTopVar :: Map T.Text (LispType,Annotation)
                -> Map T.Text (LispType,Annotation)
                -> Map T.Text (LispType,LispVar)
                -> L.Lisp
                -> Maybe LispVar
parseLispTopVar state inps gts lisp
  = parseLispVar state inps gts lisp
    `mplus`
    (do
        res <- parseLispExpr' state inps gts
               (\(expr::SMTExpr t)
                -> let sort = getSort (undefined::t) (extractAnnotation expr)
                   in withIndexableSort (undefined::SMTExpr Integer) sort $
                      \(_::u) -> case cast expr of
                                  Just res -> Val (res::SMTExpr u)) lisp
        return (LispConstr $ LispValue (Size []) (Singleton res)))

parseLispVar :: Map T.Text (LispType,Annotation)
             -> Map T.Text (LispType,Annotation)
             -> Map T.Text (LispType,LispVar)
             -> L.Lisp
             -> Maybe LispVar
parseLispVar state inps gts (L.List (L.List (L.Symbol "_":L.Symbol "store":stat):
                                     expr:val:dyns)) = do
  expr' <- parseLispVar state inps gts expr
  stat' <- mapM (L.parseMaybe L.parseLisp) stat
  val' <- parseLispExpr' state inps gts UntypedExpr val
  dyns' <- mapM (parseLispExpr' state inps gts (\e -> case cast e of
                                                 Just e' -> e')
                ) dyns
  return $ LispStore expr' stat' dyns' val'
parseLispVar state inps gts (L.List [L.List [L.Symbol "_",L.Symbol "ite"]
                                    ,cond,ifT,ifF]) = do
  cond' <- parseLispExpr' state inps gts (\e -> case cast e of
                                                 Just e' -> e') cond
  ifT' <- parseLispTopVar state inps gts ifT
  ifF' <- parseLispTopVar state inps gts ifF
  return (LispITE cond' ifT' ifF')
parseLispVar state inps gts lisp
  = (do
        (name,cat,tp) <- parseLispVarCat state inps gts lisp
        return $ NamedVar name cat tp)
    `mplus`
    (do
        val <- parseLispValue state inps gts lisp
        return $ LispConstr val)

lispVarType :: LispVar -> LispType
lispVarType (NamedVar _ _ tp) = tp
lispVarType (LispStore v _ _ _) = lispVarType v
lispVarType (LispConstr val) = extractArgAnnotation val
lispVarType (LispITE _ ifT _) = lispVarType ifT

parseLispVarAccess :: Map T.Text (LispType,Annotation)
                   -> Map T.Text (LispType,Annotation)
                   -> Map T.Text (LispType,LispVar)
                   -> L.Lisp
                   -> Maybe LispVarAccess
parseLispVarAccess state inps gts (L.List (L.List (L.Symbol "_":L.Symbol "select":stat):
                                           expr:dyns)) = do
  stat' <- mapM (L.parseMaybe L.parseLisp) stat
  expr' <- parseLispVar state inps gts expr
  dyns' <- mapM (parseLispExpr' state inps gts (\e -> case cast e of
                                                       Just e' -> e')
                ) dyns
  return $ LispVarAccess expr' stat' dyns'
parseLispVarAccess state inps gts (L.List (L.List [L.Symbol "_",L.Symbol "size"]:
                                           expr:dyns)) = do
  expr' <- parseLispVar state inps gts expr
  dyns' <- mapM (parseLispExpr' state inps gts (\e -> case cast e of
                                                       Just e' -> e')
                ) dyns
  return $ LispSizeAccess expr' dyns'
parseLispVarAccess state inps gts (L.List [L.List [L.Symbol "_",
                                                   L.Symbol "size-arrr",
                                                   n],
                                           expr]) = do
  n' <- L.parseMaybe L.parseLisp n
  expr' <- parseLispVar state inps gts expr
  return $ LispSizeArrAccess expr' n'
parseLispVarAccess state inps gts (L.List [L.List [L.Symbol "_",
                                                   L.Symbol "eq"],
                                           var1,var2]) = do
  expr1 <- parseLispTopVar state inps gts var1
  expr2 <- parseLispTopVar state inps gts var2
  return $ LispEq expr1 expr2
parseLispVarAccess state inps gts lisp = do
  expr <- parseLispVar state inps gts lisp
  return $ LispVarAccess expr [] []

lispVarAccessType :: LispVarAccess -> Sort
lispVarAccessType (LispVarAccess expr stat _) = indexType (lispVarType expr) stat
lispVarAccessType (LispSizeAccess _ _) = Fix IntSort
lispVarAccessType (LispSizeArrAccess _ n)
  = foldl (\tp _ -> Fix (ArraySort [Fix IntSort] tp)) (Fix IntSort) [1..n]
lispVarAccessType (LispEq _ _) = Fix BoolSort

parseLispValue :: Map T.Text (LispType,Annotation)
               -> Map T.Text (LispType,Annotation)
               -> Map T.Text (LispType,LispVar)
               -> L.Lisp
               -> Maybe LispValue
parseLispValue state inps gates (L.List [L.Symbol "value"
                                        ,L.List sizes
                                        ,struct]) = do
  rsizes <- mapM (\(i,lsp) -> parseSize i lsp) (zip [0..] sizes)
  rstruct <- parseStruct struct
  return (LispValue (Size rsizes) rstruct)
  where
    parseSize i lsp = withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) i $
                      \(_::t) -> case parseLispExpr' state inps gates cast lsp of
                                  Just (Just e) -> Just (SizeElement (e::SMTExpr t))
                                  _ -> Nothing
    parseStruct (L.List (L.Symbol "struct":xs)) = do
      xs' <- mapM parseStruct xs
      return $ Struct xs'
    parseStruct lsp = parseLispExpr' state inps gates
                      (\(expr::SMTExpr t)
                       -> let ann = extractAnnotation expr
                              sort = getSort (undefined::t) ann
                              (lvl,rsort) = derefSort 0 sort
                          in withIndexableSort (undefined::SMTExpr Integer) rsort $
                             \ut -> withLeveledArray ut (undefined::SMTExpr Integer) lvl $
                                    \(_::u) -> case cast expr of
                                                Just e -> Singleton (Val (e::SMTExpr u))
                      ) lsp
parseLispValue _ _ _ _ = Nothing

derefSort :: Integer -> Sort -> (Integer,Sort)
derefSort lvl (Fix (ArraySort _ el)) = derefSort (lvl+1) el
derefSort lvl sort = (lvl,sort)

parseLispExpr' :: Map T.Text (LispType,Annotation)
               -> Map T.Text (LispType,Annotation)
               -> Map T.Text (LispType,LispVar)
               -> (forall a. SMTType a => SMTExpr a -> b)
               -> L.Lisp
               -> Maybe b
parseLispExpr' state inps gates app
  = parseLispExpr state inps gates (commonFunctions `mappend` exactlyOneParser `mappend` atMostOneParser)
    (const Nothing)
    emptyDataTypeInfo
    app
    Nothing
    0

parseLispExpr :: Map T.Text (LispType,Annotation)
              -> Map T.Text (LispType,Annotation)
              -> Map T.Text (LispType,LispVar)
              -> FunctionParser
              -> (T.Text -> Maybe (SMTExpr Untyped))
              -> DataTypeInfo
              -> (forall a. SMTType a => SMTExpr a -> b)
              -> Maybe Sort
              -> Integer
              -> L.Lisp -> Maybe b
parseLispExpr state inps gates funs bound dts app sort lvl lisp
  = while (Parsing lisp) $
    case parseLispVarAccess state inps gates lisp of
     Just acc -> case acc of
       LispVarAccess (LispConstr (LispValue (Size []) (Singleton (Val v)))) [] []
         -> Just $ app v
       _ -> let sort = lispVarAccessType acc
            in withSort dts sort $
               \(_::t) ann -> Just $ app (InternalObj acc ann :: SMTExpr t)
     Nothing -> lispToExprWith (parseLispExpr state inps gates) funs bound dts app sort lvl lisp

printLispVar :: DataTypeInfo -> LispVar -> L.Lisp
printLispVar dts (NamedVar name _ _) = L.Symbol name
printLispVar dts (LispStore var stat dyn val)
  = L.List (L.List (L.Symbol "_":
                    L.Symbol "store":
                    fmap (\i -> L.Number $ fromIntegral i) stat):
            printLispVar dts var:
            printLispExpr dts val:
            fmap (printLispExpr dts) dyn)
printLispVar dts (LispITE cond ifT ifF)
  = L.List [L.List [L.Symbol "_"
                   ,L.Symbol "ite"]
           ,printLispExpr dts cond
           ,printLispVar dts ifT
           ,printLispVar dts ifF]
printLispVar dts (LispConstr val) = printLispValue dts val

printLispValue :: DataTypeInfo -> LispValue -> L.Lisp
printLispValue dts (LispValue (Size []) (Singleton (Val res))) = printLispExpr dts res
printLispValue dts (LispValue (Size sz) struct)
  = L.List [L.Symbol "value",
            L.List $ fmap (\(SizeElement el) -> printLispExpr dts el) sz,
            printLispStruct struct]
  where
    printLispStruct (Singleton (Val el)) = printLispExpr dts el
    printLispStruct (Struct xs) = L.List (L.Symbol "struct":
                                          fmap printLispStruct xs)

printLispExpr :: DataTypeInfo -> SMTExpr a -> L.Lisp
printLispExpr dts expr = exprToLispWith derel expr (error "printLispExpr error") dts
  where
    derel :: (Typeable b,Show b) => b -> L.Lisp
    derel (cast -> Just acc) = printLispVarAccess dts acc
    derel obj = error $ "Cannot derel "++show obj

printLispVarAccess :: DataTypeInfo -> LispVarAccess -> L.Lisp
printLispVarAccess dts (LispVarAccess var [] [])
  = printLispVar dts var
printLispVarAccess dts (LispVarAccess var stat dyn)
  = L.List (L.List (L.Symbol "_":L.Symbol "select":
                    fmap (\i -> L.Number $ fromIntegral i) stat):
            printLispVar dts var:
            fmap (printLispExpr dts) dyn)
printLispVarAccess dts (LispSizeAccess var dyn)
  = L.List (L.List [L.Symbol "_",L.Symbol "size"]:
            printLispVar dts var:
            fmap (printLispExpr dts) dyn)
printLispVarAccess dts (LispSizeArrAccess var n)
  = L.List [L.List [L.Symbol "_",L.Symbol "size-arr",L.Number $ fromIntegral n]
           ,printLispVar dts var]
printLispVarAccess dts (LispEq var1 var2)
  = L.List [L.List [L.Symbol "_",L.Symbol "eq"]
           ,printLispVar dts var1
           ,printLispVar dts var2]

relativize :: SMTType a
           => Map T.Text LispValue
           -> Map T.Text LispValue
           -> Map T.Text LispValue
           -> SMTExpr a
           -> SMTExpr a
relativize state inps gates (InternalObj (cast -> Just acc) ann)
  = relativizeVarAccess acc
  where
    relativizeVarAccess (LispVarAccess var stat dyn)
      = fst $ accessValue (\val -> case cast val of
                            Just val' -> (val',val)
                          ) stat dyn (relativizeVar state inps gates var)
    relativizeVarAccess (LispSizeAccess var dyn)
      = case cast $ fst $ accessSize (\i -> (i,i)) dyn (relativizeVar state inps gates var) of
         Just expr -> expr
    relativizeVarAccess (LispSizeArrAccess var n)
      = fst $ accessSizeArr (\i -> case cast i of
                              Just i' -> (i',i)) n (relativizeVar state inps gates var)
    relativizeVarAccess (LispEq var1 var2)
      = let tp = lispVarType var1
            val1 = relativizeVar state inps gates var1
            val2 = relativizeVar state inps gates var2
        in case cast (valueEq val1 val2) of
            Just res -> res
relativize state inps gates (App (SMTBuiltIn "exactly-one" _) xs)
  = case cast xs of
     Just xs' -> case cast (oneOf $ fmap (relativize state inps gates) xs') of
       Just r -> r
relativize state inps gates (App (SMTBuiltIn "at-most-one" _) xs)
  = case cast xs of
     Just xs' -> case cast (atMostOneOf $ fmap (relativize state inps gates) xs') of
       Just r -> r
relativize state inps gates (App fun args)
  = let (_,nargs) = foldExprsId (\_ e _ -> ((),relativize state inps gates e)) () args (extractArgAnnotation args)
    in App fun nargs
relativize state inps gates (UntypedExpr e) = UntypedExpr $ relativize state inps gates e
relativize state inps gates (UntypedExprValue e) = UntypedExprValue $ relativize state inps gates e
relativize state inps gates e = e

oneOf :: [SMTExpr Bool] -> SMTExpr Bool
oneOf xs = app or' (oneOf' [] xs)
  where
    oneOf' _ [] = []
    oneOf' xs (y:ys) = (app and' (y:(fmap not' $ xs++ys))):
                       (oneOf' (y:xs) ys)

atMostOneOf :: [SMTExpr Bool] -> SMTExpr Bool
atMostOneOf xs = app or' (oneOf' [] xs)
  where
    oneOf' xs [] = [app and' (fmap not' xs)]
    oneOf' xs (y:ys) = (app and' (y:(fmap not' $ xs++ys))):
                       (oneOf' (y:xs) ys)

relativizeVar :: Map T.Text LispValue
              -> Map T.Text LispValue
              -> Map T.Text LispValue
              -> LispVar
              -> LispValue
relativizeVar state _ _ (NamedVar name State _) = case Map.lookup name state of
  Just r -> r
  Nothing -> error $ "Failed to find state variable: "++show name
relativizeVar _ inps _  (NamedVar name Input _) = case Map.lookup name inps of
  Just r -> r
  Nothing -> error $ "Failed to find input variable: "++show name
relativizeVar _ _ gates (NamedVar name Gate  _) = case Map.lookup name gates of
  Just r -> r
  Nothing -> error $ "Failed to find gate variable: "++show name
relativizeVar state inps gates (LispStore var stat dyn val)
  = snd $ accessValue (const ((),castUntypedExpr val)) stat dyn
    (relativizeVar state inps gates var)
relativizeVar state inps gates (LispITE cond ifT ifF)
  = argITE (relativize state inps gates cond)
    (relativizeVar state inps gates ifT)
    (relativizeVar state inps gates ifF)
relativizeVar state inps gates (LispConstr (LispValue (Size szs) els))
  = LispValue (Size nszs) nels
  where
    nszs = fmap (\(SizeElement e) -> SizeElement $ relativize state inps gates e
                ) szs
    nels = relativizeStruct els
    relativizeStruct (Singleton (Val e)) = Singleton (Val $ relativize state inps gates e)
    relativizeStruct (Struct es) = Struct $ fmap relativizeStruct es

declareVar :: Monad m => LispProgram
              -> Map T.Text LispValue
              -> Map T.Text LispValue
              -> Map T.Text LispValue
              -> LispVar
              -> SMT' m (LispValue,Map T.Text LispValue)
declareVar prog state inps gates (NamedVar name cat _) = case cat of
  State -> case Map.lookup name state of
    Just res -> return (res,gates)
    Nothing -> error $ "Failed to find state variable while declaring "++show name
  Input -> case Map.lookup name inps of
    Just res -> return (res,gates)
    Nothing -> error $ "Failed to find input variable while declaring "++show name
  Gate -> case Map.lookup name gates of
    Just res -> return (res,gates)
    Nothing -> case Map.lookup name (programGates prog) of
      Just (tp,nvar) -> while (TranslateGate name) $ do
        (val1,gates1) <- declareVar prog state inps gates nvar
        val2 <- defineValue (T.unpack name) val1
        return (val2,Map.insert name val2 gates1)
      Nothing -> error $ "Failed to find gate variable while declaring "++show name
declareVar prog state inps gates (LispStore var stat dyn sval) = do
  (val,ngates) <- declareVar prog state inps gates var
  let res = snd $ accessValue (const ((),castUntypedExpr sval)) stat dyn val
  declareValue prog state inps ngates res
declareVar prog state inps gates (LispITE cond ifT ifF) = do
  (cond',gates1) <- declareExpr prog state inps gates cond
  (ifT',gates2) <- declareVar prog state inps gates1 ifT
  (ifF',gates3) <- declareVar prog state inps gates2 ifF
  declareValue prog state inps gates3 (argITE cond' ifT' ifF')
declareVar prog state inps gates (LispConstr val)
  = declareValue prog state inps gates val

defineValue :: Monad m => String -> LispValue -> SMT' m LispValue
defineValue name value = do
  (_,nvalue) <- foldExprs (\_ expr ann -> do
                              nexpr <- defConstNamed name expr
                              return ((),nexpr)
                          ) () value (extractArgAnnotation value)
  return nvalue

declareValue :: Monad m => LispProgram
             -> Map T.Text LispValue
             -> Map T.Text LispValue
             -> Map T.Text LispValue
             -> LispValue
             -> SMT' m (LispValue,Map T.Text LispValue)
declareValue prog state inps gates (LispValue (Size szs) els) = do
  (nszs,gates1) <- declareSize gates szs
  (nels,gates2) <- declareStruct gates els
  return (LispValue (Size nszs) nels,gates2)
  where
    declareSize gates [] = return ([],gates)
    declareSize gates (SizeElement e:es) = do
      (ne,gates1) <- declareExpr prog state inps gates e
      (nes,gates2) <- declareSize gates1 es
      return (SizeElement ne:nes,gates2)
    declareStruct gates (Singleton (Val e)) = do
      (ne,ngates) <- declareExpr prog state inps gates e
      return (Singleton (Val ne),ngates)
    declareStruct gates (Struct els) = do
      (nels,ngates) <- declareStructs gates els
      return (Struct nels,ngates)
    declareStructs gates [] = return ([],gates)
    declareStructs gates (e:es) = do
      (ne,gates1) <- declareStruct gates e
      (nes,gates2) <- declareStructs gates1 es
      return (ne:nes,gates2)

declareExpr :: (Monad m,SMTType a)
               => LispProgram
               -> Map T.Text LispValue
               -> Map T.Text LispValue
               -> Map T.Text LispValue
               -> SMTExpr a
               -> SMT' m (SMTExpr a,Map T.Text LispValue)
declareExpr prog state inps gates expr = do
  (ngates,[res]) <- foldExprM (\cgates e -> do
                                  (res,ngates) <- declareExpr' cgates e
                                  return (ngates,[res])
                              ) gates expr
  return (res,ngates)
  where
    declareExpr' :: (Monad m,SMTType t) => Map T.Text LispValue -> SMTExpr t
                 -> SMT' m (SMTExpr t,Map T.Text LispValue)
    declareExpr' gates (InternalObj (cast -> Just acc) _) = declareAccess gates acc
    declareExpr' gates expr = return (expr,gates)

    declareAccess :: (Monad m,SMTType t)
                  => Map T.Text LispValue -> LispVarAccess
                  -> SMT' m (SMTExpr t,Map T.Text LispValue)
    declareAccess gates (LispVarAccess var stat dyn) = do
      (val,ngates) <- declareVar prog state inps gates var
      let (res,_) = accessValue (\e -> case cast e of
                                  Just e' -> (e',e)
                                  Nothing -> error $ "Failed to access var "++show var++" with "++show stat++" "++show dyn++", got: "++show e
                                ) stat dyn val
      return (res,ngates)
    declareAccess gates (LispSizeAccess var dyn) = do
      (val,ngates) <- declareVar prog state inps gates var
      let (res,_) = accessSize (\i -> (i,i)) dyn val
      case cast res of
       Just res' -> return (res',ngates)
    declareAccess gates (LispSizeArrAccess var n) = do
      (val,ngates) <- declareVar prog state inps gates var
      let (res,_) = accessSizeArr (\i -> case cast i of
                                    Just i' -> (i',i)) n val
      return (res,ngates)
    declareAccess gates (LispEq var1 var2) = do
      (val1,gates1) <- declareVar prog state inps gates var1
      (val2,gates2) <- declareVar prog state inps gates1 var2
      case cast (argEq val1 val2) of
       Just res -> return res

instance TransitionRelation LispProgram where
  type State LispProgram = Map T.Text LispValue
  type Input LispProgram = Map T.Text LispValue
  type RevState LispProgram = Map Integer (T.Text,LispRev)
  type PredicateExtractor LispProgram = RSMState (Set T.Text) (T.Text,[Integer])
  type RealizationProgress LispProgram = Map T.Text LispValue
  createStateVars pre prog
    = sequence $ Map.mapWithKey
      (\name (tp,_) -> argVarsAnnNamed (pre++(T.unpack name)) tp
      ) (programState prog)
  createInputVars pre prog
    = sequence $ Map.mapWithKey
      (\name (tp,_) -> while (CreateInput name) $ argVarsAnnNamed (pre++(T.unpack name)) tp
      ) (programInput prog)
  initialState prog st = while CreateInvariant $ relativize st Map.empty Map.empty expr
    where
      expr = case [ InternalObj (LispEq
                                 (NamedVar name State
                                  (case Map.lookup name (programState prog) of
                                     Just (st,_) -> st))
                                 (LispConstr val)) ()
                  | (name,val) <- Map.toList (programInit prog) ] of
        [] -> constant True
        [e] -> e
        xs -> app and' xs
  stateInvariant prog inp st = relativize st inp Map.empty expr
    where
      expr = case programInvariant prog of
              [e] -> e
              [] -> constant True
              xs -> app and' xs
  startingProgress _ = Map.empty
  declareNextState prog st inp grp gates
    = runStateT (Map.traverseWithKey
                 (\name val -> while (DeclareNextState name) $ do
                     gates <- get
                     (nval,ngates) <- lift $ declareVar prog st inp gates val
                     put ngates
                     nval' <- lift $ defineValue (T.unpack name) nval
                     return nval') (programNext prog)) gates
  declareAssertions prog st inp gates
    = runStateT (mapM (\expr -> do
                          gates <- get
                          (expr',ngates) <- lift $ declareExpr prog st inp gates expr
                          put ngates
                          return expr'
                      ) (programProperty prog)
                ) gates
  declareAssumptions prog st inp gates
    = runStateT (mapM (\expr -> do
                          gates <- get
                          (expr',ngates) <- lift $ declareExpr prog st inp gates expr
                          put ngates
                          return expr'
                      ) (programAssumption prog)
                ) gates
  suggestedPredicates prog = fmap (\expr -> (False,
                                             \st -> relativize st Map.empty Map.empty expr)) $
                             programPredicates prog
  renderPartialState prog st = return (show st)
  renderPartialInput prog inp = return (show inp)
  defaultPredicateExtractor _ = return emptyRSM
  extractPredicates prog rsm full lifted = do
    let st = Set.fromList
             [ name
             | (name,(tp,ann)) <- Map.toList (programState prog)
             , Map.member "pc" ann
             , case Map.lookup name full of
                Just (Singleton (LispUValue (cast -> Just v))) -> v
                _ -> False ]
        vals = Map.foldlWithKey
               (\mp name pval -> getInts name [] pval mp
               ) Map.empty lifted
        getInts :: T.Text -> [Integer] -> LispStruct LispPValue -> Map (T.Text,[Integer]) Integer -> Map (T.Text,[Integer]) Integer
        getInts name idx (Singleton (LispPValue x)) mp = case cast x of
          Just i -> Map.insert (name,idx) i mp
          Nothing -> mp
        getInts name idx (Singleton LispPEmpty) mp = mp
        getInts name idx (Singleton (LispPArray arr)) mp = mp -- TODO
        getInts name idx (Struct vals) mp
          = foldl (\mp (i,pval) -> getInts name (idx++[i]) pval mp
                  ) mp (zip [0..] vals)

        nrsm = addRSMState st vals rsm
    (nrsm',props) <- mineStates (createSMTPipe "z3" ["-smt2","-in"]) nrsm
    return (nrsm',fmap (\prop st
                        -> prop (\(name,idx)
                                 -> relativize st Map.empty Map.empty
                                    (InternalObj (LispVarAccess (NamedVar name State
                                                                 (case Map.lookup name (programState prog) of
                                                                    Just (v,_) -> v))
                                                  idx []) ()))
                       ) props)
  --extractPredicates _ _ _ _ = return ((),[])
  annotationState prog = fmap fst (programState prog)
  annotationInput prog = fmap fst (programInput prog)
  createRevState pre prog = do
    st <- createStateVars pre prog
    return (st,Map.fromList $
               [ (var,(name,idx))
               | (name,val) <- Map.toList st
               , (var,idx) <- revVal val ])
    where
      revVal (LispValue (Size sz) val)
        = [ (getSizeIdx el,SizeSpec i)
          | (i,el) <- zip [0..] sz ]++
          [ (var,ElementSpec idx) | (var,idx) <- revStruct val ]
      revStruct (Struct vals) = [ (var,i:idx)
                                | (i,val) <- zip [0..] vals
                                , (var,idx) <- revStruct val ]
      revStruct (Singleton e) = [(getVarIdx e,[])]

      getSizeIdx :: SizeElement -> Integer
      getSizeIdx (SizeElement (Var i _)) = i

      getVarIdx :: LispVal -> Integer
      getVarIdx (Val (Var i _)) = i
  relativizeExpr prog rev expr st
    = snd $ foldExpr (\_ e -> case e of
                       Var i ann -> case Map.lookup i rev of
                         Just (name,idx) -> case Map.lookup name st of
                           Just (LispValue (Size sz) val) -> case idx of
                             SizeSpec i -> case sz `genericIndex` i of
                               SizeElement el -> case cast el of
                                                  Just el' -> ((),el')
                             ElementSpec is -> ((),getStruct val is)
                         Nothing -> error $ "Lisp.relativizeExpr: Cannot relativize var "++show i++" ("++show rev++")"
                       _ -> ((),e)
                     ) () expr
      where
        getStruct (Singleton (Val e)) [] = case cast e of
          Just e' -> e'
        getStruct (Struct vals) (i:is) = getStruct (vals `genericIndex` i) is

while :: LispAction -> a -> a
while act = mapException (LispException act)

instance Show LispAction where
  show (TranslateGate name) = "While translating gate "++T.unpack name++": "
  show (DeclareNextState name) = "While declaring next state for "++T.unpack name++": "
  show (CreateInput name) = "While creating input variable "++T.unpack name++": "
  show CreateInvariant = "While creating invariant: "
  show (Parsing lisp) = "While parsing "++show lisp++": "

instance Show LispException where
  show (LispException act err) = show act++show err

instance Exception LispException
