module Realization.Lisp where

import Realization
import Realization.Lisp.Array
import Realization.Lisp.Value
import Args
import PartialArgs
import RSM

import Language.SMTLib2
import Language.SMTLib2.Pipe hiding (Var)
import Language.SMTLib2.Internals.Type.Nat
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Struct (Struct(..),Tree)
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Interface as I
import qualified Language.SMTLib2.Internals.Expression as E
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum
import Data.GADT.Compare
import Data.GADT.Show
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Typeable
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import System.IO (Handle)
import qualified Data.ByteString as BS
import Data.Attoparsec
import Control.Exception
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans
import Data.Functor.Identity

data LispName (sig :: ([Type],Tree Type)) where
  LispName :: List Repr sz -> Struct Repr tp -> T.Text -> LispName '(sz,tp)

newtype Annotation (sig :: k) = Annotation { getAnnotation :: Map T.Text L.Lisp } deriving (Eq,Ord)

data NoRef (t :: k) = NoRef deriving Show

data LispProgram
  = LispProgram { programAnnotation :: Map T.Text L.Lisp
                , programState :: DMap LispName Annotation
                , programInput :: DMap LispName Annotation
                , programGates :: DMap LispName LispGate
                , programNext :: DMap LispName (LispVar LispExpr)
                , programProperty :: [LispExpr BoolType]
                , programInit :: DMap LispName LispInit
                , programInvariant :: [LispExpr BoolType]
                , programAssumption :: [LispExpr BoolType]
                , programPredicates :: [LispExpr BoolType]
                } deriving Show

data LispGate (sig :: ([Type],Tree Type)) = LispGate { gateDefinition :: LispVar LispExpr sig
                                                     , gateAnnotation :: Annotation sig }

newtype LispInit sig = LispInit (LispValue sig LispExpr)

data LispVarCat = Input | State | Gate deriving (Eq,Ord,Show,Typeable)

data LispVar e (sig :: ([Type],Tree Type)) where
  NamedVar :: LispName sig -> LispVarCat -> LispVar e sig
  LispStore :: LispVar e '(sz,tp)
            -> List Natural idx
            -> List e sz
            -> e (Struct.ElementIndex tp idx)
            -> LispVar e '(sz,tp)
  LispConstr :: LispValue sig e -> LispVar e sig
  LispITE :: e BoolType -> LispVar e sig -> LispVar e sig -> LispVar e sig

lispVarType :: GetType e => LispVar e '(sz,tp) -> (List Repr sz,Struct Repr tp)
lispVarType (NamedVar (LispName sz tps _) _) = (sz,tps)
lispVarType (LispStore var _ _ _) = lispVarType var
lispVarType (LispConstr val) = lispValueType val
lispVarType (LispITE _ v _) = lispVarType v

data LispExpr (t::Type) where
  LispExpr :: E.Expression NoRef NoRef NoRef NoRef NoRef NoRef NoRef LispExpr t
           -> LispExpr t
  LispRef :: LispVar LispExpr '(sz,tps)
          -> List Natural idx
          -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
  LispSize :: LispVar LispExpr '(sz,tps)
           -> Natural idx
           -> LispExpr (List.Index (SizeList sz) idx)
  LispEq :: LispVar LispExpr '(sz,tp)
         -> LispVar LispExpr '(sz,tp)
         -> LispExpr BoolType
  ExactlyOne :: [LispExpr BoolType] -> LispExpr BoolType
  AtMostOne :: [LispExpr BoolType] -> LispExpr BoolType

data LispSort = forall (sz :: [Type]) (tp::Tree Type).
                LispSort (List Repr sz) (Struct Repr tp)

instance GEq LispName where
  geq (LispName lvl1 tp1 n1) (LispName lvl2 tp2 n2) = do
    Refl <- geq lvl1 lvl2
    Refl <- geq tp1 tp2
    if n1==n2
      then return Refl
      else Nothing

instance GCompare LispName where
  gcompare (LispName lvl1 tp1 n1) (LispName lvl2 tp2 n2) = case gcompare lvl1 lvl2 of
    GEQ -> case gcompare tp1 tp2 of
      GEQ -> case compare n1 n2 of
        EQ -> GEQ
        LT -> GLT
        GT -> GGT
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance Show (LispName sig) where
  showsPrec p (LispName _ _ name) = showString (T.unpack name)

deriving instance Show (LispValue t LispExpr)
deriving instance Show (Size LispExpr lvl)
deriving instance Show (LispExpr e)
deriving instance Show (LispVar LispExpr t)
deriving instance Show (Annotation n)
deriving instance Show (LispGate sig)

instance GShow LispName where
  gshowsPrec = showsPrec

instance GShow LispExpr where
  gshowsPrec = showsPrec

instance GShow NoRef where
  gshowsPrec = showsPrec

instance GShow LispGate where
  gshowsPrec = showsPrec

instance ShowTag LispName LispInit where
  showTaggedPrec _ p (LispInit v) = showsPrec p v

instance ShowTag LispName (LispVar LispExpr) where
  showTaggedPrec _ = showsPrec

instance ShowTag LispName Annotation where
  showTaggedPrec _ = showsPrec

instance EqTag LispName LispUVal where
  eqTagged (LispName _ _ _) (LispName _ _ _) = (==)

instance EqTag LispName Annotation where
  eqTagged (LispName _ _ _) (LispName _ _ _) = (==)

instance OrdTag LispName LispUVal where
  compareTagged (LispName _ _ _) (LispName _ _ _) = compare

instance OrdTag LispName Annotation where
  compareTagged (LispName _ _ _) (LispName _ _ _) = compare

instance ShowTag LispName LispUVal where
  showTaggedPrec _ = showsPrec

instance ShowTag LispName LispGate where
  showTaggedPrec _ = showsPrec

instance EqTag LispName LispPVal' where
  eqTagged _ _ = (==)

instance OrdTag LispName LispPVal' where
  compareTagged _ _ = compare

instance ShowTag LispName LispPVal' where
  showTaggedPrec _ = showsPrec

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

programToLisp :: LispProgram -> L.Lisp
programToLisp prog = L.List (L.Symbol "program":elems)
  where
    elems = ann ++ states ++ inputs ++ gates ++ next ++ init ++
            prop ++ invar ++ assump ++ preds
    ann = annToLisp (programAnnotation prog)
    states = if DMap.null (programState prog)
             then []
             else [L.List (L.Symbol "state":states')]
    states' = [ L.List $ [L.Symbol name,lispSortToLisp lvl tp] ++
                         (annToLisp ann)
              | ((LispName lvl tp name)) :=> (Annotation ann)
                  <- DMap.toAscList (programState prog) ]
    inputs = if DMap.null (programInput prog)
             then []
             else [L.List (L.Symbol "input":inputs')]
    inputs' = [ L.List $ [L.Symbol name,lispSortToLisp lvl tp] ++
                         (annToLisp ann)
              | ((LispName lvl tp name)) :=> (Annotation ann)
                  <- DMap.toAscList (programInput prog) ]
    annToLisp :: Map T.Text L.Lisp -> [L.Lisp]
    annToLisp mp = concat [ [L.Symbol $ T.cons ':' name,cont]
                          | (name,cont) <- Map.toList mp ]
    gates = if DMap.null (programGates prog)
            then []
            else [L.List (L.Symbol "gates":gates')]
    gates' = [ L.List $ [L.Symbol name
                        ,lispSortToLisp lvl tp
                        ,lispVarToLisp (gateDefinition gate)]++
               (annToLisp (getAnnotation $ gateAnnotation gate))
             | ((LispName lvl tp name)) :=> gate
                 <- DMap.toAscList (programGates prog) ]
    next = if DMap.null (programNext prog)
           then []
           else [L.List (L.Symbol "next":next')]
    next' = [ L.List [L.Symbol name
                     ,lispVarToLisp lvar]
            | (nm@(LispName _ _ name)) :=> lvar
                <- DMap.toAscList (programNext prog) ]
    prop = if null (programProperty prog)
           then []
           else [L.List (L.Symbol "property":prop')]
    prop' = [ lispExprToLisp p | p <- programProperty prog ]
    init = if DMap.null (programInit prog)
           then []
           else [L.List (L.Symbol "init":init')]
    init' = [ L.List [L.Symbol name
                     ,lispValueToLisp val]
            | (LispName _ _ name) :=> (LispInit val)  <- DMap.toList $ programInit prog ]
    invar = if null (programInvariant prog)
            then []
            else [L.List (L.Symbol "invariant":invar')]
    invar' = [ lispExprToLisp p | p <- programInvariant prog ]
    assump = if null (programAssumption prog)
             then []
             else [L.List (L.Symbol "assumption":assump')]
    assump' = [ lispExprToLisp p | p <- programAssumption prog ]
    preds = if null (programPredicates prog)
            then []
            else [L.List (L.Symbol "predicates":preds')]
    preds' = [ lispExprToLisp p | p <- programPredicates prog ]

lispExprToLisp :: LispExpr t -> L.Lisp
lispExprToLisp (LispExpr e)
  = runIdentity $ exprToLispWith
    (error "No vars")
    (error "No qvars")
    (error "No functions")
    (error "No constructors")
    (error "No constructors")
    (error "No fields")
    (error "No fun args")
    (error "No let exprs")
    (return.lispExprToLisp) e
lispExprToLisp (LispRef var idx)
  = case idx' of
      [] -> var'
      _ -> L.List [L.List (L.Symbol "_":
                           L.Symbol "select":idx')
                  ,var']
  where
    idx' = statToLisp idx
    var' = lispVarToLisp var

    statToLisp :: LispIndex sig -> [L.Lisp]
    statToLisp = runIdentity . List.toList
                 (\i -> return $ L.Number $ fromInteger $ naturalToInteger i)
lispExprToLisp (LispSize var idx)
  = L.List [L.List [L.Symbol "_"
                   ,L.Symbol "size"
                   ,L.Number $ fromInteger $ naturalToInteger idx]
           ,lispVarToLisp var]
lispExprToLisp (LispEq lhs rhs)
  = L.List [L.List [L.Symbol "_"
                   ,L.Symbol "eq"]
           ,lispVarToLisp lhs
           ,lispVarToLisp rhs]
lispExprToLisp (ExactlyOne xs)
  = L.List $ (L.Symbol "exactly-one"):
             fmap lispExprToLisp xs
lispExprToLisp (AtMostOne xs)
  = L.List $ (L.Symbol "at-most-one"):
             fmap lispExprToLisp xs

lispVarToLisp :: LispVar LispExpr sig -> L.Lisp
lispVarToLisp (NamedVar (LispName _ _ name) _) = L.Symbol name
lispVarToLisp (LispStore var idx dyn el)
  = L.List (L.List (L.Symbol "_":
                    L.Symbol "store":
                    statIdx idx):
            lispVarToLisp var:
            dynIdx dyn++
            [lispExprToLisp el])
  where
    statIdx :: LispIndex idx -> [L.Lisp]
    statIdx = runIdentity . List.toList
              (return . L.Number . fromInteger . naturalToInteger)

    dynIdx :: List LispExpr sz -> [L.Lisp]
    dynIdx = runIdentity . List.toList (return.lispExprToLisp)
lispVarToLisp (LispConstr val)
  = lispValueToLisp val
lispVarToLisp (LispITE cond ifT ifF)
  = L.List [L.List [L.Symbol "_"
                   ,L.Symbol "ite"]
           ,lispExprToLisp cond
           ,lispVarToLisp ifT
           ,lispVarToLisp ifF]

lispValueToLisp :: LispValue sig LispExpr -> L.Lisp
lispValueToLisp (LispValue (Size Nil Nil) (Singleton (Sized e)))
  = lispExprToLisp e
lispValueToLisp (LispValue sz val)
  = L.List [L.Symbol "value"
           ,L.List $ lispSizeToLisp sz
           ,lispStructToLisp val]
  where
    lispStructToLisp :: Struct (Sized LispExpr lvl) tp -> L.Lisp
    lispStructToLisp (Singleton (Sized e)) = lispExprToLisp e
    lispStructToLisp (Struct tps)
      = L.List (L.Symbol "struct":
                lispStructsToLisp tps)
    lispStructsToLisp :: List (Struct (Sized LispExpr lvl)) sig -> [L.Lisp]
    lispStructsToLisp Nil = []
    lispStructsToLisp (x ::: xs) = lispStructToLisp x:
                                   lispStructsToLisp xs
    lispSizeToLisp :: Size LispExpr lvl -> [L.Lisp]
    lispSizeToLisp (Size _ lst) = runIdentity $ List.toList (return.lispExprToLisp) lst

lispSortToLisp :: List Repr sz -> Struct Repr sig -> L.Lisp
lispSortToLisp sz tp = case sz of
  Nil -> structTypeToLisp tp
  _ -> L.List [L.Symbol "array"
              ,L.List (runIdentity $ List.toList (return.typeSymbol) sz)
              ,structTypeToLisp tp]
  where
    structTypeToLisp :: Struct Repr sig -> L.Lisp
    structTypeToLisp (Singleton repr) = typeSymbol repr
    structTypeToLisp (Struct tps)
      = L.List (L.Symbol "struct":structTypesToLisp tps)

    structTypesToLisp :: List (Struct Repr) sig -> [L.Lisp]
    structTypesToLisp Nil = []
    structTypesToLisp (x ::: xs) = structTypeToLisp x:
                                   structTypesToLisp xs

parseProgram :: L.Lisp -> LispProgram
parseProgram descr = case descr of
  L.List (L.Symbol "program":elems)
    -> let (ann,elems') = parseAnnotation elems Map.empty
           mp = Map.fromList [ (key,defs) | L.List (L.Symbol key:defs) <- elems ]
           (state,state') = case Map.lookup "state" mp of
                              Just sts -> parseVarMap sts
                              Nothing -> (DMap.empty,Map.empty)
           (inp,inp') = case Map.lookup "input" mp of
                          Just sts -> parseVarMap sts
                          Nothing -> (DMap.empty,Map.empty)
           (gts,gts') = case Map.lookup "gates" mp of
                          Just lst -> parseGates state' inp' lst
                          Nothing -> (DMap.empty,Map.empty)
           nxt = case Map.lookup "next" mp of
             Just nxts -> parseNexts state' inp' gts' nxts
             Nothing -> DMap.empty
           prop = case Map.lookup "property" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' inp' gts' BoolRepr) xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing properties: "++err
           init = case Map.lookup "init" mp of
             Nothing -> DMap.empty
             Just xs -> parseInit state' xs
           invar = case Map.lookup "invariant" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' inp' Map.empty BoolRepr) xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing invariants: "++err
           assume = case Map.lookup "assumption" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' inp' gts' BoolRepr) xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing assumptions: "++err
           preds = case Map.lookup "predicates" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' Map.empty Map.empty BoolRepr) xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing predicates: "++err
       in LispProgram { programAnnotation = ann
                      , programState = state
                      , programInput = inp
                      , programGates = gts
                      , programNext = nxt
                      , programProperty = prop
                      , programInit = init
                      , programInvariant = invar
                      , programAssumption = assume
                      , programPredicates = preds }

parseAnnotation :: [L.Lisp] -> Map T.Text L.Lisp -> (Map T.Text L.Lisp,[L.Lisp])
parseAnnotation [] cur = (cur,[])
parseAnnotation (x:xs) cur = case x of
  L.Symbol (T.uncons -> Just (':',name)) -> case xs of
    y:ys -> parseAnnotation ys (Map.insert name y cur)
    [] -> error $ "Key "++show name++" is missing a value"
  _ -> let (res,unparsed) = parseAnnotation xs cur
       in (res,x:unparsed)

parseLispType :: L.Lisp
              -> (forall (sz::[Type]) (tp::Tree Type).
                  List Repr sz -> Struct Repr tp -> a)
              -> a
parseLispType (L.List [L.Symbol "array",
                       L.List idx,
                       tp]) f
  = List.reifyList (\el f -> case runExcept $ lispToSort
                                  (error $ "Only basic sorts are supported.") el of
                             Right (Sort tp) -> f tp
                   ) idx $
    \sz -> parseLispStructType tp $ f sz
parseLispType tp f
  = parseLispStructType tp $ f Nil

parseLispStructType :: L.Lisp
                    -> (forall (tp::Tree Type).
                        Struct Repr tp -> a)
                    -> a
parseLispStructType (L.List (L.Symbol "struct":tps)) f
  = parseLispStructTypes tps $
    \tps' -> f (Struct tps')
parseLispStructType tp f = case runExcept $ lispToSort
                                (error $ "Only basic sorts are supported.") tp of
  Right (Sort tp) -> f (Singleton tp)

parseLispStructTypes :: [L.Lisp]
                     -> (forall (tp::[Tree Type]).
                         List (Struct Repr) tp -> a)
                     -> a
parseLispStructTypes [] f = f Nil
parseLispStructTypes (x:xs) f
  = parseLispStructType x $
    \tp -> parseLispStructTypes xs $
      \tps -> f (tp ::: tps)

parseVarMap :: [L.Lisp] -> (DMap LispName Annotation,Map T.Text LispSort)
parseVarMap lst
  = (DMap.fromList [ (LispName lvl tp name) :=> (Annotation ann)
                   | (name,LispSort lvl tp,ann) <- lst' ],
     Map.fromList [ (name,srt) | (name,srt,ann) <- lst' ])
  where
    lst' = fmap (\st -> case st of
                          L.List def -> case parseAnnotation def Map.empty of
                            (ann,[L.Symbol name,sort])
                              -> (name,parseLispType sort LispSort,ann)
                ) lst

parseGates :: Map T.Text LispSort -> Map T.Text LispSort -> [L.Lisp]
           -> (DMap LispName LispGate,Map T.Text LispSort)
parseGates st inps lst = (mp1,mp2)
  where
    mp1 = DMap.fromList [ (LispName lvl tp name) :=>
                          (case runExcept $ parseLispVar st inps mp2 def
                                (\e -> let (lvl',tp') = lispVarType e
                                       in case geq lvl lvl' of
                                       Just Refl -> case geq tp tp' of
                                         Just Refl -> return e
                                         Nothing -> throwE $ "type error"
                                       Nothing -> throwE $ "type error") of
                             Right var -> LispGate var (Annotation ann)
                             Left err -> error $ "Cannot parse gate: "++show name++"; "++show def++" ["++err++"]")
                        | (name,LispSort lvl tp,def,ann) <- lst' ]
    mp2 = Map.fromList [ (name,srt) | (name,srt,_,_) <- lst' ]
    lst' = fmap parseGate lst
    parseGate (L.List descr) = case parseAnnotation descr Map.empty of
      (ann,[L.Symbol name,sort,def])
        -> (name,parseLispType sort LispSort,def,ann)

parseNexts :: Map T.Text LispSort -> Map T.Text LispSort -> Map T.Text LispSort
           -> [L.Lisp]
           -> DMap LispName (LispVar LispExpr)
parseNexts st inps gts lst = DMap.fromList lst'
  where
    lst' = fmap parseNext lst
    parseNext (L.List [L.Symbol name,def])
      = case Map.lookup name st of
          Just (LispSort lvl tp)
            -> (LispName lvl tp name) :=>
               (case runExcept $ parseLispVar st inps gts def
                     (\e -> let (lvl',tp') = lispVarType e
                            in case geq lvl lvl' of
                            Just Refl -> case geq tp tp' of
                              Just Refl -> return e
                              Nothing -> throwE $ "type error: expected "++show tp++", got: "++show tp'
                            Nothing -> throwE $ "type error") of
                  Right res -> res
                  Left err -> error $ "Cannot parse next expression: "++show name++"; "++show def++" ["++err++"]")

parseInit :: Map T.Text LispSort -> [L.Lisp] -> DMap LispName LispInit
parseInit st lst = DMap.fromList lst'
  where
    lst' = fmap parseInit' lst
    parseInit' (L.List [L.Symbol name,def])
      = case Map.lookup name st of
          Just (LispSort lvl tp)
            -> (LispName lvl tp name) :=>
               (case runExcept $ parseLispVar Map.empty Map.empty Map.empty def
                     (\e -> let (lvl',tp') = lispVarType e
                            in case geq lvl lvl' of
                            Just Refl -> case geq tp tp' of
                              Just Refl -> return e
                              Nothing -> throwE "type error"
                            Nothing -> throwE "type error") of
                  Right (LispConstr val) -> LispInit val)
    parseInit' x = error $ "Cannot parse init element: "++show x

parseLispVarCat :: Map T.Text LispSort -- ^ State vars
                -> Map T.Text LispSort -- ^ Input vars
                -> Map T.Text LispSort -- ^ Gate vars
                -> L.Lisp
                -> LispParse (T.Text,LispVarCat,LispSort)
parseLispVarCat state inps gts (L.Symbol name)
  = case Map.lookup name state of
      Just tp -> return (name,State,tp)
      Nothing -> case Map.lookup name inps of
        Just tp -> return (name,Input,tp)
        Nothing -> case Map.lookup name gts of
          Just tp -> return (name,Gate,tp)
          Nothing -> throwE $ "Unknown symbol "++show name
parseLispVarCat _ _ _ l = throwE $ "Not a variable: "++show l

parseLispVar :: Map T.Text LispSort -- ^ State vars
             -> Map T.Text LispSort -- ^ Input vars
             -> Map T.Text LispSort -- ^ Gate vars
             -> L.Lisp
             -> (forall lvl tp. LispVar LispExpr '(lvl,tp) -> LispParse a)
             -> LispParse a
{-parseLispVar state inps gts (L.List (L.List (L.Symbol "_":L.Symbol "store":stat):
                                     expr:val:dyns)) f
  = parseLispVar state inps gts expr $
    \arr -> do
       val <- parseLispVarT state inps gts val
       
  expr' <- parseLispVar state inps gts expr
  stat' <- mapM (L.parseMaybe L.parseLisp) stat
  val' <- parseLispExpr' state inps gts UntypedExpr val
  dyns' <- mapM (parseLispExpr' state inps gts (\e -> case cast e of
                                                 Just e' -> e')
                ) dyns
  return $ LispStore expr' stat' dyns' val'-}
parseLispVar state inps gts expr f
  = catchE (do
              (name,cat,LispSort lvl tp) <- parseLispVarCat state inps gts expr
              f (NamedVar (LispName lvl tp name) cat))
    (\_ -> parseLispValue state inps gts expr $
           \val -> f (LispConstr val))

parseIdx :: Struct Repr tps -> [Integer]
         -> (forall idx. LispIndex idx -> Repr (Struct.ElementIndex tps idx) -> LispParse a)
         -> LispParse a
parseIdx (Singleton r) [] f
  = f Nil r
parseIdx (Struct args) (i:is) f
  = parseListIdx args i $
    \prI sub -> parseIdx sub is $
                \idx r -> f (prI ::: idx) r

parseListIdx :: List e tps -> Integer
             -> (forall idx. Natural idx -> e (List.Index tps idx) -> LispParse a)
             -> LispParse a
parseListIdx (x ::: xs) 0 f = f Zero x
parseListIdx (x ::: xs) n f
  = parseListIdx xs (n-1) $
    \idx -> f (Succ idx)

parseSizeIdx :: List Repr tps -> Integer
             -> (forall idx. Natural idx -> Repr (List.Index (SizeList tps) idx) -> LispParse a)
             -> LispParse a
parseSizeIdx sz = parseListIdx (sizeListType sz)

parseDynIdx :: Map T.Text LispSort -- ^ State vars
            -> Map T.Text LispSort -- ^ Input vars
            -> Map T.Text LispSort -- ^ Gate vars
            -> [L.Lisp]
            -> (forall sz. List LispExpr sz
                -> LispParse a)
            -> LispParse a
parseDynIdx _ _ _ [] f = f Nil
parseDynIdx st inp gts (x:xs) f = parseLispExpr st inp gts Nothing x $
                                  \e -> parseDynIdx st inp gts xs $
                                        \es -> f (e ::: es)

parseLispExprT :: Map T.Text LispSort -- ^ State vars
               -> Map T.Text LispSort -- ^ Input vars
               -> Map T.Text LispSort -- ^ Gate vars
               -> Repr t
               -> L.Lisp
               -> LispParse (LispExpr t)
parseLispExprT state inps gates tp expr
  = parseLispExpr state inps gates (Just $ Sort tp) expr
    (\e -> case geq tp (getType e) of
      Just Refl -> return e
      Nothing -> throwE $ "Type error in expression "++show e)

parseLispExpr :: Map T.Text LispSort -- ^ State vars
              -> Map T.Text LispSort -- ^ Input vars
              -> Map T.Text LispSort -- ^ Gate vars
              -> Maybe Sort
              -> L.Lisp
              -> (forall t. LispExpr t -> LispParse a)
              -> LispParse a
parseLispExpr state inps gates srt (L.List ((L.Symbol "exactly-one"):xs)) f = do
  xs' <- mapM (parseLispExprT state inps gates BoolRepr) xs
  f (ExactlyOne xs')
parseLispExpr state inps gates srt (L.List ((L.Symbol "at-most-one"):xs)) f = do
  xs' <- mapM (parseLispExprT state inps gates BoolRepr) xs
  f (AtMostOne xs')
parseLispExpr state inps gts _ (L.List [L.List (L.Symbol "_":L.Symbol "select":stat)
                                       ,expr]) f = do
  idxs <- case mapM (L.parseMaybe L.parseLisp) stat of
    Nothing -> throwE $ "Can not parse static indices: "++show stat
    Just r -> return r
  parseLispVar state inps gts expr $
    \var -> let (lvl,tps) = lispVarType var
            in parseIdx tps idxs $
               \idx tp
               -> f (LispRef var idx)
parseLispExpr state inps gts srt (L.List [L.List [L.Symbol "_"
                                                 ,L.Symbol "size"
                                                 ,L.Number (L.I n)]
                                         ,var]) f
  = parseLispVar state inps gts var $
    \var' -> let (sz,tps) = lispVarType var'
             in parseSizeIdx sz n $
                \idx tp -> f (LispSize var' idx)
parseLispExpr state inps gts _ (L.List [L.List [L.Symbol "_",
                                                L.Symbol "eq"],
                                        var1,var2]) f
  = parseLispVar state inps gts var1 $
    \var1' -> parseLispVar state inps gts var2 $
              \var2' -> case geq var1' var2' of
              Just Refl -> f (LispEq var1' var2')
              Nothing -> throwE "type error"
parseLispExpr state inps gates srt expr f
  = catchE (do
               (name,cat,LispSort lvl tps)
                  <- parseLispVarCat state inps gates expr
               case tps of
                 Singleton tp' -> case lvl of
                   Nil -> f (LispRef (NamedVar (LispName lvl tps name) cat) Nil)
                   _ -> throwE $ "Variable is not a singleton"
                 _ -> throwE $ "Variable is not a singleton")
    (\_ -> lispToExprWith parser srt expr (f . LispExpr))
  where
    parser = LispParser { parseFunction = \_ _ _ _ _ _ -> throwE $ "Invalid function"
                        , parseDatatype = \_ _ -> throwE $ "Invalid datatype"
                        , parseVar = \_ _ _ _ _ _ -> throwE $ "Invalid variable"
                        , parseRecursive = parseLispExpr state inps gates
                        , registerQVar = \_ _ -> (NoRef,parser)
                        , registerLetVar = \_ _ -> (NoRef,parser) }

parseSize :: Map T.Text LispSort -- ^ State vars
          -> Map T.Text LispSort -- ^ Input vars
          -> Map T.Text LispSort -- ^ Gate vars
          -> [L.Lisp]
          -> (forall sz. Size LispExpr sz -> LispParse a)
          -> LispParse a
parseSize st inps gts es f
  = case parseSize' (\e g -> case runExcept (parseLispExpr st inps gts Nothing e
                                             (return.g)) of
                      Right res -> res) es (Just . f) of
  Just res -> res

parseLispValue :: Map T.Text LispSort -- ^ State vars
               -> Map T.Text LispSort -- ^ Input vars
               -> Map T.Text LispSort -- ^ Gate vars
               -> L.Lisp
               -> (forall lvl tp. LispValue '(lvl,tp) LispExpr -> LispParse a)
               -> LispParse a
parseLispValue state inps gates
  (L.List [L.Symbol "value"
          ,L.List sizes
          ,struct]) f = parseSize state inps gates sizes $
                        \sz
                        -> parseStruct (sizeIndices sz) struct $
                           \str -> f $ LispValue sz str
  where
    parseStruct :: List Repr sz
                -> L.Lisp
                -> (forall tp. Struct (Sized LispExpr sz) tp -> LispParse a)
                -> LispParse a
    parseStruct lvl (L.List (L.Symbol "struct":xs)) f
      = parseStructs lvl xs $
        \xs' -> f (Struct xs')
    parseStruct lvl expr f
      = parseVal lvl expr $
        \e -> f (Singleton e)

    parseStructs :: List Repr sz
                 -> [L.Lisp]
                 -> (forall tp. List (Struct (Sized LispExpr sz)) tp -> LispParse a)
                 -> LispParse a
    parseStructs lvl [] f = f Nil
    parseStructs lvl (x:xs) f
      = parseStruct lvl x $
        \x' -> parseStructs lvl xs $
        \xs' -> f (x' ::: xs')

    parseVal :: List Repr sz
             -> L.Lisp
             -> (forall tp. Sized LispExpr sz tp -> LispParse a)
             -> LispParse a
    parseVal lvl lsp f
      = parseLispExpr state inps gates Nothing lsp $
        \e -> castVal lvl e (\_ -> f)

    castVal :: List Repr sz
            -> LispExpr tp
            -> (forall tp'. Repr tp' -> Sized LispExpr sz tp' -> LispParse a)
            -> LispParse a
    castVal sz e f = case isArrayed (getType e) sz $
                          \tp -> f tp (Sized e) of
                     Just res -> res
               
parseLispValue state inps gates expr f
  = parseLispExpr state inps gates Nothing expr $
    \e -> f (LispValue (Size Nil Nil) (Singleton (Sized e)))

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

newtype LispValue' e sig = LispValue' (LispValue sig e)

newtype LispState e = LispState { lispState :: DMap LispName (LispValue' e) }

data LispRev tp where
  LispRev :: LispName '(lvl,tps)
          -> RevValue '(lvl,tps) tp
          -> LispRev tp

instance Show (LispRev tp) where
  showsPrec p (LispRev name (RevVar Nil)) = showsPrec p name
  showsPrec p (LispRev name (RevVar idx))
    = showsPrec p name . showsPrec p idx
  showsPrec p (LispRev name (RevSize lvl)) = showsPrec p name . showString "@" . showsPrec p lvl

instance GShow LispRev where
  gshowsPrec = showsPrec

instance GEq LispRev where
  geq (LispRev name1 rev1) (LispRev name2 rev2) = do
    Refl <- geq name1 name2
    Refl <- geq rev1 rev2
    return Refl

instance Eq (LispRev tp) where
  (==) = defaultEq

instance GCompare LispRev where
  gcompare (LispRev name1 rev1) (LispRev name2 rev2) = case gcompare name1 name2 of
    GLT -> GLT
    GGT -> GGT
    GEQ -> case gcompare rev1 rev2 of
      GLT -> GLT
      GGT -> GGT
      GEQ -> GEQ

instance Ord (LispRev tp) where
  compare = defaultCompare

instance GetType LispRev where
  getType (LispRev (LispName sz tps _) (RevVar idx))
    = arrayType sz (Struct.elementIndex tps idx)
  getType (LispRev (LispName sz tps _) (RevSize i))
    = List.index (sizeListType sz) i

instance TransitionRelation LispProgram where
  type State LispProgram = LispState 
  type Input LispProgram = LispState
  type RealizationProgress LispProgram = LispState
  type PredicateExtractor LispProgram = RSMState (Set T.Text) (LispRev IntType)
  stateAnnotation = programState
  inputAnnotation = programInput
  initialState prog st
    = relativize st (LispState DMap.empty)
      (error "Realization.Lisp: initial state references gates.")
      expr
    where
      expr = case [ LispEq
                     (NamedVar name State)
                     (LispConstr val)
                  | (name@(LispName _ _ _) :=> LispInit val) <- DMap.toList (programInit prog) ] of
        [] -> LispExpr (E.Const (BoolValue True))
        [e] -> e
        xs -> LispExpr (AndLst xs)
  stateInvariant prog st inp = do
    invars <- mapM (relativize st inp
                    (error "Realization.Lisp: invariant references gates.")
                   ) (programInvariant prog)
    case invars of
      [] -> I.constant True
      [x] -> return x
      xs -> embed $ AndLst xs
  startingProgress _ = LispState DMap.empty
  declareAssumptions mkGate prog st inp gts
    = runStateT (mapM (relativize st inp (declareGate mkGate prog st inp)
                      ) (programAssumption prog)
                ) gts
  declareAssertions mkGate prog st inp gts
    = runStateT (mapM (relativize st inp (declareGate mkGate prog st inp)
                      ) (programProperty prog)
                ) gts
  declareNextState mkGate prog st inp gts = do
    let lst = DMap.toAscList (programNext prog)
    (nlst,ngts) <- runStateT
                   (mapM (\(name@(LispName _ _ name') :=> var) -> do
                            nvar <- relativizeVar st inp
                                      (declareGate mkGate prog st inp) var >>=
                                      defineGate (\n e -> lift $ mkGate n e) (T.unpack name')
                            return $ name :=> (LispValue' nvar)
                         ) lst) gts
    return (LispState $ DMap.fromAscList nlst,ngts)
  suggestedPredicates prog
    = [ (False,mkCompExpr (\st -> relativize st (LispState DMap.empty)
                                  (\_ -> undefined) expr
                          ) (programState prog))
      | expr <- programPredicates prog ]
  defaultPredicateExtractor _ = return emptyRSM
  extractPredicates prog rsm (LispConcr full) (LispPart part) = liftIO $ do
    (rsm2,lines) <- mineStates (createPipe "z3" ["-smt2","-in"]) rsm1
    return (rsm2,concat $ fmap (\ln -> [mkLine E.Ge ln
                                       ,mkLine E.Gt ln]) lines)
    where
      rsm1 = addRSMState activePc ints rsm
      pcs = DMap.filterWithKey (\name val -> case DMap.lookup name (programState prog) of
                                   Just (Annotation ann) -> case Map.lookup "pc" ann of
                                     Just (L.Symbol "true") -> True
                                     _ -> False
                               ) full
      activePc :: Set T.Text
      activePc = Set.fromList [ name
                              | (LispName _ _ name)
                                :=> (LispU (Singleton (BoolValueC True))) <- DMap.toList pcs ]
      ints :: Map (LispRev IntType) Integer
      ints = Map.fromList
             [ el --(LispRev name (RevVar idx),val)
             | name@(LispName Nil _ _) :=> (LispPVal' (LispP p)) <- DMap.toList part
             , el <- pints (\idx val -> (LispRev name (RevVar idx),val)) p ]

      pints :: (forall idx. (Struct.ElementIndex tps idx ~ IntType)
                => LispIndex idx -> Integer -> a)
            -> Struct PValue tps
            -> [a]
      pints f = runIdentity . Struct.flattenIndex
                (\idx pval -> case pval of
                  PValue (IntValueC v) -> return [f idx v]
                  _ -> return [])
                (return.concat)
      
      mkLine :: E.OrdOp -> (Integer,[(LispRev IntType,Integer)])
             -> CompositeExpr LispState BoolType
      mkLine op (c,coeff)
        = mkCompExpr
          (\st -> do
              c' <- embedConst (IntValueC c)
              sum <- mapM (\(rev,val) -> do
                              let var = accessComposite rev st
                              case val of
                                1 -> return var
                                -1 -> embed $ Neg var
                                _ -> do
                                  rval <- embedConst (IntValueC val)
                                  embed $ rval :*: var
                          ) coeff
              case sum of
                [x] -> embed (Ord op c' x)
                _ -> do
                  rsum <- embed $ PlusLst sum
                  embed (Ord op c' rsum))
          (programState prog)
  isEndState prog (LispState st)
    = embed (OrLst conds) >>= embed.Not
    where
      conds = [ r | name :=> val <- DMap.toList pcs
                  , r <- case val of
                    LispValue' (LispValue (Size Nil Nil)
                                (Singleton (Sized x)))
                      -> case getType x of
                      BoolRepr -> [x]
                      _ -> []
                    _ -> [] ]
      pcs = DMap.filterWithKey (\name val -> case DMap.lookup name (programState prog) of
                                 Just (Annotation ann) -> case Map.lookup "pc" ann of
                                   Just (L.Symbol "true") -> True
                                   _ -> False
                               ) st

declareGate :: (Embed m e,GetType e)
            => (forall t. Maybe String -> e t -> m (e t))
            -> LispProgram -> LispState e -> LispState e
            -> LispName '(lvl,tp)
            -> StateT (LispState e) m (LispValue '(lvl,tp) e)
declareGate mkGate prog st inp name@(LispName _ _ name') = do
  LispState mp <- get
  case DMap.lookup name mp of
    Just (LispValue' r) -> return r
    Nothing -> case DMap.lookup name (programGates prog) of
      Just gate -> do
        val <- relativizeVar st inp (declareGate mkGate prog st inp) (gateDefinition gate)
        gt <- lift $ defineGate mkGate (T.unpack name') val
        LispState mp' <- get
        put $ LispState $ DMap.insert name (LispValue' gt) mp'
        return gt
      Nothing -> error $ "Internal error: Gate "++show name++" not defined."

defineGate :: Monad m
           => (forall t. Maybe String -> e t -> m (e t))
           -> String -> LispValue '(lvl,tp) e
           -> m (LispValue '(lvl,tp) e)
defineGate mkGate name (LispValue sz val) = do
  sz <- defineSize mkGate name sz
  v <- Struct.mapM (\(Sized e) -> do
                       e' <- mkGate (Just name) e
                       return (Sized e')
                   ) val
  return (LispValue sz v)
  where
    defineSize :: Monad m
               => (forall t. Maybe String -> e t -> m (e t))
               -> String -> Size e lvl' -> m (Size e lvl')
    defineSize mkGate name (Size tps szs) = do
      nszs <- List.mapM (mkGate (Just name)) szs
      return (Size tps nszs)

relativize :: (Embed m e,GetType e)
           => LispState e
           -> LispState e
           -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
           -> LispExpr t
           -> m (e t)
relativize st inp gts (LispExpr e) = do
  e' <- E.mapExpr err err err err err err err
        (relativize st inp gts) e
  embed e'
  where
    err = error "Realization.Lisp.relativize: LispExpr shouldn't have any user defined entities."
relativize st inp gts (LispRef var stat) = do
  LispValue _ val <- relativizeVar st inp gts var
  let Sized res = Struct.elementIndex val stat
  return res
relativize st inp gts (LispSize var idx) = do
  LispValue sz _ <- relativizeVar st inp gts var
  let Size _ szs = sz
  return $ List.index szs idx
relativize st inp gts (LispEq v1 v2) = do
  val1 <- relativizeVar st inp gts v1
  val2 <- relativizeVar st inp gts v2
  eqValue val1 val2
relativize st inp gts (ExactlyOne es) = do
  es' <- mapM (relativize st inp gts) es
  oneOf es'
relativize st inp gts (AtMostOne es) = do
  es' <- mapM (relativize st inp gts) es
  atMostOneOf es'
relativize st inp gts e = error $ "Realization.Lisp.relativize: Cannot relativize: "++show e

oneOf :: Embed m e
      => [e BoolType] -> m (e BoolType)
oneOf [] = I.constant True
oneOf [x] = return x
oneOf xs = do
  disj <- oneOf' [] xs
  embed $ OrLst disj
  where
    oneOf' :: Embed m e
           => [e BoolType] -> [e BoolType] -> m [e BoolType]
    oneOf' _ [] = return []
    oneOf' xs (y:ys) = do
      negs <- mapM (embed.Not) (xs++ys)
      conj <- let arg = y:negs
              in embed $ AndLst arg
      rest <- oneOf' (y:xs) ys
      return (conj:rest)

atMostOneOf :: Embed m e
            => [e BoolType] -> m (e BoolType)
atMostOneOf [] = I.constant True
atMostOneOf [x] = I.constant True
atMostOneOf xs = oneOf' [] xs >>= embed.OrLst
  where
    oneOf' :: Embed m e
           => [e BoolType] -> [e BoolType] -> m [e BoolType]
    oneOf' xs [] = do
      negs <- mapM (embed.Not) xs
      conj <- embed $ AndLst negs
      return [conj]
    oneOf' xs (y:ys) = do
      negs <- mapM (embed.Not) (xs++ys)
      trm <- embed $ AndLst (y:negs)
      rest <- oneOf' (y:xs) ys
      return (trm:rest)

relativizeVar :: (Embed m e,GetType e)
              => LispState e
              -> LispState e
              -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
              -> LispVar LispExpr '(sz,tps)
              -> m (LispValue '(sz,tps) e)
relativizeVar (LispState st) (LispState inp) gts (NamedVar name@(LispName _ _ _) cat)
  = case cat of
      Input -> case DMap.lookup name inp of
        Just (LispValue' r) -> return r
      State -> case DMap.lookup name st of
        Just (LispValue' r) -> return r
      Gate -> gts name
relativizeVar st inp gts (LispConstr val)
  = relativizeValue st inp gts val
relativizeVar st inp gts (LispStore v idx dyn el) = do
  LispValue sz val <- relativizeVar st inp gts v
  nel <- relativize st inp gts el
  ndyn <- List.mapM (relativize st inp gts) dyn
  (_,nval) <- Struct.access val idx $
              \arr -> accessArrayElement ndyn arr $
                      \_ -> return ((),nel)
  return (LispValue sz nval)
relativizeVar st inp gts (LispITE c ifT ifF) = do
  nc <- relativize st inp gts c
  ifT' <- relativizeVar st inp gts ifT
  ifF' <- relativizeVar st inp gts ifF
  iteValue nc ifT' ifF'

relativizeValue :: (Embed m e,GetType e)
                => LispState e
                -> LispState e
                -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
                -> LispValue sig LispExpr
                -> m (LispValue sig e)
relativizeValue st inp gts (LispValue sz val) = do
  nsz <- relativizeSize st inp gts sz
  nval <- Struct.mapM (\(Sized e) -> fmap Sized (relativize st inp gts e)
                      ) val
  return $ LispValue nsz nval
  where
    relativizeSize :: (Embed m e,GetType e)
                   => LispState e -> LispState e
                   -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
                   -> Size LispExpr lvl
                   -> m (Size e lvl)
    relativizeSize st inp gts (Size tps sz) = do
      nsz <- List.mapM (relativize st inp gts) sz
      return $ Size tps nsz

relativizeIndex :: (Embed m e,GetType e)
                => LispState e
                -> LispState e
                -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
                -> List LispExpr sz
                -> m (List e sz)
relativizeIndex st inp gts idx = List.mapM (relativize st inp gts) idx

instance Composite LispState where
  type CompDescr LispState = DMap LispName Annotation
  type RevComp LispState = LispRev
  compositeType mp = LispState $
                     DMap.fromList [ name :=> (LispValue' (compositeType (sz,tps)))
                                   | (name@(LispName sz tps _) :=> _) <- DMap.toList mp ]
  foldExprs f (LispState mp) = do
    let lst = DMap.toAscList mp
    nlst <- mapM (\(name@(LispName _ _ _) :=> (LispValue' val)) -> do
                    nval <- foldExprs (\rev -> f (LispRev name rev)) val
                    return (name :=> (LispValue' nval))
                 ) lst
    return $ LispState $ DMap.fromAscList nlst
  createComposite mkVar ann = do
    lst' <- mapM (\(name@(LispName lvl tp _) :=> _) -> do
                    res <- createComposite (\tp' rev -> mkVar tp' (LispRev name rev)) (lvl,tp)
                    return $ name :=> (LispValue' res)
                 ) lst
    return $ LispState (DMap.fromAscList lst')
    where
      lst = DMap.toAscList ann
  accessComposite (LispRev name rev) (LispState mp) = case DMap.lookup name mp of
    Just (LispValue' val) -> accessComposite rev val
  eqComposite (LispState mp1) (LispState mp2) = do
    eqs <- sequence [ eqComposite v1 v2
                    | (name@(LispName _ _ _) :=> (LispValue' v1)) <- DMap.toList mp1
                    , let LispValue' v2 = mp2 DMap.! name ]
    embed $ AndLst eqs
  revName _ (LispRev (LispName _ _ name) _) = T.unpack name

--instance GetType LispRev where
--  getType (LispRev name rev) = getType rev

newtype LispConcr = LispConcr (DMap LispName LispUVal) deriving (Eq,Ord)

instance Show LispConcr where
  showsPrec p (LispConcr mp) = showsPrec p (DMap.toList mp)

instance LiftComp LispState where
  type Unpacked LispState = LispConcr
  liftComp (LispConcr mp) = do
    let lst = DMap.toAscList mp
    nlst <- mapM (\(name@(LispName _ _ _) :=> val) -> do
                    nval <- lift' val
                    return (name :=> (LispValue' nval))
                 ) lst
    return $ LispState $ DMap.fromAscList nlst
    where
      lift' :: (Embed m e,GetType e) => LispUVal '(lvl,tps) -> m (LispValue '(lvl,tps) e)
      lift' (LispU str) = do
        str' <- liftStruct str
        return (LispValue (Size Nil Nil) str')
      lift' (LispUArray sz szs tps xs) = do
        xs' <- mapM lift' xs
        liftValues sz szs tps xs'

  unliftComp f (LispState mp) = do
    let lst = DMap.toAscList mp
    nlst <- mapM (\(name@(LispName _ _ _) :=> (LispValue' val)) -> do
                    nval <- unlift' f val
                    return (name :=> nval)
                 ) lst
    return $ LispConcr $ DMap.fromAscList nlst
    where
      unlift' :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
              -> LispValue '(lvl,tps) e -> m (LispUVal '(lvl,tps))
      unlift' f lv@(LispValue sz val) = case sz of
        Size Nil Nil -> do
          str <- extractStruct f val
          return $ LispU str
        Size (tp ::: tps) (sz' ::: szs) -> do
          vals <- unliftValue f lv
          vals' <- mapM (unlift' f) vals
          return $ LispUArray tp tps
            (Struct.map
             (\e -> sizedType e (sizeIndices sz)) val)
            vals'

newtype LispPVal' sig = LispPVal' (LispPVal sig) deriving (Typeable,Eq,Ord)

instance Show (LispPVal' sig) where
  showsPrec p (LispPVal' pval) = showsPrec p pval

newtype LispPart = LispPart (DMap LispName LispPVal') deriving (Eq,Ord,Show)

instance PartialComp LispState where
  type Partial LispState = LispPart
  maskValue _ (LispPart mp) xs
    = let (res,nmp) = DMap.mapAccumLWithKey
                      (\xs (LispName _ _ _) (LispPVal' p::LispPVal' '(lvl,tp))
                       -> let (np,nxs) = maskLispValue p xs
                          in (nxs,LispPVal' np)
                      ) xs mp
      in (LispPart nmp,res)
  unmaskValue _ (LispConcr cmp)
    = let lst = DMap.toAscList cmp
          nlst = fmap (\(name@(LispName _ _ _) :=> cval)
                        -> name :=> LispPVal' (unmaskLispValue cval)
                      ) lst
      in LispPart $ DMap.fromAscList nlst
  assignPartial f (LispState mp1) (LispPart mp2) = do
    let lst1 = DMap.toAscList mp1
    mkPartial lst1
    where
      mkPartial [] = return []
      mkPartial ((name@(LispName _ _ _) :=> LispValue' var):xs)
        = case DMap.lookup name mp2 of
            Just (LispPVal' val) -> do
              r1 <- assignPartialLisp f var val
              r2 <- mkPartial xs
              return (r1++r2)

instance GEq NoRef where
  geq _ _ = error "geq for NoRef called."

instance GCompare NoRef where
  gcompare _ _ = error "gcompare for NoRef called."

instance GetType NoRef where
  getType _ = error "getType called for NoRef."

instance GetFunType NoRef where
  getFunType _ = error "getFunType called for NoRef."

instance GetConType NoRef where
  getConType _ = error "getConType called for NoRef."

instance GetFieldType NoRef where
  getFieldType _ = error "getFieldType called for NoRef."

instance (GetType e,GEq e) => GEq (LispVar e) where
  geq (NamedVar n1 cat1) (NamedVar n2 cat2)
    = if cat1/=cat2
      then Nothing
      else geq n1 n2
  geq (LispStore v1 i1 d1 e1) (LispStore v2 i2 d2 e2) = do
    Refl <- geq v1 v2
    Refl <- geq i1 i2
    Refl <- geq d1 d2
    Refl <- geq e1 e2
    return Refl
  geq (LispConstr v1@(LispValue _ _)) (LispConstr v2@(LispValue _ _)) = do
    (Refl,Refl) <- geqValue v1 v2
    return Refl
  geq (LispITE c1 t1 f1) (LispITE c2 t2 f2) = do
    Refl <- geq c1 c2
    Refl <- geq t1 t2
    Refl <- geq f1 f2
    return Refl
  geq _ _ = Nothing

instance GEq LispExpr where
  geq (LispExpr e1) (LispExpr e2) = geq e1 e2
  geq (LispRef v1 i1) (LispRef v2 i2) = do
    Refl <- geq v1 v2
    Refl <- geq i1 i2
    return Refl
  geq (LispSize v1 i1) (LispSize v2 i2) = do
    Refl <- geq v1 v2
    Refl <- geq i1 i2
    return Refl
  geq (LispEq x1 y1) (LispEq x2 y2) = do
    Refl <- geq x1 x2
    Refl <- geq y1 y2
    return Refl
  geq (ExactlyOne xs) (ExactlyOne ys)
    = if xs==ys
      then Just Refl
      else Nothing
  geq (AtMostOne xs) (AtMostOne ys)
    = if xs==ys
      then Just Refl
      else Nothing
  geq _ _ = Nothing

instance Eq (LispExpr t) where
  (==) = defaultEq

instance GetType LispExpr where
  getType (LispExpr e) = getType e
  getType (LispRef v i) = arrayType lvl (lispIndexType tps i)
    where
      (lvl,tps) = lispVarType v
  getType (LispSize v i) = List.index (sizeListType sz) i
    where
      (sz,tps) = lispVarType v
  getType (LispEq _ _) = BoolRepr
  getType (ExactlyOne _) = BoolRepr
  getType (AtMostOne _) = BoolRepr

instance Embed Identity LispExpr where
  type EmVar Identity LispExpr = NoRef
  type EmQVar Identity LispExpr = NoRef
  type EmFun Identity LispExpr = NoRef
  type EmConstr Identity LispExpr = NoRef
  type EmField Identity LispExpr = NoRef
  type EmFunArg Identity LispExpr = NoRef
  type EmLVar Identity LispExpr = NoRef
  embed = return.LispExpr
  embedQuantifier = error "LispExpr doesn't embed quantifier."
  embedConstrTest = error "LispExpr doesn't embed datatypes."
  embedGetField = error "LispExpr doesn't embed datatypes."
  embedConst c = do
    v <- valueFromConcrete (error "LispExpr doesn't embed datatypes.") c
    return (LispExpr (E.Const v))

instance Embed m e => Embed (StateT (LispState e) m) e where
  type EmVar (StateT (LispState e) m) e = EmVar m e
  type EmQVar (StateT (LispState e) m) e = EmQVar m e
  type EmFun (StateT (LispState e) m) e = EmFun m e
  type EmConstr (StateT (LispState e) m) e = EmConstr m e
  type EmField (StateT (LispState e) m) e = EmField m e
  type EmFunArg (StateT (LispState e) m) e = EmFunArg m e
  type EmLVar (StateT (LispState e) m) e = EmLVar m e
  embed = lift . embed
  embedQuantifier q tps f = lift (embedQuantifier q tps f)
  embedConstrTest name dt e = lift (embedConstrTest name dt e)
  embedGetField name fname dt pr e = lift (embedGetField name fname dt pr e)
  embedConst = lift . embedConst
  embedTypeOf = lift . embedTypeOf
