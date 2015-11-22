module Realization.Lisp where

import Realization
import Realization.Lisp.Value
import Args
import PartialArgs
--import RSM

import Language.SMTLib2
import Language.SMTLib2.Pipe hiding (Var)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum
import Data.GADT.Compare
import Data.GADT.Show
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Typeable
import qualified Data.AttoLisp as L
import Data.Constraint
import System.IO (Handle)
import qualified Data.ByteString as BS
import Data.Attoparsec
--import Control.Applicative
import Control.Exception
import Control.Monad.Trans.Except
import Control.Monad.Identity
import Control.Monad.Trans.Identity
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans

data LispName (sig :: (Nat,Struct Type)) where
  LispName :: (KnownNat lvl,GetStructType tp) => T.Text -> LispName '(lvl,tp)

newtype Annotation (sig :: k) = Annotation (Map T.Text L.Lisp)

data NoRef (t :: k) = NoRef deriving Show

data LispProgram
  = LispProgram { programAnnotation :: Map T.Text L.Lisp
                , programState :: DMap LispName Annotation
                , programInput :: DMap LispName Annotation
                , programGates :: DMap LispName (LispVar LispExpr)
                , programNext :: DMap LispName (LispVar LispExpr)
                , programProperty :: [LispExpr BoolType]
                , programInit :: DMap LispName LispInit
                , programInvariant :: [LispExpr BoolType]
                , programAssumption :: [LispExpr BoolType]
                , programPredicates :: [LispExpr BoolType]
                } deriving Show

newtype LispInit sig = LispInit (LispValue sig LispExpr)

data LispVarCat = Input | State | Gate deriving (Eq,Ord,Show,Typeable)

data LispVar e (sig :: (Nat,Struct Type)) where
  NamedVar :: LispName sig -> LispVarCat -> LispVar e sig
  LispStore :: GetType tp'
            => LispVar e '(lvl,tp)
            -> LispIndex tp tp' -> LispArrayIndex e lvl Z tp'
            -> e tp'
            -> LispVar e '(lvl,tp)
  LispConstr :: LispValue sig e -> LispVar e sig
  LispITE :: e BoolType -> LispVar e sig -> LispVar e sig -> LispVar e sig

data LispExpr (t::Type) where
  LispExpr :: Expression NoRef NoRef NoRef NoRef NoRef NoRef LispExpr t
           -> LispExpr t
  LispRef :: LispVar LispExpr '(lvl,tps)
          -> LispIndex tps tp -> LispArrayIndex LispExpr lvl rlvl tp
          -> LispExpr (LispType rlvl tp)
  LispEq :: (KnownNat lvl,GetStructType tp)
         => LispVar LispExpr '(lvl,tp)
         -> LispVar LispExpr '(lvl,tp)
         -> LispExpr BoolType
  ExactlyOne :: [LispExpr BoolType] -> LispExpr BoolType
  AtMostOne :: [LispExpr BoolType] -> LispExpr BoolType

data LispSort = forall (lvl::Nat) (tp::Struct Type).
                (KnownNat lvl,GetStructType tp) => LispSort (Proxy lvl) (Proxy tp)

instance GEq LispName where
  geq p@(LispName n1) q@(LispName n2) = case p of
    (_::LispName '(lvl1,tp1)) -> case q of
      (_::LispName '(lvl2,tp2)) -> do
        Refl <- sameNat (Proxy::Proxy lvl1) (Proxy::Proxy lvl2) 
        Refl <- geq (getStructType::LispStruct Repr tp1)
                    (getStructType::LispStruct Repr tp2)
        if n1==n2
          then return Refl
          else Nothing

instance GCompare LispName where
  gcompare p@(LispName n1) q@(LispName n2) = case p of
    (_::LispName '(lvl1,tp1)) -> case q of
      (_::LispName '(lvl2,tp2)) -> case gcompareNat (Proxy::Proxy lvl1) (Proxy::Proxy lvl2) of
        GEQ -> case gcompare (getStructType::LispStruct Repr tp1)
                             (getStructType::LispStruct Repr tp2) of
          GEQ -> case compare n1 n2 of
                   EQ -> GEQ
                   LT -> GLT
                   GT -> GGT
          GLT -> GLT
          GGT -> GGT
        GLT -> GLT
        GGT -> GGT

instance Show (LispName sig) where
  showsPrec p (LispName name) = showString (T.unpack name)

deriving instance Show (LispValue t LispExpr)
deriving instance Show (Size LispExpr lvl)
deriving instance Show (LispExpr e)
deriving instance Show (LispArrayIndex LispExpr lvl rlvl e)
deriving instance Show (LispVar LispExpr t)
deriving instance Show (Annotation n)

instance GShow LispName where
  gshowsPrec = showsPrec

instance GShow LispExpr where
  gshowsPrec = showsPrec

instance GShow NoRef where
  gshowsPrec = showsPrec

instance ShowTag LispName LispInit where
  showTaggedPrec _ p (LispInit v) = showsPrec p v

instance ShowTag LispName (LispVar LispExpr) where
  showTaggedPrec _ = showsPrec

instance ShowTag LispName Annotation where
  showTaggedPrec _ = showsPrec

instance ShowTag LispName LispUVal where
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
            prop ++ init ++ invar ++ assump ++ preds
    ann = annToLisp (programAnnotation prog)
    states = if DMap.null (programState prog)
             then []
             else [L.List (L.Symbol "state":states')]
    states' = [ L.List $ [L.Symbol name,lispSortToLisp nm] ++
                         (annToLisp ann)
              | (nm@(LispName name)) :=> (Annotation ann)
                  <- DMap.toAscList (programState prog) ]
    inputs = if DMap.null (programInput prog)
             then []
             else [L.List (L.Symbol "input":inputs')]
    inputs' = [ L.List $ [L.Symbol name,lispSortToLisp nm] ++
                         (annToLisp ann)
              | (nm@(LispName name)) :=> (Annotation ann)
                  <- DMap.toAscList (programInput prog) ]
    annToLisp :: Map T.Text L.Lisp -> [L.Lisp]
    annToLisp mp = concat [ [L.Symbol $ T.cons ':' name,cont]
                          | (name,cont) <- Map.toList mp ]
    gates = if DMap.null (programGates prog)
            then []
            else [L.List (L.Symbol "gates":gates')]
    gates' = [ L.List [L.Symbol name
                      ,lispSortToLisp nm
                      ,lispVarToLisp lvar]
             | (nm@(LispName name)) :=> lvar
                 <- DMap.toAscList (programGates prog) ]
    next = if DMap.null (programNext prog)
           then []
           else [L.List (L.Symbol "next":next')]
    next' = [ L.List [L.Symbol name
                     ,lispVarToLisp lvar]
            | (nm@(LispName name)) :=> lvar
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
            | (LispName name) :=> (LispInit val)  <- DMap.toList $ programInit prog ]
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

lispExprToLisp :: GetType t => LispExpr t -> L.Lisp
lispExprToLisp (LispExpr e)
  = runIdentity $ exprToLispWith
    (error "No vars")
    (error "No qvars")
    (error "No functions")
    (error "No constructors")
    (error "No constructors")
    (error "No fields")
    (error "No fun args")
    (return.lispExprToLisp) e
lispExprToLisp (LispRef var idx dyn)
  = case (idx',dyn') of
      ([],[]) -> var'
      _ -> L.List (L.List (L.Symbol "_":
                           L.Symbol "select":idx'):
                   var':dyn')
  where
    idx' = statToLisp idx
    dyn' = dynToLisp dyn
    var' = lispVarToLisp var

    statToLisp :: LispIndex sig tp -> [L.Lisp]
    statToLisp ValGet = []
    statToLisp (ValIdx i is)
      = (L.Number $ fromInteger $ natVal i):
        statToLisp is

    dynToLisp :: LispArrayIndex LispExpr lvl lvl' tp -> [L.Lisp]
    dynToLisp ArrGet = []
    dynToLisp (ArrIdx i is) = (lispExprToLisp i):
                              dynToLisp is
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
lispVarToLisp (NamedVar (LispName name) _) = L.Symbol name
lispVarToLisp (LispStore var idx dyn el)
  = L.List (L.List (L.Symbol "_":
                    L.Symbol "store":
                    statIdx idx):
            lispVarToLisp var:
            dynIdx dyn++
            [lispExprToLisp el])
  where
    statIdx :: LispIndex tp res -> [L.Lisp]
    statIdx ValGet = []
    statIdx (ValIdx pr idx) = (L.Number $ fromInteger $ natVal pr):
                              statIdx idx

    dynIdx :: LispArrayIndex LispExpr lvl lvl' tp -> [L.Lisp]
    dynIdx ArrGet = []
    dynIdx (ArrIdx i is) = lispExprToLisp i:
                           dynIdx is
lispVarToLisp (LispConstr val)
  = lispValueToLisp val
lispVarToLisp (LispITE cond ifT ifF)
  = L.List [L.List [L.Symbol "_"
                   ,L.Symbol "ite"]
           ,lispExprToLisp cond
           ,lispVarToLisp ifT
           ,lispVarToLisp ifF]

lispValueToLisp :: LispValue sig LispExpr -> L.Lisp
lispValueToLisp (LispValue { size = NoSize
                           , value = LSingleton (Val e) })
  = lispExprToLisp e
lispValueToLisp val
  = L.List [L.Symbol "value"
           ,L.List $ lispSizeToLisp (size val)
           ,lispStructToLisp (value val)]
  where
    lispStructToLisp :: LispStruct (LispVal LispExpr lvl) tp -> L.Lisp
    lispStructToLisp (LSingleton (Val e)) = lispExprToLisp e
    lispStructToLisp (LStruct tps)
      = L.List (L.Symbol "struct":
                lispStructsToLisp tps)
    lispStructsToLisp :: StructArgs (LispVal LispExpr lvl) sig -> [L.Lisp]
    lispStructsToLisp NoSArg = []
    lispStructsToLisp (SArg x xs) = lispStructToLisp x:
                                    lispStructsToLisp xs
    lispSizeToLisp :: Size LispExpr lvl -> [L.Lisp]
    lispSizeToLisp NoSize = []
    lispSizeToLisp (Size x xs) = (lispExprToLisp x):
                                 lispSizeToLisp xs

lispSortToLisp :: (KnownNat lvl,GetStructType tp) =>  e '(lvl,tp) -> L.Lisp
lispSortToLisp (_::e '(lvl,tp)) = case natVal (Proxy::Proxy lvl) of
  0 -> structTypeToLisp (getStructType::LispStruct Repr tp)
  n -> L.List [L.Symbol "array"
              ,L.Number $ fromInteger n
              ,structTypeToLisp (getStructType::LispStruct Repr tp)]
  where
    structTypeToLisp :: LispStruct Repr sig -> L.Lisp
    structTypeToLisp (LSingleton repr) = typeSymbol repr
    structTypeToLisp (LStruct tps)
      = L.List (L.Symbol "struct":structTypesToLisp tps)

    structTypesToLisp :: StructArgs Repr sig -> [L.Lisp]
    structTypesToLisp NoSArg = []
    structTypesToLisp (SArg x xs) = structTypeToLisp x:
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
             Just xs -> case runExcept $ mapM (parseLispExprT state' inp' gts') xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing properties: "++err
           init = case Map.lookup "init" mp of
             Nothing -> DMap.empty
             Just xs -> parseInit state' xs
           invar = case Map.lookup "invariant" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' inp' Map.empty) xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing invariants: "++err
           assume = case Map.lookup "assumption" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' inp' gts') xs of
               Right lst -> lst
               Left err -> error $ "Error while parsing assumptions: "++err
           preds = case Map.lookup "predicate" mp of
             Nothing -> []
             Just xs -> case runExcept $ mapM (parseLispExprT state' Map.empty Map.empty) xs of
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
              -> (forall (lvl::Nat) (tp::Struct Type).
                  (KnownNat lvl,GetStructType tp)
                   => Proxy lvl -> Proxy tp -> a)
              -> a
parseLispType (L.List [L.Symbol "array",
                       L.Number n,
                       tp]) f
  = reifyNat n $
    \prLvl -> parseLispStructType tp $
    \prTp -> f prLvl prTp
parseLispType tp f
  = parseLispStructType tp $
    \prTp -> f (Proxy::Proxy Z) prTp

parseLispStructType :: L.Lisp
                    -> (forall (tp::Struct Type).
                        GetStructType tp => Proxy tp -> a)
                    -> a
parseLispStructType (L.List (L.Symbol "struct":tps)) f
  = parseLispStructTypes tps $
    \(_::Proxy tps) -> f (Proxy::Proxy ('Struct tps))
parseLispStructType tp f = case runExcept $ lispToSort (error $ "Only basic sorts are supported.") tp of
  Right (Sort (_::Proxy tp)) -> f (Proxy::Proxy ('Singleton tp))

parseLispStructTypes :: [L.Lisp]
                     -> (forall (tp::[Struct Type]).
                         GetStructTypes tp => Proxy tp -> a)
                     -> a
parseLispStructTypes [] f = f (Proxy::Proxy '[])
parseLispStructTypes (x:xs) f
  = parseLispStructType x $
    \(_::Proxy tp) -> parseLispStructTypes xs $
      \(_::Proxy tps) -> f (Proxy::Proxy (tp ': tps))

parseVarMap :: [L.Lisp] -> (DMap LispName Annotation,Map T.Text LispSort)
parseVarMap lst
  = (DMap.fromList [ (LispName name :: LispName '(lvl,tp)) :=> (Annotation ann)
                   | (name,LispSort (_::Proxy lvl) (_::Proxy tp),ann) <- lst' ],
     Map.fromList [ (name,srt) | (name,srt,ann) <- lst' ])
  where
    lst' = fmap (\st -> case st of
                          L.List def -> case parseAnnotation def Map.empty of
                            (ann,[L.Symbol name,sort])
                              -> (name,parseLispType sort LispSort,ann)
                ) lst

parseGates :: Map T.Text LispSort -> Map T.Text LispSort -> [L.Lisp]
           -> (DMap LispName (LispVar LispExpr),Map T.Text LispSort)
parseGates st inps lst = (mp1,mp2)
  where
    mp1 = DMap.fromList [ (LispName name :: LispName '(lvl,tp)) :=>
                          (case runExcept $ parseLispVar st inps mp2 def
                                (\e -> case gcast e of
                                   Just e' -> return e'
                                   Nothing -> throwE $ "type error") of
                             Right var -> var
                             Left err -> error $ "Cannot parse gate: "++show name++"; "++show def++" ["++err++"]")
                        | (name,LispSort (_::Proxy lvl) (_::Proxy tp),def) <- lst' ]
    mp2 = Map.fromList [ (name,srt) | (name,srt,_) <- lst' ]
    lst' = fmap parseGate lst
    parseGate (L.List [L.Symbol name,sort,def])
      = (name,parseLispType sort LispSort,def)

parseNexts :: Map T.Text LispSort -> Map T.Text LispSort -> Map T.Text LispSort
           -> [L.Lisp]
           -> DMap LispName (LispVar LispExpr)
parseNexts st inps gts lst = DMap.fromList lst'
  where
    lst' = fmap parseNext lst
    parseNext (L.List [L.Symbol name,def])
      = case Map.lookup name st of
          Just (LispSort (_::Proxy lvl) (_::Proxy tp))
            -> (LispName name :: LispName '(lvl,tp)) :=>
               (case runExcept $ parseLispVar st inps gts def
                     (\e -> case gcast e of
                        Just e' -> return e'
                        Nothing -> throwE $ "type error") of
                  Right res -> res
                  Left err -> error $ "Cannot parse next expression: "++show name++"; "++show def++" ["++err++"]")

parseInit :: Map T.Text LispSort -> [L.Lisp] -> DMap LispName LispInit
parseInit st lst = DMap.fromList lst'
  where
    lst' = fmap parseInit' lst
    parseInit' (L.List [L.Symbol name,def])
      = case Map.lookup name st of
          Just (LispSort plvl@(_::Proxy lvl) ptp@(_::Proxy tp))
            -> (LispName name :: LispName '(lvl,tp)) :=>
               (case runExcept $ parseLispVar Map.empty Map.empty Map.empty def
                     (\e -> case gcast e of
                        Nothing -> throwE "type error"
                        Just e' -> return e') of
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
             -> (forall lvl tp. (KnownNat lvl,GetStructType tp)
                 => LispVar LispExpr '(lvl,tp) -> LispParse a)
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
              (name,cat,LispSort (_::Proxy lvl) (_::Proxy tp)) <- parseLispVarCat state inps gts expr
              f (NamedVar (LispName name :: LispName '(lvl,tp)) cat))
    (\_ -> parseLispValue state inps gts expr $
           \val -> f (LispConstr val))

parseIdx :: LispStruct Repr tps -> [Integer]
         -> (forall tp. (GetType tp) => Repr tp -> LispIndex tps tp -> LispParse a)
         -> LispParse a
parseIdx (LSingleton (r::Repr t) :: LispStruct Repr tps) [] f
  = f r (ValGet::LispIndex tps t)
parseIdx (LStruct args) (i:is) f
  = parseIdx' args i $
    \prI sub -> parseIdx sub is $
                \r idx -> f r (ValIdx prI idx)
  where
    parseIdx' :: StructArgs Repr tps -> Integer
              -> (forall n. (KnownNat n,IndexableStruct tps n)
                  => Proxy n -> LispStruct Repr (Idx tps n) -> LispParse a)
              -> LispParse a
    parseIdx' (SArg x xs) 0 f
      = f (Proxy::Proxy Z) x
    parseIdx' (SArg x xs) n f
      = parseIdx' xs (n-1) $
        \(_::Proxy n) obj -> f (Proxy::Proxy (S n)) obj


parseDynIdx :: (KnownNat lvl,GetType tp)
            => Proxy tp -> Proxy lvl -> Repr (LispType lvl tp) -> [LispExpr IntType]
            -> (forall rlvl. (KnownNat rlvl,GetType (LispType rlvl tp))
                => LispArrayIndex LispExpr lvl rlvl tp -> LispParse a)
            -> LispParse a
parseDynIdx _ pr _ [] f = case natPred pr of
  NoPred -> f ArrGet
parseDynIdx p lvl (ArrayRepr (Arg IntRepr NoArg) repr) (i:is) f
  = case natPred lvl of
      Pred pr -> parseDynIdx p pr repr is $
                 \idx -> f (ArrIdx i idx)

parseLispExprT :: GetType t
               => Map T.Text LispSort -- ^ State vars
               -> Map T.Text LispSort -- ^ Input vars
               -> Map T.Text LispSort -- ^ Gate vars
               -> L.Lisp
               -> LispParse (LispExpr t)
parseLispExprT state inps gates expr
  = with $ \pr -> parseLispExpr state inps gates (Just $ Sort pr) expr
                  (\e -> case gcast e of
                     Just e' -> return e'
                     Nothing -> throwE $ "Type error in expression "++show e)
  where
    with :: (Proxy t -> LispParse (LispExpr t))
         -> LispParse (LispExpr t)
    with f = f Proxy

deriveLispBaseType :: (KnownNat lvl,GetType rtp) => Proxy lvl -> Repr rtp
                   -> (forall tp. GetType tp
                       => Repr tp -> Dict (rtp ~ LispType lvl tp)
                       -> LispParse a)
                   -> LispParse a
deriveLispBaseType lvl tp f = case natPred lvl of
  NoPred -> f tp Dict
  Pred n -> case tp of
    ArrayRepr (Arg IntRepr NoArg) r
      -> deriveLispBaseType n r $
         \r' Dict -> f r' Dict
    _ -> throwE $ "Should be an array"

parseLispExpr :: Map T.Text LispSort -- ^ State vars
              -> Map T.Text LispSort -- ^ Input vars
              -> Map T.Text LispSort -- ^ Gate vars
              -> Maybe Sort
              -> L.Lisp
              -> (forall t. GetType t => LispExpr t -> LispParse a)
              -> LispParse a
parseLispExpr state inps gates srt (L.List ((L.Symbol "exactly-one"):xs)) f = do
  xs' <- mapM (parseLispExprT state inps gates) xs
  f (ExactlyOne xs')
parseLispExpr state inps gates srt (L.List ((L.Symbol "at-most-one"):xs)) f = do
  xs' <- mapM (parseLispExprT state inps gates) xs
  f (AtMostOne xs')
parseLispExpr state inps gts _ (L.List (L.List (L.Symbol "_":L.Symbol "select":stat):
                                        expr:dyns)) f = do
  idxs <- case mapM (L.parseMaybe L.parseLisp) stat of
    Nothing -> throwE $ "Can not parse static indices: "++show stat
    Just r -> return r
  dyns' <- mapM (parseLispExprT state inps gts) dyns
  parseLispVar state inps gts expr $
    \(var::LispVar LispExpr '(lvl,tp)) -> parseIdx (getStructType::LispStruct Repr tp) idxs $
    \repr (idx::LispIndex tp tp')
      -> case deriveLispTypeCtx (Proxy::Proxy lvl) (Proxy::Proxy tp') of
           Dict -> parseDynIdx (Proxy::Proxy tp') (Proxy::Proxy lvl)
                     (getType::Repr (LispType lvl tp')) dyns' $
                       \dyn -> f (LispRef var idx dyn)
parseLispExpr state inps gts _ (L.List [L.List [L.Symbol "_",
                                                L.Symbol "eq"],
                                        var1,var2]) f
  = parseLispVar state inps gts var1 $
    \var1' -> do
       var2' <- parseLispVar state inps gts var2
                (\e -> case gcast e of
                   Just e' -> return e'
                   Nothing -> throwE "type error")
       f (LispEq var1' var2')
parseLispExpr state inps gates srt expr f
  = catchE (do
               (name,cat,LispSort prLvl@(_::Proxy lvl) (_::Proxy tp))
                  <- parseLispVarCat state inps gates expr
               case getStructType :: LispStruct Repr tp of
                 LSingleton (_::Repr tp') -> case deriveLispTypeCtx prLvl (Proxy::Proxy tp') of
                   Dict -> f (LispRef (NamedVar (LispName name :: LispName '(lvl,tp)) cat)
                                       (ValGet::LispIndex tp tp')
                                       (ArrGet::LispArrayIndex LispExpr lvl lvl tp'))
                 _ -> throwE $ "Variable is not a singleton")
    (\_ -> lispToExprWith parser srt expr (f . LispExpr))
  where
    parser = LispParser { parseFunction = \_ _ _ _ _ _ -> throwE $ "Invalid function"
                        , parseDatatype = \_ _ -> throwE $ "Invalid datatype"
                        , parseVar = \_ _ _ _ _ -> throwE $ "Invalid variable"
                        , parseRecursive = parseLispExpr state inps gates
                        , registerQVar = \_ _ -> (NoRef,parser)
                        , registerLetVar = \_ _ -> (NoRef,parser) }

parseSize :: Map T.Text LispSort -- ^ State vars
          -> Map T.Text LispSort -- ^ Input vars
          -> Map T.Text LispSort -- ^ Gate vars
          -> [L.Lisp]
          -> (forall lvl. (KnownNat lvl,GetType (LispType lvl IntType)) => Size LispExpr lvl -> LispParse a)
          -> LispParse a
parseSize st inps gts [] f = f NoSize
parseSize st inps gts (x:xs) f
  = parseSize st inps gts xs $
    \szs -> do
       sz <- parseLispExprT st inps gts x
       f (Size sz szs)

parseLispValue :: Map T.Text LispSort -- ^ State vars
               -> Map T.Text LispSort -- ^ Input vars
               -> Map T.Text LispSort -- ^ Gate vars
               -> L.Lisp
               -> (forall lvl tp. (KnownNat lvl,GetStructType tp)
                   => LispValue '(lvl,tp) LispExpr -> LispParse a)
               -> LispParse a
parseLispValue state inps gates
  (L.List [L.Symbol "value"
          ,L.List sizes
          ,struct]) f = parseSize state inps gates sizes $
  \(sz::Size LispExpr lvl)
   -> parseStruct (Proxy::Proxy lvl) struct $
      \str -> f $ LispValue sz str
  where
    parseStruct :: KnownNat lvl
                => Proxy lvl
                -> L.Lisp
                -> (forall tp. GetStructType tp
                    => LispStruct (LispVal LispExpr lvl) tp -> LispParse a)
                -> LispParse a
    parseStruct lvl (L.List (L.Symbol "struct":xs)) f
      = parseStructs lvl xs $
        \xs' -> f (LStruct xs')
    parseStruct lvl expr f
      = parseVal lvl expr $
        \e -> f (LSingleton e)

    parseStructs :: KnownNat lvl
                 => Proxy lvl
                 -> [L.Lisp]
                 -> (forall tp. GetStructTypes tp
                     => StructArgs (LispVal LispExpr lvl) tp -> LispParse a)
                 -> LispParse a
    parseStructs lvl [] f = f NoSArg
    parseStructs lvl (x:xs) f
      = parseStruct lvl x $
        \x' -> parseStructs lvl xs $
        \xs' -> f (SArg x' xs')

    parseVal :: KnownNat lvl
             => Proxy lvl
             -> L.Lisp
             -> (forall tp. GetType tp
                 => LispVal LispExpr lvl tp -> LispParse a)
             -> LispParse a
    parseVal (lvl::Proxy lvl) lsp f
      = parseLispExpr state inps gates Nothing lsp $
        \e -> deriveLispBaseType lvl (getTypeOf e) $
        \(_::Repr tp) d -> case d of
           Dict -> f (Val e::LispVal LispExpr lvl tp)
parseLispValue state inps gates expr f
  = parseLispExpr state inps gates Nothing expr $
    \e -> f (LispValue NoSize (LSingleton (Val e)))

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

newtype LispState e = LispState (DMap LispName (LispValue' e))

data LispRev tp where
  LispRev :: LispName '(lvl,tps)
          -> RevValue '(lvl,tps) tp
          -> LispRev tp

deriving instance Show (LispRev tp)

instance GShow LispRev where
  gshowsPrec = showsPrec

instance TransitionRelation LispProgram where
  type State LispProgram = LispState 
  type Input LispProgram = LispState
  type RealizationProgress LispProgram = LispState
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
                  | (name@(LispName _) :=> LispInit val) <- DMap.toList (programInit prog) ] of
        [] -> LispExpr (Const (BoolValue True))
        [e] -> e
        xs -> allEqFromList xs (\arg -> LispExpr (App (Logic And) arg))
  stateInvariant prog st inp = do
    invars <- mapM (relativize st inp
                    (error "Realization.Lisp: invariant references gates.")
                   ) (programInvariant prog)
    case invars of
      [] -> [expr| true |]
      [x] -> return x
      xs -> [expr| (and # xs) |]
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
                   (mapM (\(name@(LispName name') :=> var) -> do
                            nvar <- relativizeVar st inp
                                      (declareGate mkGate prog st inp) var >>=
                                      defineGate (\n e -> lift $ mkGate n e) (T.unpack name')
                            return $ name :=> (LispValue' nvar)
                         ) lst) gts
    return (LispState $ DMap.fromAscList nlst,ngts)

declareGate :: (Embed m e)
            => (forall t. GetType t => Maybe String -> e t -> m (e t))
            -> LispProgram -> LispState e -> LispState e
            -> LispName '(lvl,tp)
            -> StateT (LispState e) m (LispValue '(lvl,tp) e)
declareGate mkGate prog st inp name@(LispName name') = do
  LispState mp <- get
  case DMap.lookup name mp of
    Just (LispValue' r) -> return r
    Nothing -> case DMap.lookup name (programGates prog) of
      Just var -> do
        val <- relativizeVar st inp (declareGate mkGate prog st inp) var
        gt <- lift $ defineGate mkGate (T.unpack name') val
        LispState mp' <- get
        put $ LispState $ DMap.insert name (LispValue' gt) mp'
        return gt

defineGate :: Monad m
           => (forall t. GetType t => Maybe String -> e t -> m (e t))
           -> String -> LispValue '(lvl,tp) e
           -> m (LispValue '(lvl,tp) e)
defineGate mkGate name val = do
  sz <- defineSize mkGate name (size val)
  v <- mapLispStructM (\_ (Val e) -> do
                         e' <- mkGate (Just name) e
                         return (Val e')
                      ) (value val)
  return (LispValue sz v)
  where
    defineSize :: Monad m
               => (forall t. GetType t => Maybe String -> e t -> m (e t))
               -> String -> Size e lvl' -> m (Size e lvl')
    defineSize _ _ NoSize = return NoSize
    defineSize mkGate name (Size i is) = do
      i' <- mkGate (Just name) i
      is' <- defineSize mkGate name is
      return (Size i' is')

relativize :: (Embed m e,GetType t)
           => LispState e
           -> LispState e
           -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
           -> LispExpr t
           -> m (e t)
relativize st inp gts (LispExpr e) = do
  e' <- mapExpr err err err err err err
        (relativize st inp gts) e
  embed e'
  where
    err = error "Realization.Lisp.relativize: LispExpr shouldn't have any user defined entities."
relativize st inp gts (LispRef var stat dyn) = do
  val <- relativizeVar st inp gts var
  dyn' <- relativizeIndex st inp gts dyn
  (Val res,_) <- accessVal stat (value val) $
                 \val' -> accessArray dyn' val' $
                    \val'' -> return (val'',val'')
  return res
relativize st inp gts (LispEq v1 v2) = do
  val1 <- relativizeVar st inp gts v1
  val2 <- relativizeVar st inp gts v2
  c1 <- eqSize (size val1) (size val2)
  c2 <- eqVal (value val1) (value val2)
  case c1++c2 of
    [] -> embedConst $ BoolValueC True
    [x] -> return x
    xs -> [expr| (and # xs) |]
  where
    eqSize :: Embed m e
           => Size e sig -> Size e sig
           -> m [e BoolType]
    eqSize NoSize NoSize = return []
    eqSize (Size i is) (Size j js) = do
      c <- [expr| (= i j) |]
      cs <- eqSize is js
      return (c:cs)

    eqVal :: Embed m e
          => LispStruct (LispVal e lvl) tps
          -> LispStruct (LispVal e lvl) tps
          -> m [e BoolType]
    eqVal (LSingleton (Val v1)) (LSingleton (Val v2)) = do
      c <- [expr| (= v1 v2) |]
      return [c]
    eqVal (LStruct xs) (LStruct ys) = eqVal' xs ys

    eqVal' :: Embed m e
           => StructArgs (LispVal e lvl) tps
           -> StructArgs (LispVal e lvl) tps
           -> m [e BoolType]
    eqVal' NoSArg NoSArg = return []
    eqVal' (SArg x xs) (SArg y ys) = do
      c1 <- eqVal x y
      c2 <- eqVal' xs ys
      return $ c1++c2
relativize st inp gts (ExactlyOne es) = do
  es' <- mapM (relativize st inp gts) es
  oneOf es'
relativize st inp gts (AtMostOne es) = do
  es' <- mapM (relativize st inp gts) es
  atMostOneOf es'
relativize st inp gts e = error $ "Realization.Lisp.relativize: Cannot relativize: "++show e

oneOf :: Embed m e
      => [e BoolType] -> m (e BoolType)
oneOf [] = [expr| true |]
oneOf [x] = return x
oneOf xs = do
  disj <- oneOf' [] xs
  [expr| (or # disj) |]
  where
    oneOf' :: Embed m e
           => [e BoolType] -> [e BoolType] -> m [e BoolType]
    oneOf' _ [] = return []
    oneOf' xs (y:ys) = do
      negs <- mapM (\e -> [expr| (not e) |]) (xs++ys)
      conj <- let arg = y:negs
              in [expr| (and # arg) |]
      rest <- oneOf' (y:xs) ys
      return (conj:rest)

atMostOneOf :: Embed m e
            => [e BoolType] -> m (e BoolType)
atMostOneOf [] = [expr| true |]
atMostOneOf [x] = [expr| true |]
atMostOneOf xs = do
  disj <- oneOf' [] xs
  [expr| (or # disj) |]
  where
    oneOf' :: Embed m e
           => [e BoolType] -> [e BoolType] -> m [e BoolType]
    oneOf' xs [] = do
      negs <- mapM (\e -> [expr| (not e) |]) xs
      conj <- [expr| (and # negs) |]
      return [conj]
    oneOf' xs (y:ys) = do
      negs <- mapM (\e -> [expr| (not e) |]) (xs++ys)
      conj <- [expr| (and # negs) |]
      rest <- oneOf' (y:xs) ys
      return (conj:rest)

relativizeVar :: (Embed m e)
              => LispState e
              -> LispState e
              -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
              -> LispVar LispExpr sig
              -> m (LispValue sig e)
relativizeVar (LispState st) (LispState inp) gts (NamedVar name@(LispName _) cat)
  = case cat of
      Input -> case DMap.lookup name inp of
        Just (LispValue' r) -> return r
      State -> case DMap.lookup name st of
        Just (LispValue' r) -> return r
      Gate -> gts name
relativizeVar st inp gts (LispConstr val) = do
  sz <- relativizeSize st inp gts (size val)
  val <- mapLispStructM (\_ (Val e) -> fmap Val (relativize st inp gts e)
                        ) (value val)
  return $ LispValue sz val
  where
    relativizeSize :: (Embed m e)
                   => LispState e -> LispState e
                   -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
                   -> Size LispExpr lvl
                   -> m (Size e lvl)
    relativizeSize _ _ _ NoSize = return NoSize
    relativizeSize st inp gts (Size i is) = do
      i' <- relativize st inp gts i
      is' <- relativizeSize st inp gts is
      return $ Size i' is'

relativizeIndex :: (Embed m e)
                => LispState e
                -> LispState e
                -> (forall lvl tp. LispName '(lvl,tp) -> m (LispValue '(lvl,tp) e))
                -> LispArrayIndex LispExpr lvl rlvl tp
                -> m (LispArrayIndex e lvl rlvl tp)
relativizeIndex st inp gts ArrGet = return ArrGet
relativizeIndex st inp gts (ArrIdx i is) = do
  i' <- relativize st inp gts i
  is' <- relativizeIndex st inp gts is
  return (ArrIdx i' is')

instance Composite LispState where
  type CompDescr LispState = DMap LispName Annotation
  type RevComp LispState = LispRev
  foldExprs f (LispState mp) = do
    let lst = DMap.toAscList mp
    nlst <- mapM (\(name@(LispName _) :=> (LispValue' val)) -> do
                    nval <- foldExprs f val
                    return (name :=> (LispValue' nval))
                 ) lst
    return $ LispState $ DMap.fromAscList nlst
  createComposite mkVar ann = do
    lst' <- mapM (\(name@(LispName _) :=> _) -> do
                    res <- createComposite (\rev -> mkVar (LispRev name rev)) ()
                    return $ name :=> (LispValue' res)
                 ) lst
    return $ LispState (DMap.fromAscList lst')
    where
      lst = DMap.toAscList ann
  eqComposite (LispState mp1) (LispState mp2) = do
    eqs <- sequence [ eqComposite v1 v2
                    | (name@(LispName _) :=> (LispValue' v1)) <- DMap.toList mp1
                    , let LispValue' v2 = mp2 DMap.! name ]
    [expr| (and # eqs) |]

newtype LispConcr = LispConcr (DMap LispName LispUVal)

instance Show LispConcr where
  showsPrec p (LispConcr mp) = showsPrec p (DMap.toList mp)

instance LiftComp LispState where
  type Unpacked LispState = LispConcr
  liftComp (LispConcr mp) = do
    let lst = DMap.toAscList mp
    nlst <- mapM (\(name@(LispName _) :=> val) -> do
                    nval <- liftComp val
                    return (name :=> (LispValue' nval))
                 ) lst
    return $ LispState $ DMap.fromAscList nlst
  unliftComp f (LispState mp) = do
    let lst = DMap.toAscList mp
    nlst <- mapM (\(name@(LispName _) :=> (LispValue' val)) -> do
                    nval <- unliftComp f val
                    return (name :=> nval)
                 ) lst
    return $ LispConcr $ DMap.fromAscList nlst

newtype LispPVal' sig = LispPVal' (LispPVal sig) deriving Typeable

newtype LispPart = LispPart (DMap LispName LispPVal')

instance PartialComp LispState where
  type Partial LispState = LispPart
  maskValue _ (LispPart mp) xs
    = let (res,nmp) = DMap.mapAccumLWithKey
                      (\xs (LispName _) (LispPVal' p::LispPVal' '(lvl,tp))
                       -> let (np,nxs) = maskValue (Proxy::Proxy (LispValue '(lvl,tp)))
                                         p xs
                          in (nxs,LispPVal' np)
                      ) xs mp
      in (LispPart nmp,res)
  unmaskValue _ (LispConcr cmp)
    = let lst = DMap.toAscList cmp
          nlst = fmap (\(name@(LispName _)
                          :=> (cval::LispUVal '(lvl,tp)))
                        -> name :=> LispPVal'
                           (unmaskValue (Proxy::Proxy (LispValue '(lvl,tp))) cval)
                      ) lst
      in LispPart $ DMap.fromAscList nlst
  assignPartial f (LispState mp1) (LispPart mp2) = do
    let lst1 = DMap.toAscList mp1
    mkPartial lst1
    where
      mkPartial [] = return []
      mkPartial ((name@(LispName _) :=> LispValue' var):xs)
        = case DMap.lookup name mp2 of
            Just (LispPVal' val) -> do
              r1 <- assignPartial f var val
              r2 <- mkPartial xs
              return (r1++r2)

instance GEq LispRev where
  geq (LispRev name1 val1) (LispRev name2 val2) = do
    Refl <- geq name1 name2
    Refl <- geq val1 val2
    return Refl

instance GCompare LispRev where
  gcompare (LispRev name1 val1) (LispRev name2 val2)
    = case gcompare name1 name2 of
    GEQ -> gcompare val1 val2
    GLT -> GLT
    GGT -> GGT

{-import Data.Map (Map)
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
-}
