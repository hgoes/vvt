{-# LANGUAGE RankNTypes,TypeFamilies,MultiParamTypeClasses,FlexibleContexts,
             FlexibleInstances,ScopedTypeVariables,GADTs,DeriveDataTypeable,
             DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
module Realization.Lisp.Value where

import Args
import PartialArgs

import Language.SMTLib2.Internals.TH
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Expression

import Data.List (genericIndex,genericLength,genericReplicate)
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Data.Constraint
import Prelude hiding (mapM,foldl,and,concat)
import Data.Proxy
import Data.GADT.Compare
import Data.GADT.Show
import Control.Monad.Identity
import Text.Show

import Debug.Trace

data Struct a = Singleton a
              | Struct [Struct a]
              deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

type family LispType (lvl :: Nat) (t :: Type) :: Type where
  LispType Z t = t
  LispType (S n) t = ArrayType '[IntType] (LispType n t)

type family IdxStruct (tps :: [Struct Type]) (idx :: Nat) :: Struct Type where
  IdxStruct (tp ': tps) Z = tp
  IdxStruct (tp ': tps) (S n) = IdxStruct tps n

lispTypeGetType :: Natural lvl -> Repr tp -> Repr (LispType lvl tp)
lispTypeGetType Zero tp = tp
lispTypeGetType (Succ n) tp = ArrayRepr (Arg IntRepr NoArg)
                              (lispTypeGetType n tp)

lispTypeType :: Natural lvl -> Repr (LispType lvl tp) -> Repr tp
lispTypeType Zero tp = tp
lispTypeType (Succ n) (ArrayRepr _ tp) = lispTypeType n tp

accessStruct :: Monad m
             => StructArgs st tps
             -> Natural idx
             -> (LispStruct st (IdxStruct tps idx)
                 -> m (a,LispStruct st (IdxStruct tps idx)))
               -> m (a,StructArgs st tps)
accessStruct (SArg x xs) Zero f = do
  (res,nx) <- f x
  return (res,SArg nx xs)
accessStruct (SArg x xs) (Succ n) f = do
  (res,nxs) <- accessStruct xs n f
  return (res,SArg x nxs)

data Size (e::Type -> *) (lvl :: Nat) where
  NoSize :: Size e Z
  Size :: e (LispType n IntType) -> Size e n -> Size e (S n)

sizeLevel :: Size e lvl -> Natural lvl
sizeLevel NoSize = Zero
sizeLevel (Size _ sz) = Succ (sizeLevel sz)

data StructArgs e (sig :: [Struct Type]) where
  NoSArg :: StructArgs e '[]
  SArg :: LispStruct e tp
       -> StructArgs e tps
       -> StructArgs e (tp ': tps)

data LispStruct e (tp :: Struct Type) where
  LSingleton :: e t -> LispStruct e (Singleton t)
  LStruct :: StructArgs e sig -> LispStruct e ('Struct sig)

instance GShow e => Show (LispStruct e tp) where
  showsPrec p (LSingleton x) = gshowsPrec p x
  showsPrec p (LStruct xs) = showChar '{' .
                             showSArg xs .
                             showChar '}'
    where
      showSArg :: GShow e => StructArgs e sig -> ShowS
      showSArg NoSArg = id
      showSArg (SArg x NoSArg) = gshowsPrec 0 x
      showSArg (SArg x xs) = gshowsPrec 0 x .
                             showString ", " .
                             showSArg xs

data LispValue (sig :: (Nat,Struct Type)) (e::Type -> *)
  = LispValue { size :: Size e (Fst sig)
              , value :: LispStruct (LispVal e (Fst sig)) (Snd sig) }

lispValueType :: GetType e => LispValue '(lvl,tps) e -> (Natural lvl,LispStruct Repr tps)
lispValueType val = (lvl,
                     mapLispStruct (\(Val e) -> lispTypeType lvl (getType e)) (value val))
  where
    lvl = sizeLevel (size val)

data LispUVal (sig :: (Nat,Struct Type)) where
  LispU :: !(LispStruct ConcreteValue tps) -> LispUVal '(Z,tps)
  LispUArray :: Natural n -> LispStruct Repr tps -> [LispUVal '(n,tps)] -> LispUVal '(S n,tps)

instance GEq LispUVal where
  geq (LispU x) (LispU y) = do
    Refl <- geq x y
    return Refl
  geq (LispUArray nx tpx x) (LispUArray ny tpy y) = do
    Refl <- geq nx ny
    Refl <- geq tpx tpy
    if x==y
      then return Refl
      else Nothing
  geq _ _ = Nothing

deriving instance Eq (LispUVal sig)
deriving instance Ord (LispUVal sig)

instance Show (LispUVal sig) where
  showsPrec p (LispU x) = showsPrec p x
  showsPrec p (LispUArray _ _ arr) = showListWith (showsPrec 0) arr

data LispPVal (sig :: (Nat,Struct Type)) where
  LispP :: !(LispStruct PValue tps) -> LispPVal '(Z,tps)
  LispPArray :: !([LispPVal '(n,tps)]) -> LispPVal '(S n,tps)

deriving instance Eq (LispPVal sig)
deriving instance Ord (LispPVal sig)
instance Show (LispPVal sig) where
  showsPrec p (LispP struct) = showsPrec p struct
  showsPrec p (LispPArray arr) = showsPrec p arr

data LispVal e lvl tp where
  Val :: e (LispType n tp) -> LispVal e n tp

--instance GetType e => GetType (LispVal e lvl) where
--  getType e = 

data LispArrayIndex e (lvl::Nat) (rlvl::Nat) (tp::Type) where
  ArrGet :: Natural lvl -> Repr tp -> LispArrayIndex e lvl lvl tp
  ArrIdx :: e IntType
         -> LispArrayIndex e lvl n tp
         -> LispArrayIndex e (S lvl) n tp

lispArrayIndexLevel :: LispArrayIndex e lvl rlvl tp -> Natural rlvl
lispArrayIndexLevel (ArrGet l _) = l
lispArrayIndexLevel (ArrIdx _ idx) = lispArrayIndexLevel idx

data LispIndex (tp :: Struct Type) (res :: Type) where
  ValGet :: Repr tp -> LispIndex (Singleton tp) tp
  ValIdx :: Natural n
         -> LispIndex (IdxStruct tps n) res
         -> LispIndex ('Struct tps) res

lispIndexType :: LispIndex tps tp -> Repr tp
lispIndexType (ValGet tp) = tp
lispIndexType (ValIdx _ idx) = lispIndexType idx

instance GShow e => GShow (LispStruct e) where
  gshowsPrec = showsPrec

instance GShow e => Show (LispVal e lvl tp) where
  showsPrec p (Val e) = showParen (p>10) $
                        showString "Val " .
                        gshowsPrec 11 e

instance GShow e => GShow (LispVal e lvl) where
  gshowsPrec = showsPrec

getIndex :: (Embed m e,GetType e) => LispArrayIndex e lvl rlvl tp
         -> LispVal e lvl tp
         -> m (LispVal e rlvl tp)
getIndex (ArrGet _ _) (Val val) = return (Val val)
getIndex (ArrIdx i is) (Val val) = do
  e <- [expr| (select val i) |]
  getIndex is (Val e)

accessVal :: Monad m
          => LispIndex tp res
          -> LispStruct (LispVal e lvl) tp
          -> (LispVal e lvl res -> m (a,LispVal e lvl res))
          -> m (a,LispStruct (LispVal e lvl) tp)
accessVal (ValGet _) (LSingleton val) f = do
  (res,nval) <- f val
  return (res,LSingleton nval)
accessVal (ValIdx pr is) (LStruct tps) f = do
  (res,ntps) <- accessStruct tps pr (\tp -> accessVal is tp f)
  return (res,LStruct ntps)

accessArray :: (Embed m e,GetType e)
            => LispArrayIndex e lvl rlvl tp
            -> LispVal e lvl tp
            -> (LispVal e rlvl tp -> m (a,LispVal e rlvl tp))
            -> m (a,LispVal e lvl tp)
accessArray (ArrGet _ _) el f = f el
accessArray (ArrIdx i is) (Val arr) f = do
  el <- [expr| (select arr i) |]
  (res,nel) <- accessArray is (Val el) f
  narr <- case nel of
    Val el' -> [expr| (store arr el' i) |]
  return (res,Val narr)

instance GEq e => GEq (LispStruct e) where
  geq (LSingleton x1) (LSingleton x2) = do
    Refl <- geq x1 x2
    return Refl
  geq (LStruct args1) (LStruct args2) = do
    Refl <- geq args1 args2
    return Refl
  geq _ _ = Nothing

instance GEq e => GEq (StructArgs e) where
  geq NoSArg NoSArg = return Refl
  geq (SArg x xs) (SArg y ys) = do
    Refl <- geq x y
    Refl <- geq xs ys
    return Refl
  geq _ _ = Nothing

instance GCompare e => GCompare (LispStruct e) where
  gcompare (LSingleton x1) (LSingleton x2) = case gcompare x1 x2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (LSingleton _) _ = GLT
  gcompare _ (LSingleton _) = GGT
  gcompare (LStruct args1) (LStruct args2) = case gcompare args1 args2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance GCompare e => Eq (LispStruct e sig) where
  (==) = defaultEq
instance GCompare e => Ord (LispStruct e sig) where
  compare = defaultCompare

instance GCompare e => GCompare (StructArgs e) where
  gcompare NoSArg NoSArg = GEQ
  gcompare NoSArg _ = GLT
  gcompare _ NoSArg = GGT
  gcompare (SArg x xs) (SArg y ys) = case gcompare x y of
    GEQ -> case gcompare xs ys of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

data RevValue sig t where
  RevVar :: Natural lvl -> LispIndex tps tp -> RevValue '(lvl,tps) (LispType lvl tp)
  RevSize :: Natural lvl -> Natural rlvl
          -> RevValue '(S lvl,tps) (LispType rlvl IntType)

instance GEq (LispIndex tps) where
  geq (ValGet tp1) (ValGet tp2) = do
    Refl <- geq tp1 tp2
    return Refl
  geq (ValIdx n1 i1) (ValIdx n2 i2) = do
    Refl <- geq n1 n2
    Refl <- geq i1 i2
    return Refl
  geq _ _ = Nothing

-- Don't inline compareLispIndex here or the instance becomes incoherent (Don't ask me...)
instance GCompare (LispIndex tps) where
  gcompare = compareLispIndex

instance Show (LispIndex tps tp) where
  showsPrec p (ValGet _) = showString "ValGet"
  showsPrec p (ValIdx n idx) = showParen (p>10) $
                               showString "ValIdx " .
                               showsPrec 11 (naturalToInteger n) .
                               showChar ' ' .
                               showsPrec 11 idx

instance GShow (LispIndex idx) where
  gshowsPrec = showsPrec

compareLispIndex :: LispIndex tps t1 -> LispIndex tps t2 -> GOrdering t1 t2
compareLispIndex (ValGet tp1) (ValGet tp2) = case gcompare tp1 tp2 of
  GEQ -> GEQ
  GLT -> GLT
  GGT -> GGT
compareLispIndex (ValGet _) _ = GLT
compareLispIndex _ (ValGet _) = GGT
compareLispIndex (ValIdx n1 i1) (ValIdx n2 i2)
  = case gcompare n1 n2 of
  GEQ -> case compareLispIndex i1 i2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  GLT -> GLT
  GGT -> GGT

instance GEq (RevValue sig) where
  geq (RevVar lvl1 i1) (RevVar lvl2 i2) = do
    Refl <- geq lvl1 lvl2
    Refl <- geq i1 i2
    return Refl
  geq (RevSize lvl1 rlvl1) (RevSize lvl2 rlvl2) = do
    Refl <- geq lvl1 lvl2
    Refl <- geq rlvl1 rlvl2
    return Refl
  geq _ _ = Nothing

instance GCompare (RevValue sig) where
  gcompare (RevVar lvl1 i1) (RevVar lvl2 i2) = case gcompare lvl1 lvl2 of
    GEQ -> case gcompare i1 i2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (RevVar _ _) _ = GLT
  gcompare _ (RevVar _ _) = GGT
  gcompare (RevSize lvl1 rlvl1) (RevSize lvl2 rlvl2) = case gcompare lvl1 lvl2 of
    GEQ -> case gcompare rlvl1 rlvl2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance Show (RevValue sig t) where
  showsPrec p (RevVar _ idx) = showParen (p>10) $
                               showString "RevVar " .
                               showsPrec 11 idx
  showsPrec p (RevSize lvl _) = showParen (p>10) $
                                showString "RevSize " .
                                showsPrec 11 (naturalToInteger lvl)

instance GShow (RevValue sig) where
  gshowsPrec = showsPrec

instance Composite (LispValue '(lvl,tps)) where
  type CompDescr (LispValue '(lvl,tps)) = (Natural lvl,LispStruct Repr tps)
  type RevComp (LispValue '(lvl,tps)) = RevValue '(lvl,tps)
  foldExprs f val = do
    sz' <- foldSize f (size val)
    val' <- mapLispStructM (\(Val e) -> fmap Val (f e)) (value val)
    return $ LispValue sz' val'
    where
      foldSize :: Monad m => (forall t. e t -> m (e' t))
               -> Size e lvl'
               -> m (Size e' lvl')
      foldSize f NoSize = return NoSize
      foldSize f (Size sz szs) = do
        nsz <- f sz
        nszs <- foldSize f szs
        return $ Size nsz nszs
  createComposite f (lvl,tp) = do
    sz <- case lvl of
      Zero -> return NoSize
      Succ lvl' -> createSize lvl' f Zero NoSize
    val <- createStruct f lvl tp
    return (LispValue sz val)
    where
      createSize :: (Monad m)
                 => Natural lvl'
                 -> (forall t. RevValue '(S lvl',tp) t -> m (e t))
                 -> Natural lvl''
                 -> Size e lvl''
                 -> m (Size e (S lvl'))
      createSize lvl f lvl' szs = case geq (Succ lvl) lvl' of
        Nothing -> do
          sz <- f (RevSize lvl lvl')
          createSize lvl f (Succ lvl') (Size sz szs)
        Just Refl -> return szs

      createStruct :: Monad m => (forall t. RevValue '(lvl,tps) t -> m (e t))
                   -> Natural lvl
                   -> LispStruct Repr tps
                   -> m (LispStruct (LispVal e lvl) tps)
      createStruct f lvl = mapLispStructIdxM
                           (\idx tp -> do
                               e <- f (RevVar lvl idx)
                               return (Val e))
  accessComposite (RevVar lvl idx) val
    = fst $ runIdentity $ accessVal idx (value val) $
      \v@(Val e) -> return (e,v)
  accessComposite (RevSize lvl idx) val = getSize idx lvl (size val)
    where
      getSize :: Natural rlvl -> Natural lvl' -> Size e (S lvl') -> e (LispType rlvl IntType)
      getSize idx lvl (Size i is)
        = case geq idx lvl of
        Just Refl -> i
        Nothing -> case (lvl,is) of
          (Succ lvl',Size _ _) -> getSize idx lvl' is
  eqComposite v1 v2 = do
    eqS <- eqSize (size v1) (size v2)
    eqV <- eqStruct (value v1) (value v2)
    let eqs = eqS++eqV
    [expr| (and # ${eqs}) |]
    where
      eqSize :: (Embed m e,GetType e) => Size e n -> Size e n -> m [e BoolType]
      eqSize NoSize NoSize = return []
      eqSize (Size x xs) (Size y ys) = do
        eq <- [expr| (= x y) |]
        eqs <- eqSize xs ys
        return (eq:eqs)
      eqStruct :: (Embed m e,GetType e)
               => LispStruct (LispVal e n) tps'
               -> LispStruct (LispVal e n) tps'
               -> m [e BoolType]
      eqStruct (LSingleton (Val x)) (LSingleton (Val y)) = do
        e <- [expr| (= x y) |]
        return [e]
      eqStruct (LStruct xs) (LStruct ys) = eqStructArgs xs ys
      eqStructArgs :: (Embed m e,GetType e)
                   => StructArgs (LispVal e n) tps'
                   -> StructArgs (LispVal e n) tps'
                   -> m [e BoolType]
      eqStructArgs NoSArg NoSArg = return []
      eqStructArgs (SArg x xs) (SArg y ys) = do
        e <- eqStruct x y
        es <- eqStructArgs xs ys
        return (e++es)

instance GetType (RevValue sig) where
  getType (RevVar lvl idx) = lispTypeGetType lvl (lispIndexType idx)

instance LiftComp (LispValue '(lvl,tps)) where
  type Unpacked (LispValue '(lvl,tps)) = LispUVal '(lvl,tps)
  liftComp (LispU str) = do
    str' <- liftStruct str
    return $ LispValue { size = NoSize
                       , value = str' }
  liftComp (LispUArray lvl tps xs) = do
    xs' <- mapM liftComp xs
    liftValues xs'
  unliftComp f val = case sizeLevel $ size val of
    Zero -> do
      str <- extractStruct f (value val)
      return $ LispU str
    Succ lvl -> do
      vals <- unliftValue f val
      vals' <- mapM (unliftComp f) vals
      return $ LispUArray lvl (mapLispStruct (\(Val e) -> lispTypeType (Succ lvl) (getType e)
                                             ) (value val)) vals'

instance PartialComp (LispValue '(lvl,tps)) where
  type Partial (LispValue '(lvl,tps)) = LispPVal '(lvl,tps)
  maskValue _ (LispP str) xs = let (str',xs') = maskStruct str xs
                               in (LispP str',xs')
    where
      maskStruct :: LispStruct PValue tps' -> [Bool] -> (LispStruct PValue tps',[Bool])
      maskStruct (LSingleton (NoPValue tp)) (_:xs) = (LSingleton (NoPValue tp),xs)
      maskStruct (LSingleton (PValue x)) (False:xs) = (LSingleton (NoPValue (valueTypeC x)),xs)
      maskStruct (LSingleton (PValue v)) (True:xs) = (LSingleton (PValue v),xs)
      maskStruct (LStruct str) xs = let (str',xs') = maskStructs str xs
                                    in (LStruct str',xs')
      maskStructs :: StructArgs PValue tps' -> [Bool]
                  -> (StructArgs PValue tps',[Bool])
      maskStructs NoSArg xs = (NoSArg,xs)
      maskStructs (SArg y ys) xs = let (y',xs1) = maskStruct y xs
                                       (ys',xs2) = maskStructs ys xs1
                                   in (SArg y' ys',xs2)
  maskValue pr (LispPArray arr) xs = case pr of
    (_::Proxy (LispValue '(S lvl',tp)))
      -> let (xs',arr') = mapAccumL (\xs e -> let (e',xs') = maskValue (Proxy::Proxy (LispValue '(lvl',tp))) e xs
                                              in (xs',e')
                                    ) xs arr
         in (LispPArray arr',xs')
  unmaskValue _ (LispU xs) = LispP $ mapLispStruct PValue xs
  unmaskValue pr (LispUArray _ _ xs) = case pr of
    (_::Proxy (LispValue '(S lvl',tp)))
      -> LispPArray (fmap (unmaskValue (Proxy::Proxy (LispValue '(lvl',tp)))) xs)
  assignPartial f val (LispP str) = assignStruct f (value val) str
    where
      assignStruct :: Embed m e => (forall t. e t -> ConcreteValue t -> m p)
                   -> LispStruct (LispVal e Z) tps'
                   -> LispStruct PValue tps'
                   -> m [Maybe p]
      assignStruct f (LSingleton (Val x)) (LSingleton (PValue val)) = do
        r <- f x val
        return [Just r]
      assignStruct _ _ (LSingleton (NoPValue _)) = return [Nothing]
      assignStruct f (LStruct xs) (LStruct ys) = assignStructs f xs ys

      assignStructs :: Embed m e => (forall t. e t -> ConcreteValue t -> m p)
                    -> StructArgs (LispVal e Z) tps'
                    -> StructArgs PValue tps'
                    -> m [Maybe p]
      assignStructs _ NoSArg NoSArg = return []
      assignStructs f (SArg x xs) (SArg y ys) = do
        r1 <- assignStruct f x y
        r2 <- assignStructs f xs ys
        return $ r1++r2
  assignPartial f val (LispPArray xs) = do
    lst <- mapM (\(x,n) -> do
                   (asgnSize,nval) <- indexValue f n val
                   rest <- assignPartial f nval x
                   return (Just asgnSize:rest)
                ) (zip xs [0..])
    return $ concat lst

indexValue :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
           -> Integer
           -> LispValue '(S lvl,tps) e
           -> m (p,LispValue '(lvl,tps) e)
indexValue f x val = do
  let idx = IntValueC x
  (res,sz) <- indexSize f idx (size val)
  nval <- indexValue' f idx (value val)
  return (res,LispValue sz nval)
  where
    indexSize :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
              -> ConcreteValue IntType -> Size e (S lvl)
              -> m (p,Size e lvl)
    indexSize f n (Size x NoSize) = do
      res <- f x n
      return (res,NoSize)
    indexSize f n (Size x xs@(Size _ _)) = do
      (res,xs') <- indexSize f n xs
      n' <- embedConst n
      x' <- [expr| (select x n') |]
      return (res,Size x' xs')

    indexValue' :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
                -> ConcreteValue IntType
                -> LispStruct (LispVal e (S lvl)) tps
                -> m (LispStruct (LispVal e lvl) tps)
    indexValue' f n = mapLispStructM
                      (\(Val x)
                       -> do
                            n' <- embedConst n
                            x' <- [expr| (select x n') |]
                            return $ Val x')

extractStruct :: Monad m => (forall t. e t -> m (ConcreteValue t))
              -> LispStruct (LispVal e Z) tps
              -> m (LispStruct ConcreteValue tps)
extractStruct f = mapLispStructM (\(Val x) -> f x)

unliftValue :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
            -> LispValue '(S lvl,tps) e
            -> m [LispValue '(lvl,tps) e]
unliftValue f val = do
  szs <- unliftSize f (size val)
  vals <- unliftStruct f szs (value val)
  return $ zipWith LispValue szs vals

unliftStruct :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
             -> [Size e lvl]
             -> LispStruct (LispVal e (S lvl)) tps
             -> m [LispStruct (LispVal e lvl) tps]
unliftStruct f szs (LSingleton (Val x :: LispVal e (S lvl) tp))
  = mapM (\(idx,sz) -> do
             idx' <- embedConst $ IntValueC idx
             el <- [expr| (select x idx') |]
             return $ LSingleton (Val el)
         ) (zip [0..] szs)
unliftStruct f szs (LStruct vals) = do
  vals' <- unliftStructs f szs vals
  return $ fmap LStruct vals'

unliftStructs :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
              -> [Size e lvl]
              -> StructArgs (LispVal e (S lvl)) tps
              -> m [StructArgs (LispVal e lvl) tps]
unliftStructs f szs NoSArg = return $ fmap (const NoSArg) szs
unliftStructs f szs (SArg x xs) = do
  x' <- unliftStruct f szs x
  xs' <- unliftStructs f szs xs
  return $ zipWith SArg x' xs'

{-deriveLispTypeCtx' :: Proxy lvl -> Proxy t
                   -> Dict (GetType (LispType lvl t))
deriveLispTypeCtx' (_::Proxy lvl) (_::Proxy t)
  = case getType :: Repr (LispType (S lvl) t) of
      ArrayRepr (Arg IntRepr NoArg) repr -> Dict-}

unliftSize :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
           -> Size e (S lvl) -> m [Size e lvl]
unliftSize f (Size x NoSize) = do
  IntValueC val <- f x
  return $ genericReplicate val NoSize
unliftSize f (Size x xs@(Size _ _)) = do
  xs' <- unliftSize f xs
  mapM (\(idx,sz) -> do
           idx' <- embedConst $ IntValueC idx
           el <- [expr| (select x idx') |]
           return (Size el sz)
       ) (zip [0..] xs')

liftValues :: (Embed m e,GetType e) => [LispValue '(lvl,tp) e]
           -> m (LispValue '(S lvl,tp) e)
liftValues xs = do
  sz <- liftSizes (fmap size xs)
  val <- liftStructs (fmap value xs)
  return $ LispValue sz val

liftSizes :: (Embed m e,GetType e) => [Size e lvl] -> m (Size e (S lvl))
liftSizes xs = liftSizes' (genericLength xs) xs

liftSizes' :: (Embed m e,GetType e) => Integer -> [Size e lvl] -> m (Size e (S lvl))
liftSizes' len xs@(x:_) = case x of
  NoSize -> do
    sz <- embedConst (IntValueC len)
    return $ Size sz NoSize
  Size _ szs -> do
    sz <- liftSizeArr (sizeLevel szs) (fmap (\(Size x _) -> x) xs)
    szs <- liftSizes' len (fmap (\(Size _ r) -> r) xs)
    return $ Size sz szs
  where
    liftSizeArr :: (Embed m e,GetType e)
                => Natural n
                -> [e (LispType n IntType)]
                -> m (e (LispType (S n) IntType))
    liftSizeArr lvl lst = do
      c <- embedConst (IntValueC 0)
      arr <- leveledConst lvl c
      listArray arr lst

liftStruct :: (Embed m e,GetType e)
           => LispStruct ConcreteValue tps
           -> m (LispStruct (LispVal e Z) tps)
liftStruct = mapLispStructM (fmap Val . embedConst)

liftStructs :: (Embed m e,GetType e)
            => [LispStruct (LispVal e lvl) tp]
            -> m (LispStruct (LispVal e (S lvl)) tp)
liftStructs xs@(x:_) = case x of
  LSingleton _ -> fmap LSingleton $ liftVal (fmap (\(LSingleton x) -> x) xs)
  LStruct _ -> fmap LStruct (liftStructs' (fmap (\(LStruct x) -> x) xs))
  where
    liftStructs' :: (Embed m e,GetType e)
                 => [StructArgs (LispVal e lvl) tp]
                 -> m (StructArgs (LispVal e (S lvl)) tp)
    liftStructs' (NoSArg:_) = return NoSArg
    liftStructs' xs@(SArg _ _:_) = do
      y <- liftStructs $ fmap (\(SArg x _) -> x) xs
      ys <- liftStructs' $ fmap (\(SArg _ x) -> x) xs
      return $ SArg y ys

liftVal :: (Embed m e,GetType e) => [LispVal e lvl tp] -> m (LispVal e (S lvl) tp)
liftVal xs@(Val x:_) = fmap Val $ listArray' (getType x) (fmap (\(Val x) -> x) xs)

{-deriveLispTypeCtx :: (KnownNat lvl,GetType tp) => Proxy lvl -> Proxy tp
                  -> Dict (GetType (LispType lvl tp))
deriveLispTypeCtx pr repr = case natPred pr of
  NoPred -> Dict
  Pred n -> case deriveLispTypeCtx n repr of
    Dict -> Dict-}

leveledConst :: (Embed m e,GetType e)
             => Natural lvl -> e t -> m (e (LispType lvl t))
leveledConst lvl c = case lvl of
  Zero -> return c
  Succ lvl' -> do
    x <- leveledConst lvl' c
    embed $ App (ConstArray (Arg IntRepr NoArg) (getType x)) (Arg x NoArg)

listArray' :: (Embed m e,GetType e) => Repr t -> [e t] -> m (e (ArrayType '[IntType] t))
listArray' tp xs = do
  c <- embedConst $ defaultValue tp
  listArray c xs
  where
    defaultValue :: Repr t -> ConcreteValue t
    defaultValue tp = case tp of
      BoolRepr -> BoolValueC False
      IntRepr -> IntValueC 0
      RealRepr -> RealValueC 0
      BitVecRepr bw -> BitVecValueC 0 bw

listArray :: (Embed m e,GetType e) => e t -> [e t]
          -> m (e (ArrayType '[IntType] t))
listArray def els = do
  arr <- embed $ App (ConstArray (Arg IntRepr NoArg) (getType def)) (Arg def NoArg)
  (arr',_) <- foldlM (\(arr,n) x -> do
                         i <- embedConst (IntValueC n)
                         arr' <- [expr| (store arr x i) |]
                         return (arr',n+1)
                     ) (arr,0) els
  return arr'

mapLispStruct :: (forall t. e t -> e' t)
              -> LispStruct e tp
              -> LispStruct e' tp
mapLispStruct f = runIdentity . mapLispStructM (\e -> return $ f e)

mapLispStructM :: (Monad m) => (forall t. e t -> m (e' t))
               -> LispStruct e tp
               -> m (LispStruct e' tp)
mapLispStructM f (LSingleton x) = fmap LSingleton (f x)
mapLispStructM f (LStruct xs) = do
  xs' <- mapStructArgsM (\p str -> mapLispStructM f str
                        ) xs
  return (LStruct xs')

mapLispStructIdxM :: (Monad m,GetType e) => (forall t. LispIndex tp t -> e t -> m (e' t))
               -> LispStruct e tp
               -> m (LispStruct e' tp)
mapLispStructIdxM f (LSingleton x) = fmap LSingleton (f (ValGet (getType x)) x)
mapLispStructIdxM f (LStruct xs) = do
  xs' <- mapStructArgsM (\p str -> mapLispStructIdxM (\i e -> f (ValIdx p i) e) str
                        ) xs
  return (LStruct xs')


mapStructArgsM :: Monad m
               => (forall t n. Natural n -> LispStruct e (IdxStruct tps n)
                   -> m (LispStruct e' (IdxStruct tps n)))
               -> StructArgs e tps
               -> m (StructArgs e' tps)
mapStructArgsM f NoSArg = return NoSArg
mapStructArgsM f (SArg x xs) = do
  x' <- f Zero x
  xs' <- mapStructArgsM (\n str -> f (Succ n) str
                        ) xs
  return $ SArg x' xs'

eqArrayIndex :: GEq e
             => LispArrayIndex e lvl rlvl1 tp1
             -> LispArrayIndex e lvl rlvl2 tp2
             -> Maybe (rlvl1 :~: rlvl2,
                       tp1 :~: tp2)
eqArrayIndex (ArrGet n1 tp1) (ArrGet n2 tp2) = do
  Refl <- geq n1 n2
  Refl <- geq tp1 tp2
  return (Refl,Refl)
eqArrayIndex (ArrIdx i1 is1) (ArrIdx i2 is2) = do
  Refl <- geq i1 i2
  (Refl,Refl) <- eqArrayIndex is1 is2
  return (Refl,Refl)
eqArrayIndex _ _ = Nothing
