{-# LANGUAGE RankNTypes,TypeFamilies,MultiParamTypeClasses,FlexibleContexts,
             FlexibleInstances,ScopedTypeVariables,GADTs,DeriveDataTypeable,
             DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
module Realization.Lisp.Value where

import Args
import PartialArgs

import Language.SMTLib2.Internals.TH
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Struct (Tree(..),Struct(..))
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
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

type family LispType (lvl :: Nat) (t :: Type) :: Type where
  LispType Z t = t
  LispType (S n) t = ArrayType '[IntType] (LispType n t)

lispTypeGetType :: Natural lvl -> Repr tp -> Repr (LispType lvl tp)
lispTypeGetType Zero tp = tp
lispTypeGetType (Succ n) tp = ArrayRepr (Cons IntRepr Nil)
                              (lispTypeGetType n tp)

lispTypeType :: Natural lvl -> Repr (LispType lvl tp) -> Repr tp
lispTypeType Zero tp = tp
lispTypeType (Succ n) (ArrayRepr _ tp) = lispTypeType n tp

data Size (e::Type -> *) (lvl :: Nat) where
  NoSize :: Size e Z
  Size :: e (LispType n IntType) -> Size e n -> Size e (S n)

sizeLevel :: Size e lvl -> Natural lvl
sizeLevel NoSize = Zero
sizeLevel (Size _ sz) = Succ (sizeLevel sz)

createSize :: Monad m => (forall n. Natural n -> m (e (LispType n IntType)))
           -> Natural lvl
           -> m (Size e lvl)
createSize f Zero = return NoSize
createSize f (Succ n) = do
  sz <- f n
  szs <- createSize f n
  return (Size sz szs)

createSize' :: forall m lvl e.
               (Monad m)
               => (forall n diff. ((diff + n) ~ lvl)
                   => Natural n -> Natural diff -> m (e (LispType n IntType)))
               -> Natural lvl
               -> m (Size e lvl)
createSize' f lvl = create' lvl Zero
  where
    create' :: ((diff + n) ~ lvl) => Natural n -> Natural diff -> m (Size e n)
    create' Zero _ = return NoSize
    -- TOOOODOOOOOO TODO TODO
    {-create' (Succ n) diff = do
      sz <- f n (Succ diff)
      szs <- create' n (Succ diff)
      return (Size sz szs)-}

accessSize :: (Monad m,(diff + n) ~ lvl) => (e (LispType n IntType) -> m (a,e (LispType n IntType)))
            -> Natural n
            -> Natural diff
            -> Size e lvl
            -> m (a,Size e lvl)
accessSize f _ (Succ Zero) (Size sz szs) = do
  (res,nsz) <- f sz
  return (res,Size nsz szs)
accessSize f n (Succ ndiff) (Size sz szs) = do
  (res,nszs) <- accessSize f n ndiff szs
  return (res,Size sz nszs)

eqValue :: (Embed m e,GetType e)
        => LispValue '(lvl,tps) e
        -> LispValue '(lvl,tps) e
        -> m (e BoolType)
eqValue v1 v2 = do
  conj1 <- eqSize (size v1) (size v2)
  conj2 <- eqVal (value v1) (value v2)
  [expr| (and # ${conj1++conj2}) |]
  where
    eqSize :: (Embed m e,GetType e) => Size e lvl -> Size e lvl -> m [e BoolType]
    eqSize NoSize NoSize = return []
    eqSize (Size x xs) (Size y ys) = do
      c <- [expr| (= x y) |]
      cs <- eqSize xs ys
      return (c:cs)
    eqVal :: (Embed m e,GetType e) => Struct (LispVal e lvl) tps
          -> Struct (LispVal e lvl) tps
          -> m [e BoolType]
    eqVal = Struct.zipFlatten (\(Val x) (Val y) -> do
                                  res <- [expr| (= x y) |]
                                  return [res])
            (return . concat)

data LispValue (sig :: (Nat,Tree Type)) (e::Type -> *)
  = LispValue { size :: Size e (Fst sig)
              , value :: Struct (LispVal e (Fst sig)) (Snd sig) }

lispValueType :: GetType e => LispValue '(lvl,tps) e -> (Natural lvl,Struct Repr tps)
lispValueType val = (lvl,
                     Struct.map (\(Val e) -> lispTypeType lvl (getType e)) (value val))
  where
    lvl = sizeLevel (size val)

data LispUVal (sig :: (Nat,Tree Type)) where
  LispU :: Struct ConcreteValue tps -> LispUVal '(Z,tps)
  LispUArray :: Natural n -> Struct Repr tps -> [LispUVal '(n,tps)] -> LispUVal '(S n,tps)

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

data LispPVal (sig :: (Nat,Tree Type)) where
  LispP :: Struct PValue tps -> LispPVal '(Z,tps)
  LispPArray :: [LispPVal '(n,tps)] -> LispPVal '(S n,tps)

deriving instance Eq (LispPVal sig)
deriving instance Ord (LispPVal sig)
instance Show (LispPVal sig) where
  showsPrec p (LispP struct) = showsPrec p struct
  showsPrec p (LispPArray arr) = showsPrec p arr

data LispVal e lvl tp where
  Val :: e (LispType n tp) -> LispVal e n tp

data LispArrayIndex e lvl where
  ArrGet :: LispArrayIndex e Z
  ArrIdx :: e IntType -> LispArrayIndex e lvl -> LispArrayIndex e (S lvl)

lispArrayIndexLevel :: LispArrayIndex e lvl -> Natural lvl
lispArrayIndexLevel ArrGet = Zero
lispArrayIndexLevel (ArrIdx _ is) = Succ (lispArrayIndexLevel is)

instance GEq e => GEq (LispArrayIndex e) where
  geq ArrGet ArrGet = return Refl
  geq (ArrIdx e1 i1) (ArrIdx e2 i2) = do
    Refl <- geq e1 e2
    Refl <- geq i1 i2
    return Refl
  geq _ _ = Nothing

type LispIndex idx = List Natural idx

lispIndexType :: Struct Repr tps -> LispIndex idx -> Repr (Struct.ElementIndex tps idx)
lispIndexType = Struct.elementIndex

instance GShow e => Show (LispVal e lvl tp) where
  showsPrec p (Val e) = showParen (p>10) $
                        showString "Val " .
                        gshowsPrec 11 e

instance GShow e => GShow (LispVal e lvl) where
  gshowsPrec = showsPrec

getIndex :: (Embed m e,GetType e,vlvl ~ (lvl + rlvl)) => LispArrayIndex e lvl
         -> LispVal e vlvl tp
         -> m (LispVal e rlvl tp)
getIndex ArrGet (Val val) = return (Val val)
getIndex (ArrIdx i is) (Val val) = do
  e <- [expr| (select val i) |]
  getIndex is (Val e)

accessVal :: Monad m
          => LispIndex idx
          -> Struct (LispVal e lvl) tp
          -> (LispVal e lvl (Struct.ElementIndex tp idx) -> m (a,LispVal e lvl ntp))
          -> m (a,Struct (LispVal e lvl) (Struct.Insert tp idx (Leaf ntp)))
accessVal idx val = Struct.accessElement val idx

accessArray :: (Embed m e,GetType e,vlvl ~ (lvl + rlvl))
            => LispArrayIndex e lvl
            -> LispVal e vlvl tp
            -> (LispVal e rlvl tp -> m (a,LispVal e rlvl tp))
            -> m (a,LispVal e vlvl tp)
accessArray ArrGet el f = f el
accessArray (ArrIdx i is) (Val arr) f = do
  el <- [expr| (select arr i) |]
  (res,Val nel) <- accessArray is (Val el) f
  narr <- [expr| (store arr nel i) |]
  return (res,Val narr)

data RevValue sig t where
  RevVar :: LispIndex idx
         -> RevValue '(lvl,tps) (LispType lvl (Struct.ElementIndex tps idx))
  RevSize :: ((diff + rlvl) ~ lvl)
          => Natural rlvl
          -> Natural diff
          -> RevValue '(lvl,tps) (LispType rlvl IntType)

instance GEq (RevValue sig) where
  geq (RevVar i1) (RevVar i2) = do
    Refl <- geq i1 i2
    return Refl
  geq (RevSize n1 _) (RevSize n2 _) = do
    Refl <- geq n1 n2
    return Refl
  geq _ _ = Nothing

instance GCompare (RevValue sig) where
  gcompare (RevVar i1) (RevVar i2) = case gcompare i1 i2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevVar _) _ = GLT
  gcompare _ (RevVar _) = GGT
  gcompare (RevSize n1 _) (RevSize n2 _) = case gcompare n1 n2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance Show (RevValue sig t) where
  showsPrec p (RevVar idx) = showParen (p>10) $
                             showString "RevVar " .
                             showsPrec 11 idx
  showsPrec p (RevSize lvl _) = showParen (p>10) $
                                showString "RevSize " .
                                showsPrec 11 lvl

instance GShow (RevValue sig) where
  gshowsPrec = showsPrec

instance Composite (LispValue '(lvl,tps)) where
  type CompDescr (LispValue '(lvl,tps)) = (Natural lvl,Struct Repr tps)
  type RevComp (LispValue '(lvl,tps)) = RevValue '(lvl,tps)
  foldExprs f val = do
    sz' <- foldSize f (size val)
    val' <- Struct.mapM (\(Val e) -> fmap Val (f e)) (value val)
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
    sz <- createSize' (\n diff -> f (lispTypeGetType n IntRepr) (RevSize n diff)) lvl
    val <- createStruct f lvl tp
    return (LispValue sz val)
    where
      createStruct :: Monad m => (forall t. Repr t -> RevValue '(lvl,tps) t -> m (e t))
                   -> Natural lvl
                   -> Struct Repr tps
                   -> m (Struct (LispVal e lvl) tps)
      createStruct f lvl = Struct.mapIndexM
                           (\idx tp -> do
                               e <- f (lispTypeGetType lvl tp) (RevVar idx)
                               return (Val e))
  accessComposite (RevVar idx) val
    = fst $ runIdentity $ accessVal idx (value val) $
      \v@(Val e) -> return (e,v)
  accessComposite (RevSize rlvl diff) val
    = fst $ runIdentity $ accessSize (\e -> return (e,e)) rlvl diff (size val)
  eqComposite = eqValue 
  revType _ (lvl,tps) (RevVar idx) = lispTypeGetType lvl (Struct.elementIndex tps idx)
  revType _ (lvl,tps) (RevSize rlvl _) = lispTypeGetType rlvl IntRepr

instance LiftComp (LispValue '(lvl,tps)) where
  type Unpacked (LispValue '(lvl,tps)) = LispUVal '(lvl,tps)
  liftComp (LispU vals) = do
    vals' <- Struct.mapM (\v -> do
                             c <- embedConst v
                             return (Val c)
                         ) vals
    return $ LispValue NoSize vals'
  liftComp (LispUArray lvl tps lst) = do
    lst' <- mapM liftComp lst
    liftValues lst'
  unliftComp f val = case size val of
    NoSize -> do
      rval <- Struct.mapM (\(Val e) -> f e) (value val)
      return (LispU rval)
    Size sz szs -> do
      let (lvl,tps) = lispValueType val
          rlvl = case lvl of
            Succ n -> n
      vals <- unliftValue f val
      vals' <- mapM (unliftComp f) vals
      return $ LispUArray rlvl tps vals'

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
                -> Struct (LispVal e (S lvl)) tps
                -> m (Struct (LispVal e lvl) tps)
    indexValue' f n = Struct.mapM
                      (\(Val x)
                       -> do
                            n' <- embedConst n
                            x' <- [expr| (select x n') |]
                            return $ Val x')

assignPartialLisp :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
                  -> LispValue tps e -> LispPVal tps
                  -> m [Maybe p]
assignPartialLisp f val (LispP str) = assignStruct f (value val) str
  where
    assignStruct :: Embed m e => (forall t. e t -> ConcreteValue t -> m p)
                 -> Struct (LispVal e Z) tps'
                 -> Struct PValue tps'
                 -> m [Maybe p]
    assignStruct f (Singleton (Val x)) (Singleton (PValue val)) = do
      r <- f x val
      return [Just r]
    assignStruct _ _ (Singleton (NoPValue _)) = return [Nothing]
    assignStruct f (Struct xs) (Struct ys) = assignStructs f xs ys

    assignStructs :: Embed m e => (forall t. e t -> ConcreteValue t -> m p)
                  -> List (Struct (LispVal e Z)) tps'
                  -> List (Struct PValue) tps'
                  -> m [Maybe p]
    assignStructs _ Nil Nil = return []
    assignStructs f (Cons x xs) (Cons y ys) = do
      r1 <- assignStruct f x y
      r2 <- assignStructs f xs ys
      return $ r1++r2
assignPartialLisp f val (LispPArray xs) = do
  lst <- mapM (\(x,n) -> do
                  (asgnSize,nval) <- indexValue f n val
                  rest <- assignPartialLisp f nval x
                  return (Just asgnSize:rest)
              ) (zip xs [0..])
  return $ concat lst

unmaskLispValue :: LispUVal tps -> LispPVal tps
unmaskLispValue (LispU xs) = LispP $ runIdentity $ Struct.mapM (return.PValue) xs
unmaskLispValue (LispUArray _ _ xs)
  = LispPArray (fmap unmaskLispValue xs)

maskLispValue :: LispPVal tps -> [Bool] -> (LispPVal tps,[Bool])
maskLispValue (LispP str) xs = let (str',xs') = maskStruct str xs
                               in (LispP str',xs')
maskLispValue (LispPArray arr) xs
  = let (xs',arr') = mapAccumL (\xs e -> let (e',xs') = maskLispValue e xs
                                         in (xs',e')
                               ) xs arr
    in (LispPArray arr',xs')
                                  
maskStruct :: Struct PValue tps -> [Bool] -> (Struct PValue tps,[Bool])
maskStruct (Singleton (NoPValue tp)) (_:xs) = (Singleton (NoPValue tp),xs)
maskStruct (Singleton (PValue x)) (False:xs) = (Singleton (NoPValue (valueTypeC x)),xs)
maskStruct (Singleton (PValue v)) (True:xs) = (Singleton (PValue v),xs)
maskStruct (Struct str) xs = let (str',xs') = maskStructs str xs
                             in (Struct str',xs')
maskStructs :: List (Struct PValue) tps' -> [Bool]
            -> (List (Struct PValue) tps',[Bool])
maskStructs Nil xs = (Nil,xs)
maskStructs (Cons y ys) xs = let (y',xs1) = maskStruct y xs
                                 (ys',xs2) = maskStructs ys xs1
                             in (Cons y' ys',xs2)


extractStruct :: Monad m => (forall t. e t -> m (ConcreteValue t))
              -> Struct (LispVal e Z) tps
              -> m (Struct ConcreteValue tps)
extractStruct f = Struct.mapM (\(Val x) -> f x)

unliftValue :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
            -> LispValue '(S lvl,tps) e
            -> m [LispValue '(lvl,tps) e]
unliftValue f val = do
  szs <- unliftSize f (size val)
  vals <- unliftStruct f szs (value val)
  return $ zipWith LispValue szs vals

unliftStruct :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
             -> [Size e lvl]
             -> Struct (LispVal e (S lvl)) tps
             -> m [Struct (LispVal e lvl) tps]
unliftStruct f szs (Singleton (Val x))
  = mapM (\(idx,sz) -> do
             idx' <- embedConst $ IntValueC idx
             el <- [expr| (select x idx') |]
             return $ Singleton (Val el)
         ) (zip [0..] szs)
unliftStruct f szs (Struct vals) = do
  vals' <- unliftStructs f szs vals
  return $ fmap Struct vals'

unliftStructs :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
              -> [Size e lvl]
              -> List (Struct (LispVal e (S lvl))) tps
              -> m [List (Struct (LispVal e lvl)) tps]
unliftStructs f szs Nil = return $ fmap (const Nil) szs
unliftStructs f szs (Cons x xs) = do
  x' <- unliftStruct f szs x
  xs' <- unliftStructs f szs xs
  return $ zipWith Cons x' xs'

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
           => Struct ConcreteValue tps
           -> m (Struct (LispVal e Z) tps)
liftStruct = Struct.mapM (fmap Val . embedConst)

liftStructs :: (Embed m e,GetType e)
            => [Struct (LispVal e lvl) tp]
            -> m (Struct (LispVal e (S lvl)) tp)
liftStructs xs@(x:_) = case x of
  Singleton _ -> fmap Singleton $ liftVal (fmap (\(Singleton x) -> x) xs)
  Struct _ -> fmap Struct (liftStructs' (fmap (\(Struct x) -> x) xs))
  where
    liftStructs' :: (Embed m e,GetType e)
                 => [List (Struct (LispVal e lvl)) tp]
                 -> m (List (Struct (LispVal e (S lvl))) tp)
    liftStructs' (Nil:_) = return Nil
    liftStructs' xs@(Cons _ _:_) = do
      y <- liftStructs $ fmap (\(Cons x _) -> x) xs
      ys <- liftStructs' $ fmap (\(Cons _ x) -> x) xs
      return $ Cons y ys

liftVal :: (Embed m e,GetType e) => [LispVal e lvl tp] -> m (LispVal e (S lvl) tp)
liftVal xs@(Val x:_) = fmap Val $ listArray' (getType x) (fmap (\(Val x) -> x) xs)

leveledConst :: (Embed m e,GetType e)
             => Natural lvl -> e t -> m (e (LispType lvl t))
leveledConst lvl c = case lvl of
  Zero -> return c
  Succ lvl' -> do
    x <- leveledConst lvl' c
    embed $ App (ConstArray (Cons IntRepr Nil) (getType x)) (Cons x Nil)

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
  arr <- embed $ App (ConstArray (Cons IntRepr Nil) (getType def)) (Cons def Nil)
  (arr',_) <- foldlM (\(arr,n) x -> do
                         i <- embedConst (IntValueC n)
                         arr' <- [expr| (store arr x i) |]
                         return (arr',n+1)
                     ) (arr,0) els
  return arr'
