{-# LANGUAGE RankNTypes,TypeFamilies,MultiParamTypeClasses,FlexibleContexts,
             FlexibleInstances,ScopedTypeVariables,GADTs,DeriveDataTypeable,
             DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
module Realization.Lisp.Value where

import Realization.Lisp.Array

import Args
import PartialArgs

import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Struct (Tree(..),Struct(..))
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Interface

import Data.List (genericLength)
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Prelude hiding (mapM,foldl,and,concat)
import Data.GADT.Compare
import Data.GADT.Show
import Control.Monad.Identity
import Text.Show

data LispValue (sig :: ([Type],Tree Type)) (e::Type -> *) where
  LispValue :: Size e sz -> Struct (Sized e sz) tps -> LispValue '(sz,tps) e

lispValueType :: GetType e => LispValue '(sz,tps) e -> (List Repr sz,Struct Repr tps)
lispValueType (LispValue sz val) = (rsz,Struct.map (\e -> sizedType e rsz) val)
  where
    rsz = sizeIndices sz

eqValue :: (Embed m e,GetType e)
        => LispValue '(lvl,tps) e
        -> LispValue '(lvl,tps) e
        -> m (e BoolType)
eqValue (LispValue sz1 v1) (LispValue sz2 v2) = do
  conj1 <- eqSize sz1 sz2
  conj2 <- eqVal v1 v2
  case conj1++conj2 of
    [] -> embed $ ConstBool True
    [x] -> return x
    xs -> embed $ AndLst xs
  where
    eqVal :: (Embed m e,GetType e) => Struct (Sized e lvl) tps
          -> Struct (Sized e lvl) tps
          -> m [e BoolType]
    eqVal = Struct.zipFlatten (\(Sized x) (Sized y) -> do
                                  res <- embed $ x :==: y
                                  return [res])
            (return . concat)

iteValue :: (Embed m e,GetType e)
         => e BoolType -> LispValue '(sz,tps) e -> LispValue '(sz,tps) e
         -> m (LispValue '(sz,tps) e)
iteValue c (LispValue sz1 v1) (LispValue sz2 v2) = do
  nsz <- iteSize c sz1 sz2
  nval <- Struct.zipWithM (\(Sized x) (Sized y) -> do
                              z <- embed $ ITE c x y
                              return (Sized z)
                          ) v1 v2
  return (LispValue nsz nval)

geqValue :: (GetType e,GEq e) => LispValue '(lvl1,tps1) e -> LispValue '(lvl2,tps2) e -> Maybe (lvl1 :~: lvl2,tps1 :~: tps2)
geqValue (LispValue (Size sz1 _) val1) (LispValue (Size sz2 _) val2) = do
  Refl <- geq sz1 sz2
  Refl <- eqSized sz1 val1 val2
  return (Refl,Refl)
  where
    eqSized :: (GetType e,GEq e) => List Repr sz
            -> Struct (Sized e sz) tp1
            -> Struct (Sized e sz) tp2
            -> Maybe (tp1 :~: tp2)
    eqSized sz (Singleton x) (Singleton y) = do
      Refl <- geqSized sz x y
      return Refl
    eqSized sz (Struct Nil) (Struct Nil) = return Refl
    eqSized sz (Struct (x ::: xs)) (Struct (y ::: ys)) = do
      Refl <- eqSized sz x y
      Refl <- eqSized sz (Struct xs) (Struct ys)
      return Refl
    eqSized _ _ _ = Nothing

data LispUVal (sig :: ([Type],Tree Type)) where
  LispU :: Struct ConcreteValue tps -> LispUVal '( '[],tps)
  LispUArray :: Repr sz -> List Repr szs -> Struct Repr tps
             -> [LispUVal '(szs,tps)] -> LispUVal '(sz ': szs,tps)

instance GEq LispUVal where
  geq (LispU x) (LispU y) = do
    Refl <- geq x y
    return Refl
  geq (LispUArray nx nxs tpx x) (LispUArray ny nys tpy y) = do
    Refl <- geq nx ny
    Refl <- geq nxs nys
    Refl <- geq tpx tpy
    if x==y
      then return Refl
      else Nothing
  geq _ _ = Nothing

deriving instance Eq (LispUVal sig)
deriving instance Ord (LispUVal sig)

instance Show (LispUVal sig) where
  showsPrec p (LispU x) = showsPrec p x
  showsPrec p (LispUArray _ _ _ arr) = showListWith (showsPrec 0) arr

data LispPVal (sig :: ([Type],Tree Type)) where
  LispP :: Struct PValue tps -> LispPVal '( '[],tps)
  LispPArray :: Repr sz -> [LispPVal '(szs,tps)] -> LispPVal '(sz ': szs,tps)

deriving instance Eq (LispPVal sig)
deriving instance Ord (LispPVal sig)
instance Show (LispPVal sig) where
  showsPrec p (LispP struct) = showsPrec p struct
  showsPrec p (LispPArray _ arr) = showsPrec p arr

type LispIndex idx = List Natural idx

lispIndexType :: Struct Repr tps -> LispIndex idx -> Repr (Struct.ElementIndex tps idx)
lispIndexType = Struct.elementIndex

accessVal :: Monad m
          => LispIndex idx
          -> Struct (Sized e lvl) tp
          -> (Sized e lvl (Struct.ElementIndex tp idx) -> m (a,Sized e lvl ntp))
          -> m (a,Struct (Sized e lvl) (Struct.Insert tp idx (Leaf ntp)))
accessVal idx val = Struct.accessElement val idx

data RevValue sig t where
  RevVar :: LispIndex idx
         -> RevValue '(sz,tps) (Arrayed sz (Struct.ElementIndex tps idx))
  RevSize :: Natural i
          -> RevValue '(sz,tps) (List.Index (SizeList sz) i)

instance GEq (RevValue sig) where
  geq (RevVar i1) (RevVar i2) = do
    Refl <- geq i1 i2
    return Refl
  geq (RevSize n1) (RevSize n2) = do
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
  gcompare (RevSize n1) (RevSize n2) = case gcompare n1 n2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance Show (RevValue sig t) where
  showsPrec p (RevVar idx) = showParen (p>10) $
                             showString "RevVar " .
                             showsPrec 11 idx
  showsPrec p (RevSize lvl) = showParen (p>10) $
                              showString "RevSize " .
                              showsPrec 11 lvl

instance GShow (RevValue sig) where
  gshowsPrec = showsPrec

instance Composite (LispValue '(lvl,tps)) where
  type CompDescr (LispValue '(lvl,tps)) = (List Repr lvl,Struct Repr tps)
  type RevComp (LispValue '(lvl,tps)) = RevValue '(lvl,tps)
  compositeType (sz,tps)
    = LispValue (sizeType sz)
      (runIdentity $ Struct.mapM
       (\tp -> return (Sized (arrayType sz tp))) tps)
  foldExprs f (LispValue sz val) = do
    sz' <- foldSize (\i -> f (RevSize i)) sz
    val' <- Struct.mapIndexM (\idx (Sized e) -> fmap Sized (f (RevVar idx) e)) val
    return $ LispValue sz' val'
  createComposite f (lvl,tp) = do
    sz <- createSize (\i tp -> f tp (RevSize i)) lvl
    val <- createStruct f lvl tp
    return (LispValue sz val)
    where
      createStruct :: Monad m => (forall t. Repr t -> RevValue '(lvl,tps) t -> m (e t))
                   -> List Repr lvl
                   -> Struct Repr tps
                   -> m (Struct (Sized e lvl) tps)
      createStruct f lvl = Struct.mapIndexM
                           (\idx tp -> do
                               e <- f (arrayType lvl tp) (RevVar idx)
                               return (Sized e))
  accessComposite (RevVar idx) (LispValue sz val)
    = fst $ runIdentity $ accessVal idx val $
      \v@(Sized e) -> return (e,v)
  accessComposite (RevSize idx) (LispValue sz val)
    = fst $ runIdentity $ accessSize (\e -> return (e,e)) idx sz
  eqComposite = eqValue 
  revType _ (lvl,tps) (RevVar idx) = arrayType lvl (Struct.elementIndex tps idx)
  revType _ (lvl,tps) (RevSize idx)
    = List.index (sizeListType lvl) idx

instance LiftComp (LispValue '(lvl,tps)) where
  type Unpacked (LispValue '(lvl,tps)) = LispUVal '(lvl,tps)
  liftComp (LispU vals) = do
    vals' <- Struct.mapM (\v -> do
                             c <- embedConst v
                             return (Sized c)
                         ) vals
    return $ LispValue (Size Nil Nil) vals'
  liftComp (LispUArray sz szs tps lst) = do
    lst' <- mapM liftComp lst
    liftValues sz szs tps lst'
  unliftComp f lv@(LispValue sz val) = case sz of
    Size Nil Nil -> do
      rval <- Struct.mapM (\(Sized e) -> f e) val
      return (LispU rval)
    Size (_ ::: _) (_ ::: _) -> case lispValueType lv of
      (sz' ::: szs,tps) -> do
        vals <- unliftValue f lv
        vals' <- mapM (unliftComp f) vals
        return $ LispUArray sz' szs tps vals'

indexValue :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
           -> ConcreteValue sz
           -> LispValue '(sz ': szs,tps) e
           -> m (p,LispValue '(szs,tps) e)
indexValue f idx (LispValue sz val) = do
  (res,nsz) <- indexSize f idx sz
  nval <- indexValue' f idx val
  return (res,LispValue nsz nval)
  where
    indexSize :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
              -> ConcreteValue sz -> Size e (sz ': szs)
              -> m (p,Size e szs)
    indexSize f n (Size (tp ::: tps) (sz ::: szs)) = do
      res <- f sz n
      nszs <- List.unmapM (sizeListType tps) szs (\arr -> do
                                                     n' <- embedConst n
                                                     embed $ Select arr (n' ::: Nil))
      return (res,Size tps nszs)

    indexValue' :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
                -> ConcreteValue sz
                -> Struct (Sized e (sz ': szs)) tps
                -> m (Struct (Sized e szs) tps)
    indexValue' f n = Struct.mapM
                      (\(Sized x)
                       -> do
                            n' <- embedConst n
                            x' <- embed $ Select x (n' ::: Nil)
                            return $ Sized x')

assignPartialLisp :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
                  -> LispValue tps e -> LispPVal tps
                  -> m [Maybe p]
assignPartialLisp f (LispValue sz val) (LispP str) = assignStruct f val str
  where
    assignStruct :: Embed m e => (forall t. e t -> ConcreteValue t -> m p)
                 -> Struct (Sized e '[]) tps'
                 -> Struct PValue tps'
                 -> m [Maybe p]
    assignStruct f (Singleton (Sized x)) (Singleton (PValue val)) = do
      r <- f x val
      return [Just r]
    assignStruct _ _ (Singleton (NoPValue _)) = return [Nothing]
    assignStruct f (Struct xs) (Struct ys) = assignStructs f xs ys

    assignStructs :: Embed m e => (forall t. e t -> ConcreteValue t -> m p)
                  -> List (Struct (Sized e '[])) tps'
                  -> List (Struct PValue) tps'
                  -> m [Maybe p]
    assignStructs _ Nil Nil = return []
    assignStructs f (x ::: xs) (y ::: ys) = do
      r1 <- assignStruct f x y
      r2 <- assignStructs f xs ys
      return $ r1++r2
assignPartialLisp f val (LispPArray sz xs) = do
  lst <- mapM (\(x,n) -> do
                  (asgnSize,nval) <- indexValue f n val
                  rest <- assignPartialLisp f nval x
                  return (Just asgnSize:rest)
              ) (zip xs range)
  return $ concat lst
  where
    len = lengthValue sz (genericLength xs)
    range = sizeRange len

unmaskLispValue :: LispUVal tps -> LispPVal tps
unmaskLispValue (LispU xs) = LispP $ runIdentity $ Struct.mapM (return.PValue) xs
unmaskLispValue (LispUArray sz _ _ xs)
  = LispPArray sz (fmap unmaskLispValue xs)

maskLispValue :: LispPVal tps -> [Bool] -> (LispPVal tps,[Bool])
maskLispValue (LispP str) xs = let (str',xs') = maskStruct str xs
                               in (LispP str',xs')
maskLispValue (LispPArray sz arr) xs
  = let (xs',arr') = mapAccumL (\xs e -> let (e',xs') = maskLispValue e xs
                                         in (xs',e')
                               ) xs arr
    in (LispPArray sz arr',xs')

maskStruct :: Struct PValue tps -> [Bool] -> (Struct PValue tps,[Bool])
maskStruct (Singleton (NoPValue tp)) (_:xs) = (Singleton (NoPValue tp),xs)
maskStruct (Singleton (PValue x)) (False:xs) = (Singleton (NoPValue (valueTypeC x)),xs)
maskStruct (Singleton (PValue v)) (True:xs) = (Singleton (PValue v),xs)
maskStruct (Struct str) xs = let (str',xs') = maskStructs str xs
                             in (Struct str',xs')

maskStructs :: List (Struct PValue) tps' -> [Bool]
            -> (List (Struct PValue) tps',[Bool])
maskStructs Nil xs = (Nil,xs)
maskStructs (y ::: ys) xs = let (y',xs1) = maskStruct y xs
                                (ys',xs2) = maskStructs ys xs1
                            in (y' ::: ys',xs2)

extractStruct :: Monad m => (forall t. e t -> m (ConcreteValue t))
              -> Struct (Sized e '[]) tps
              -> m (Struct ConcreteValue tps)
extractStruct f = Struct.mapM (\(Sized x) -> f x)

unliftValue :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
            -> LispValue '(sz ': szs,tps) e
            -> m [LispValue '(szs,tps) e]
unliftValue f lv@(LispValue sz val) = case lispValueType lv of
  (csz ::: szs,tps) -> do
    nszs <- unliftSize f sz
    nvals <- unliftStruct f csz nszs val
    return $ zipWith LispValue nszs nvals

unliftStruct :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
             -> Repr sz
             -> [Size e szs]
             -> Struct (Sized e (sz ': szs)) tps
             -> m [Struct (Sized e szs) tps]
unliftStruct f sz szs (Singleton (Sized x))
  = mapM (\(idx,sz) -> do
             idx' <- embedConst idx
             el <- embed $ Select x (idx' ::: Nil)
             return $ Singleton (Sized el)
         ) (zip range szs)
  where
    len = lengthValue sz (genericLength szs)
    range = sizeRange len
unliftStruct f sz szs (Struct vals) = do
  vals' <- unliftStructs f sz szs vals
  return $ fmap Struct vals'

unliftStructs :: (Embed m e,GetType e)
              => (forall t. e t -> m (ConcreteValue t))
              -> Repr sz
              -> [Size e szs]
              -> List (Struct (Sized e (sz ': szs))) tps
              -> m [List (Struct (Sized e szs)) tps]
unliftStructs f sz szs Nil = return $ fmap (const Nil) szs
unliftStructs f sz szs (x ::: xs) = do
  x' <- unliftStruct f sz szs x
  xs' <- unliftStructs f sz szs xs
  return $ zipWith (:::) x' xs'

liftValues :: (Embed m e,GetType e)
           => Repr sz
           -> List Repr szs
           -> Struct Repr tps
           -> [LispValue '(szs,tps) e]
           -> m (LispValue '(sz ': szs,tps) e)
liftValues sz szs tps xs = do
  nsz <- liftSizes sz szs (fmap (\(LispValue sz _) -> sz) xs)
  nval <- liftStructs sz szs tps (fmap (\(LispValue _ val) -> val) xs)
  return $ LispValue nsz nval

liftStruct :: (Embed m e,GetType e)
           => Struct ConcreteValue tps
           -> m (Struct (Sized e '[]) tps)
liftStruct = Struct.mapM (fmap Sized . embedConst)

liftStructs :: (Embed m e,GetType e)
            => Repr sz
            -> List Repr szs
            -> Struct Repr tp
            -> [Struct (Sized e szs) tp]
            -> m (Struct (Sized e (sz ': szs)) tp)
liftStructs sz szs tp vals = case tp of
  Singleton tp' -> fmap Singleton $ liftSized sz szs tp' (fmap (\(Singleton x) -> x) vals)
  Struct tps -> fmap Struct (liftStructs' sz szs tps (fmap (\(Struct x) -> x) vals))
  where
    liftStructs' :: (Embed m e,GetType e)
                 => Repr sz
                 -> List Repr szs
                 -> List (Struct Repr) tps
                 -> [List (Struct (Sized e szs)) tps]
                 -> m (List (Struct (Sized e (sz ': szs))) tps)
    liftStructs' sz szs Nil _ = return Nil
    liftStructs' sz szs (tp ::: tps) vals = do
      y <- liftStructs sz szs tp $ fmap (\(x ::: _) -> x) vals
      ys <- liftStructs' sz szs tps $ fmap (\(_ ::: xs) -> xs) vals
      return $ y ::: ys
