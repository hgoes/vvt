{-# LANGUAGE UndecidableInstances #-}
module Realization.Lisp.Array where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Interface

import Data.GADT.Compare
import Data.GADT.Show
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Functor.Identity
import Data.List (genericLength)
import Data.Foldable (foldlM)

type family Arrayed (sz :: [Type]) (tp :: Type) :: Type where
  Arrayed '[] tp = tp
  Arrayed (x ': xs) tp = ArrayType '[x] (Arrayed xs tp)

type family SizeList (sz :: [Type]) :: [Type] where
  SizeList '[] = '[]
  SizeList (x ': xs) = x ': (List.Map (SizeList xs) (ArrayType '[x]))

arrayType :: List Repr sz -> Repr tp -> Repr (Arrayed sz tp)
arrayType Nil tp = tp
arrayType (x ::: xs) tp = ArrayRepr (x ::: Nil) (arrayType xs tp)

arrayedType :: Repr (Arrayed sz tp) -> List Repr sz -> Repr tp
arrayedType tp Nil = tp
arrayedType (ArrayRepr (_ ::: Nil) el) (_ ::: tps)
  = arrayedType el tps

isArrayed :: Repr tp -> List Repr sz
          -> (forall tp'. (tp ~ Arrayed sz tp') => Repr tp' -> a)
          -> Maybe a
isArrayed tp Nil f = Just (f tp)
isArrayed (ArrayRepr (idx ::: Nil) tp) (i ::: is) f
  = case geq idx i of
  Just Refl -> isArrayed tp is f
  Nothing -> Nothing

sizeListType :: List Repr sz -> List Repr (SizeList sz)
sizeListType Nil = Nil
sizeListType (x ::: xs) = x ::: (List.map (sizeListType xs) (ArrayRepr (x ::: Nil)))

data Size (e :: Type -> *) (sz :: [Type]) where
  Size :: List Repr sz -> List e (SizeList sz) -> Size e sz

sizeType :: List Repr sz -> Size Repr sz
sizeType lst = Size lst (sizeListType lst)

sizeIndices :: Size e sz -> List Repr sz
sizeIndices (Size tps _) = tps

accessSize :: (Monad m) => (e (List.Index (SizeList sz) i)
                            -> m (a,e (List.Index (SizeList sz) i)))
           -> Natural i
           -> Size e sz
           -> m (a,Size e sz)
accessSize f idx (Size tps sz) = do
  (res,nsz) <- List.access' sz idx f
  return (res,Size tps nsz)

createSize :: forall m e sz.
              Monad m => (forall i. Natural i -> Repr (List.Index (SizeList sz) i)
                          -> m (e (List.Index (SizeList sz) i)))
           -> List Repr sz
           -> m (Size e sz)
createSize f sz = do
  rsz <- List.mapIndexM f (sizeListType sz)
  return (Size sz rsz)

deSize :: Monad m => Size e (sz ': szs)
       -> (forall tp. Repr sz -> e sz -> e (ArrayType '[sz] tp) -> m (e tp))
       -> m (Size e szs)
deSize (Size (tp ::: tps) (sz ::: szs)) f = do
  nszs <- List.unmapM (sizeListType tps) szs (f tp sz)
  return (Size tps nszs)

asArray :: Repr idx -> Repr tp
        -> (forall tp'. (tp ~ ArrayType '[idx] tp')
            => Repr tp' -> Maybe a)
        -> Maybe a
asArray idx (ArrayRepr (idx' ::: Nil) el) f = do
  Refl <- geq idx idx'
  f el
asArray _ _ _ = Nothing

asArrays :: Repr idx -> List Repr tps
         -> (forall tps'. (tps ~ List.Map tps' (ArrayType '[idx]))
             => List Repr tps' -> Maybe a)
         -> Maybe a
asArrays _ Nil g = g Nil
asArrays idx (tp ::: tps) g
  = asArray idx tp $
    \tp' -> asArrays idx tps $
            \tps' -> g (tp' ::: tps')

enSize :: GetType e => e sz -> Size e szs
       -> (forall szs'. (szs ~ List.Map szs' (ArrayType '[sz]))
           => Size e (sz ': szs') -> Maybe a)
       -> Maybe a
enSize sz (Size tps szs) f
  = asArrays tp tps $
    \ntps -> case geq (sizeListType (tp ::: ntps))
                  (tp ::: (runIdentity (List.mapM (return.getType) szs))) of
             Just Refl -> f (Size (tp ::: ntps) (sz ::: szs))
  where
    tp = getType sz

indexSize :: (Embed m e,GetType e) => Size e (sz ': szs) -> e sz -> m (Size e szs)
indexSize sz idx = deSize sz (\_ _ arr -> embed $ Select arr (idx ::: Nil))

liftSizes :: (Embed m e,GetType e)
          => Repr sz -> List Repr szs
          -> [Size e szs]
          -> m (Size e (sz ': szs))
liftSizes tp tps vals = do
  sz <- embedConst len
  rangeR <- mapM embedConst range
  szs <- buildSize sz tps (zip rangeR (fmap (\(Size _ sz) -> sz) vals))
  return (Size (tp ::: tps) szs)
  where
    len = lengthValue tp (genericLength vals)
    range = sizeRange len
    buildSize :: (Embed m e,GetType e)
              => e sz
              -> List Repr szs
              -> [(e sz,List e (SizeList szs))]
              -> m (List e (SizeList (sz ': szs)))
    buildSize sz tps vals = do
      def <- List.mapM (\tp -> defaultValue tp)
             (List.map (sizeListType tps)
              (ArrayRepr ((getType sz) ::: Nil)))
      arr <- foldlM (\carr (idx,val) -> zipArr idx carr val
                    ) def vals
      return (sz ::: arr)

    zipArr :: (Embed m e,GetType e)
           => e sz
           -> List e (List.Map lst (ArrayType '[sz]))
           -> List e lst
           -> m (List e (List.Map lst (ArrayType '[sz])))
    zipArr idx Nil Nil = return Nil
    zipArr idx (arr ::: arrs) (el ::: els) = do
      narr <- embed $ Store arr (idx ::: Nil) el
      narrs <- zipArr idx arrs els
      return (narr ::: narrs)
    
unliftSize :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
           -> Size e (sz ': szs)
           -> m [Size e szs]
unliftSize f sz@(Size (_ ::: _) (s ::: _)) = do
  x <- f s
  mapM (\i -> do
           i' <- embedConst i
           indexSize sz i'
       ) (sizeRange x)

sizeRange :: ConcreteValue tp -> [ConcreteValue tp]
sizeRange (BoolValueC False) = []
sizeRange (BoolValueC True) = [BoolValueC False]
sizeRange (IntValueC n) = [IntValueC i | i <- [0..n-1] ]
sizeRange (RealValueC _) = error "sizeRange: Cannot generate size range for real type."
sizeRange (BitVecValueC v bw) = [BitVecValueC i bw | i <- [0..v-1] ]
sizeRange (ConstrValueC _) = error "sizeRange: Cannot generate size range for user defined type."

defaultValue :: (Embed m e,GetType e) => Repr tp -> m (e tp)
defaultValue BoolRepr = embedConst $ BoolValueC False
defaultValue IntRepr = embedConst $ IntValueC 0
defaultValue RealRepr = embedConst $ RealValueC 0
defaultValue (BitVecRepr bw) = embedConst $ BitVecValueC 0 bw
defaultValue (ArrayRepr idx tp) = do
  def <- defaultValue tp
  embed $ ConstArray idx def
defaultValue (DataRepr _) = error "defaultValue: User defined types don't have default values."

lengthValue :: Repr tp -> Integer -> ConcreteValue tp
lengthValue BoolRepr 0 = BoolValueC False
lengthValue BoolRepr 1 = BoolValueC True
lengthValue BoolRepr n = error $ "lengthValue: length of "++show n++" invalid for bool type."
lengthValue IntRepr n = IntValueC n
lengthValue RealRepr n = RealValueC (fromInteger n)
lengthValue (BitVecRepr bw) n
  | n < 2^(naturalToInteger bw) = BitVecValueC n bw
  | otherwise = error $ "lengthValue: length of "++show n++" invalid for bitvector "++
                show (naturalToInteger bw)++" type."
lengthValue (DataRepr _) n = error "lengthValue: Cannot represent length as user defined data type."

eqSize :: (Embed m e,GetType e) => Size e sz -> Size e sz -> m [e BoolType]
eqSize (Size _ sz1) (Size _ sz2)
  = List.zipToListM (\x y -> embed $ x :==: y) sz1 sz2

iteSize :: (Embed m e,GetType e) => e BoolType -> Size e sz -> Size e sz -> m (Size e sz)
iteSize c (Size tps sz1) (Size _ sz2) = do
  nsz <- List.zipWithM (\x y -> embed $ ITE c x y) sz1 sz2
  return (Size tps nsz)

parseSize' :: GetType e => (forall r. L.Lisp -> (forall tp. e tp -> r) -> r)
           -> [L.Lisp]
           -> (forall sz. Size e sz -> Maybe r)
           -> Maybe r
parseSize' f [] g = g (Size Nil Nil)
parseSize' f (x:xs) g
  = f x $ \sz -> parseSize' f xs $
                 \szs -> enSize sz szs g  

instance GEq (Size e) where
  geq (Size sz1 _) (Size sz2 _) = do
    Refl <- geq sz1 sz2
    return Refl

-- Sized

newtype Sized (e :: Type -> *) (sz :: [Type]) (tp :: Type)
  = Sized (e (Arrayed sz tp))

sizedType :: GetType e => Sized e sz tp -> List Repr sz -> Repr tp
sizedType (Sized e) sz = arrayedType (getType e) sz

geqSized :: (GetType e,GEq e) => List Repr sz -> Sized e sz tp1 -> Sized e sz tp2
         -> Maybe (tp1 :~: tp2)
geqSized sz x@(Sized x') y@(Sized y') = do
  Refl <- geq (sizedType x sz) (sizedType y sz)
  Refl <- geq x' y'
  return Refl

foldSize :: Monad m => (forall i. Natural i -> e (List.Index (SizeList sz) i)
                        -> m (e' (List.Index (SizeList sz) i)))
         -> Size e sz
         -> m (Size e' sz)
foldSize f (Size tps sz) = do
  nsz <- List.mapIndexM f sz
  return (Size tps nsz)

getIndex :: (Embed m e,GetType e)
         => List e idx
         -> Size e sz
         -> Sized e sz tp
         -> m (e (Arrayed (List.StripPrefix sz idx) tp))
getIndex idx sz e'@(Sized e)
  = getIndex' idx rsz (sizedType e' rsz) e
  where
    rsz = sizeIndices sz

getIndex' :: (Embed m e,GetType e)
          => List e idx
          -> List Repr sz
          -> Repr tp
          -> e (Arrayed sz tp)
          -> m (e (Arrayed (List.StripPrefix sz idx) tp))
getIndex' Nil _ _ e = return e
getIndex' (i ::: is) (j ::: js) tp e
  = case geq (getType i) j of
  Just Refl -> do
    e' <- embed $ Select e (i ::: Nil)
    getIndex' is js tp e'

indexArray :: (Embed m e,GetType e)
           => List e sz
           -> Sized e sz tp
           -> m (e tp)
indexArray Nil (Sized e) = return e
indexArray (i ::: is) (Sized e) = do
  ne <- embed $ Select e (i ::: Nil)
  indexArray is (Sized ne)

accessArray :: (Embed m e,GetType e)
            => List e idx
            -> List Repr sz
            -> Sized e sz tp
            -> (e (Arrayed (List.StripPrefix sz idx) tp)
                -> m (a,e (Arrayed (List.StripPrefix sz idx) tp)))
            -> m (a,Sized e sz tp)
accessArray idx sz e'@(Sized e) f = do
  (res,ne) <- accessArray' idx sz (sizedType e' sz) e f
  return (res,Sized ne)

accessArray' :: (Embed m e,GetType e)
             => List e idx
             -> List Repr sz
             -> Repr tp
             -> e (Arrayed sz tp)
             -> (e (Arrayed (List.StripPrefix sz idx) tp)
                 -> m (a,e (Arrayed (List.StripPrefix sz idx) tp)))
             -> m (a,e (Arrayed sz tp))
accessArray' Nil _ _ e f = f e
accessArray' (i ::: is) (j ::: js) tp e f
  = case geq (getType i) j of
  Just Refl -> do
    el <- embed $ Select e (i ::: Nil)
    (res,nel) <- accessArray' is js tp el f
    ne <- embed $ Store e (i ::: Nil) nel
    return (res,ne)

accessArrayElement :: (Embed m e,GetType e)
                   => List e sz
                   -> Sized e sz tp
                   -> (e tp -> m (a,e tp))
                   -> m (a,Sized e sz tp)
accessArrayElement Nil (Sized e) f = do
  (res,ne) <- f e
  return (res,Sized ne)
accessArrayElement (i ::: is) (Sized e) f = do
  el <- embed $ Select e (i ::: Nil)
  (res,Sized nel) <- accessArrayElement is (Sized el) f
  ne <- embed $ Store e (i ::: Nil) nel
  return (res,Sized ne)

liftSized :: (Embed m e,GetType e)
          => Repr sz
          -> List Repr szs
          -> Repr tp
          -> [Sized e szs tp]
          -> m (Sized e (sz ': szs) tp)
liftSized sz szs tp vals = do
  def <- defaultValue arrTp
  arr <- embed $ ConstArray (sz ::: Nil) def
  ne <- foldlM (\carr (idx,Sized e) -> do
                   idx' <- embedConst idx
                   embed $ Store carr (idx' ::: Nil) e
               ) arr (zip range vals)
  return (Sized ne)
  where
    len = lengthValue sz (genericLength vals)
    range = sizeRange len
    arrTp = arrayType szs tp

instance GShow e => Show (Sized e sz tp) where
  showsPrec p (Sized e) = showParen (p>10) $
                          showString "Sized " .
                          gshowsPrec 11 e

instance GShow e => GShow (Sized e lvl) where
  gshowsPrec = showsPrec
