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

class Typeable sig => GetStructType (sig::Struct Type) where
  getStructType :: LispStruct Repr sig

class Typeable sig => GetStructTypes (sig::[Struct Type]) where
  getStructTypes :: StructArgs Repr sig

instance (GetType t) => GetStructType ('Singleton t) where
  getStructType = LSingleton getType

instance (GetStructTypes tps) => GetStructType ('Struct tps) where
  getStructType = LStruct getStructTypes

instance GetStructTypes '[] where
  getStructTypes = NoSArg

instance (GetStructType tp,GetStructTypes tps) => GetStructTypes (tp ': tps) where
  getStructTypes = SArg getStructType
                        getStructTypes

type family LispType (lvl :: Nat) (t :: Type) :: Type where
  LispType Z t = t
  LispType (S n) t = ArrayType '[IntType] (LispType n t)

class IndexableStruct (tps :: [Struct Type]) (idx :: Nat) where
  type Idx tps idx :: Struct Type
  accessStruct :: Monad m
               => StructArgs (LispVal b lvl) tps -> Proxy idx
               -> (LispStruct (LispVal b lvl) (Idx tps idx)
                   -> m (a,LispStruct (LispVal b lvl) (Idx tps idx)))
               -> m (a,StructArgs (LispVal b lvl) tps)

instance IndexableStruct (tp ': tps) Z where
  type Idx (tp ': tps) Z = tp
  accessStruct (SArg x xs) _ f = do
    (res,nx) <- f x
    return (res,SArg nx xs)

instance IndexableStruct tps n => IndexableStruct (tp ': tps) (S n) where
  type Idx (tp ': tps) (S n) = Idx tps n
  accessStruct (SArg x xs) (_::Proxy (S n)) f = do
    (res,nxs) <- accessStruct xs (Proxy::Proxy n) f
    return (res,SArg x nxs)

data Size (e::Type -> *) (lvl :: Nat) where
  NoSize :: Size e Z
  Size :: (KnownNat n,GetType (LispType n IntType))
       => e (LispType n IntType) -> !(Size e n) -> Size e (S n)

data StructArgs e (sig :: [Struct Type]) where
  NoSArg :: StructArgs e '[]
  SArg :: !(LispStruct e tp) -> !(StructArgs e tps) -> StructArgs e (tp ': tps)

data LispStruct e (tp :: Struct Type) where
  LSingleton :: GetType t => !(e t) -> LispStruct e (Singleton t)
  LStruct :: !(StructArgs e sig) -> LispStruct e ('Struct sig)

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
  = LispValue { size :: !(Size e (Fst sig))
              , value :: !(LispStruct (LispVal e (Fst sig)) (Snd sig)) }

data LispUVal (sig :: (Nat,Struct Type)) where
  LispU :: GetStructType tps => !(LispStruct ConcreteValue tps) -> LispUVal '(Z,tps)
  LispUArray :: KnownNat n => !([LispUVal '(n,tps)]) -> LispUVal '(S n,tps)

instance Show (LispUVal sig) where
  showsPrec p (LispU x) = showsPrec p x
  showsPrec p (LispUArray arr) = showListWith (showsPrec 0) arr

data LispPVal (sig :: (Nat,Struct Type)) where
  LispP :: GetStructType tps => !(LispStruct PValue tps) -> LispPVal '(Z,tps)
  LispPArray :: KnownNat n => !([LispPVal '(n,tps)]) -> LispPVal '(S n,tps)

data LispVal e lvl tp where
  Val :: GetType (LispType n tp) => !(e (LispType n tp)) -> LispVal e n tp

data LispArrayIndex e (lvl::Nat) (rlvl::Nat) (tp::Type) where
  ArrGet :: GetType (LispType lvl tp) => LispArrayIndex e lvl lvl tp
  ArrIdx :: GetType (LispType lvl tp)
         => !(e IntType)
         -> !(LispArrayIndex e lvl n tp)
         -> LispArrayIndex e (S lvl) n tp

data LispIndex (tp :: Struct Type) (res :: Type) where
  ValGet :: GetType tp => LispIndex (Singleton tp) tp
  ValIdx :: (KnownNat n,IndexableStruct tps n)
         => !(Proxy n)
         -> !(LispIndex (Idx tps n) res)
         -> LispIndex ('Struct tps) res

instance GShow e => GShow (LispStruct e) where
  gshowsPrec = showsPrec

instance GShow e => Show (LispVal e lvl tp) where
  showsPrec p (Val e) = showParen (p>10) $
                        showString "Val " .
                        gshowsPrec 11 e

instance GShow e => GShow (LispVal e lvl) where
  gshowsPrec = showsPrec

getIndex :: (Embed m e,GetType tp) => LispArrayIndex e lvl rlvl tp
         -> LispVal e lvl tp
         -> m (LispVal e rlvl tp)
getIndex ArrGet (Val val) = return (Val val)
getIndex (ArrIdx i is) (Val val) = do
  e <- [expr| (select val i) |]
  getIndex is (Val e)

accessVal :: Monad m
          => LispIndex tp res
          -> LispStruct (LispVal e lvl) tp
          -> (LispVal e lvl res -> m (a,LispVal e lvl res))
          -> m (a,LispStruct (LispVal e lvl) tp)
accessVal ValGet (LSingleton val) f = do
  (res,nval) <- f val
  return (res,LSingleton nval)
accessVal (ValIdx pr is) (LStruct tps) f = do
  (res,ntps) <- accessStruct tps pr (\tp -> accessVal is tp f)
  return (res,LStruct ntps)

accessArray :: (Embed m e)
            => LispArrayIndex e lvl rlvl tp
            -> LispVal e lvl tp
            -> (LispVal e rlvl tp -> m (a,LispVal e rlvl tp))
            -> m (a,LispVal e lvl tp)
accessArray ArrGet el f = f el
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
  RevVar :: LispIndex tps tp -> RevValue '(lvl,tps) (LispType lvl tp)
  RevSize :: KnownNat rlvl
          => Proxy rlvl
          -> RevValue '(S lvl,tps) (LispType rlvl IntType)

instance GEq (LispIndex tps) where
  geq (ValGet::LispIndex tps1 t1) (ValGet::LispIndex tps2 t2)
    = case eqT :: Maybe (t1 :~: t2) of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (ValIdx (_::Proxy p1) i1) (ValIdx (_::Proxy p2) i2)
    = case eqT :: Maybe (p1 :~: p2) of
    Just Refl -> case geq i1 i2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
    Nothing -> Nothing
  geq _ _ = Nothing

-- Don't inline compareLispIndex here or the instance becomes incoherent (Don't ask me...)
instance GCompare (LispIndex tps) where
  gcompare = compareLispIndex

instance Show (LispIndex tps tp) where
  showsPrec p ValGet = showString "ValGet"
  showsPrec p (ValIdx n idx) = showParen (p>10) $
                               showString "ValIdx " .
                               showsPrec 11 (natVal n) .
                               showChar ' ' .
                               showsPrec 11 idx

instance GShow (LispIndex idx) where
  gshowsPrec = showsPrec

compareLispIndex :: LispIndex tps t1 -> LispIndex tps t2 -> GOrdering t1 t2
compareLispIndex (ValGet::LispIndex tps1 t1) (ValGet::LispIndex tps2 t2)
  = case eqT :: Maybe (t1 :~: t2) of
    Just Refl -> GEQ
    Nothing -> case compare (typeRep (Proxy::Proxy t1)) (typeRep (Proxy::Proxy t2)) of
      LT -> GLT
      GT -> GGT
compareLispIndex ValGet _ = GLT
compareLispIndex _ ValGet = GGT
compareLispIndex (ValIdx (p1::Proxy n1) i1) (ValIdx (p2::Proxy n2) i2)
  = case eqT :: Maybe (n1 :~: n2) of
  Just Refl -> case compareLispIndex i1 i2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  Nothing -> case compare (typeRep p1) (typeRep p2) of
    LT -> GLT
    GT -> GGT

instance GEq (RevValue sig) where
  geq (RevVar i1) (RevVar i2) = case geq i1 i2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (RevSize (_::Proxy lvl1)) (RevSize (_::Proxy lvl2))
    = case eqT :: Maybe (lvl1 :~: lvl2) of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq _ _ = Nothing

instance GCompare (RevValue sig) where
  gcompare (RevVar i1) (RevVar i2) = case gcompare i1 i2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevVar _) _ = GLT
  gcompare _ (RevVar _) = GGT
  gcompare (RevSize (p1::Proxy lvl1)) (RevSize (p2::Proxy lvl2))
    = case eqT :: Maybe (lvl1 :~: lvl2) of
    Just Refl -> GEQ
    Nothing -> case compare (typeRep p1) (typeRep p2) of
      LT -> GLT
      GT -> GGT

instance Show (RevValue sig t) where
  showsPrec p (RevVar idx) = showParen (p>10) $
                             showString "RevVar " .
                             showsPrec 11 idx
  showsPrec p (RevSize lvl) = showParen (p>10) $
                              showString "RevSize " .
                              showsPrec 11 (natVal lvl)

instance GShow (RevValue sig) where
  gshowsPrec = showsPrec

instance (KnownNat lvl,GetStructType tps) => Composite (LispValue '(lvl,tps)) where
  type CompDescr (LispValue '(lvl,tps)) = ()
  type RevComp (LispValue '(lvl,tps)) = RevValue '(lvl,tps)
  foldExprs f val = do
    sz' <- foldSize f (size val)
    val' <- mapLispStructM (\_ (Val e) -> fmap Val (f e)) (value val)
    return $ LispValue sz' val'
    where
      foldSize :: Monad m => (forall t. GetType t => e t -> m (e' t))
               -> Size e lvl'
               -> m (Size e' lvl')
      foldSize f NoSize = return NoSize
      foldSize f (Size sz szs) = do
        nsz <- f sz
        nszs <- foldSize f szs
        return $ Size nsz nszs
  createComposite f () = with $ \pr -> do
    sz <- case natPred pr of
      NoPred -> return NoSize
      Pred pr' -> createSize pr' f NoSize
    val <- createStruct f getStructType
    return (LispValue sz val)
    where
      with :: (Proxy lvl -> m (LispValue '(lvl,tps) tp)) -> m (LispValue '(lvl,tps) tp)
      with f = f Proxy
      createSize :: (Monad m,KnownNat lvl',GetType (LispType lvl' IntType),KnownNat lvl2)
                 => Proxy lvl2 -> (forall t. GetType t => RevValue '(S lvl2,tp) t -> m (e t))
                 -> Size e lvl' -> m (Size e (S lvl2))
      createSize (pr::Proxy lvl2) f (szs::Size e lvl')
        = case eqT :: Maybe (S lvl2 :~: lvl') of
            Nothing -> do
              sz <- f (RevSize (Proxy::Proxy lvl'))
              createSize pr f (Size sz szs)
            Just Refl -> return szs

      createStruct :: Monad m => (forall t. GetType t => RevValue '(lvl,tps) t -> m (e t))
                   -> LispStruct Repr tps
                   -> m (LispStruct (LispVal e lvl) tps)
      createStruct f = mapLispStructM
                       (\idx (x::Repr tp) -> case deriveLispTypeCtx (Proxy::Proxy lvl)
                                                                    (Proxy::Proxy tp) of
            Dict -> do
              e <- f (RevVar idx)
              return (Val e))
  accessComposite (RevVar idx) val
    = fst $ runIdentity $ accessVal idx (value val) $
      \v@(Val e) -> return (e,v)
  accessComposite (RevSize idx) val = getSize idx (size val)
    where
      getSize :: KnownNat rlvl => Proxy rlvl -> Size e (S lvl') -> e (LispType rlvl IntType)
      getSize idx (Size (i::e (LispType lvl' IntType)) is :: Size e (S lvl'))
        = case sameNat idx (Proxy::Proxy lvl') of
        Just Refl -> i
        Nothing -> case is of
          Size _ _ -> getSize idx is
  eqComposite v1 v2 = do
    eqS <- eqSize (size v1) (size v2)
    eqV <- eqStruct (value v1) (value v2)
    let eqs = eqS++eqV
    [expr| (and # eqs) |]
    where
      eqSize :: Embed m e => Size e n -> Size e n -> m [e BoolType]
      eqSize NoSize NoSize = return []
      eqSize (Size x xs) (Size y ys) = do
        eq <- [expr| (= x y) |]
        eqs <- eqSize xs ys
        return (eq:eqs)
      eqStruct :: Embed m e
               => LispStruct (LispVal e n) tps'
               -> LispStruct (LispVal e n) tps'
               -> m [e BoolType]
      eqStruct (LSingleton (Val x)) (LSingleton (Val y)) = do
        e <- [expr| (= x y) |]
        return [e]
      eqStruct (LStruct xs) (LStruct ys) = eqStructArgs xs ys
      eqStructArgs :: Embed m e
                   => StructArgs (LispVal e n) tps'
                   -> StructArgs (LispVal e n) tps'
                   -> m [e BoolType]
      eqStructArgs NoSArg NoSArg = return []
      eqStructArgs (SArg x xs) (SArg y ys) = do
        e <- eqStruct x y
        es <- eqStructArgs xs ys
        return (e++es)

instance (KnownNat lvl,GetStructType tps) => LiftComp (LispValue '(lvl,tps)) where
  type Unpacked (LispValue '(lvl,tps)) = LispUVal '(lvl,tps)
  liftComp (LispU str) = do
    str' <- liftStruct str
    return $ LispValue { size = NoSize
                       , value = str' }
  liftComp (LispUArray xs) = do
    xs' <- mapM liftComp xs
    liftValues xs'
  unliftComp f (val :: LispValue '(lvl,tp) e) = case natPred (Proxy::Proxy lvl) of
    NoPred -> do
      str <- extractStruct f (value val)
      return $ LispU str
    Pred _ -> do
      vals <- unliftValue f val
      vals' <- mapM (unliftComp f) vals
      return $ LispUArray vals'

instance (KnownNat lvl,GetStructType tps) => PartialComp (LispValue '(lvl,tps)) where
  type Partial (LispValue '(lvl,tps)) = LispPVal '(lvl,tps)
  maskValue _ (LispP str) xs = let (str',xs') = maskStruct str xs
                               in (LispP str',xs')
    where
      maskStruct :: LispStruct PValue tps' -> [Bool] -> (LispStruct PValue tps',[Bool])
      maskStruct (LSingleton NoPValue) (_:xs) = (LSingleton NoPValue,xs)
      maskStruct (LSingleton (PValue _)) (False:xs) = (LSingleton NoPValue,xs)
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
  unmaskValue _ (LispU xs) = LispP $ mapLispStruct (const PValue) xs
  unmaskValue pr (LispUArray xs) = case pr of
    (_::Proxy (LispValue '(S lvl',tp)))
      -> LispPArray (fmap (unmaskValue (Proxy::Proxy (LispValue '(lvl',tp)))) xs)
  assignPartial f val (LispP str) = assignStruct f (value val) str
    where
      assignStruct :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
                   -> LispStruct (LispVal e Z) tps'
                   -> LispStruct PValue tps'
                   -> m [Maybe p]
      assignStruct f (LSingleton (Val x)) (LSingleton (PValue val)) = do
        r <- f x val
        return [Just r]
      assignStruct _ _ (LSingleton NoPValue) = return [Nothing]
      assignStruct f (LStruct xs) (LStruct ys) = assignStructs f xs ys

      assignStructs :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
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

indexValue :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
           -> Integer
           -> LispValue '(S lvl,tps) e
           -> m (p,LispValue '(lvl,tps) e)
indexValue f x val = do
  let idx = IntValueC x
  (res,sz) <- indexSize f idx (size val)
  nval <- indexValue' f idx (value val)
  return (res,LispValue sz nval)
  where
    indexSize :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
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

    indexValue' :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
                -> ConcreteValue IntType
                -> LispStruct (LispVal e (S lvl)) tps
                -> m (LispStruct (LispVal e lvl) tps)
    indexValue' f n = mapLispStructM
                      (\_ ((Val x)::LispVal e (S lvl) tp)
                       -> case deriveLispTypeCtx' (Proxy::Proxy lvl)
                                                  (Proxy::Proxy tp) of
                          Dict -> do
                            n' <- embedConst n
                            x' <- [expr| (select x n') |]
                            return $ Val x')

extractStruct :: Monad m => (forall t. GetType t => e t -> m (ConcreteValue t))
              -> LispStruct (LispVal e Z) tps
              -> m (LispStruct ConcreteValue tps)
extractStruct f = mapLispStructM (\_ (Val x) -> f x)

unliftValue :: Embed m e => (forall t. GetType t => e t -> m (ConcreteValue t))
            -> LispValue '(S lvl,tps) e
            -> m [LispValue '(lvl,tps) e]
unliftValue f val = do
  szs <- unliftSize f (size val)
  vals <- unliftStruct f szs (value val)
  return $ zipWith LispValue szs vals

unliftStruct :: Embed m e => (forall t. GetType t => e t -> m (ConcreteValue t))
             -> [Size e lvl]
             -> LispStruct (LispVal e (S lvl)) tps
             -> m [LispStruct (LispVal e lvl) tps]
unliftStruct f szs (LSingleton (Val x :: LispVal e (S lvl) tp))
  = case deriveLispTypeCtx' (Proxy::Proxy lvl) (Proxy::Proxy tp) of
      Dict -> mapM (\(idx,sz) -> do
                       idx' <- embedConst $ IntValueC idx
                       el <- [expr| (select x idx') |]
                       return $ LSingleton (Val el)
                   ) (zip [0..] szs)
unliftStruct f szs (LStruct vals) = do
  vals' <- unliftStructs f szs vals
  return $ fmap LStruct vals'

unliftStructs :: Embed m e => (forall t. GetType t => e t -> m (ConcreteValue t))
              -> [Size e lvl]
              -> StructArgs (LispVal e (S lvl)) tps
              -> m [StructArgs (LispVal e lvl) tps]
unliftStructs f szs NoSArg = return $ fmap (const NoSArg) szs
unliftStructs f szs (SArg x xs) = do
  x' <- unliftStruct f szs x
  xs' <- unliftStructs f szs xs
  return $ zipWith SArg x' xs'

deriveLispTypeCtx' :: GetType (LispType (S lvl) t) => Proxy lvl -> Proxy t
                   -> Dict (GetType (LispType lvl t))
deriveLispTypeCtx' (_::Proxy lvl) (_::Proxy t)
  = case getType :: Repr (LispType (S lvl) t) of
      ArrayRepr (Arg IntRepr NoArg) repr -> Dict

unliftSize :: Embed m e => (forall t. GetType t => e t -> m (ConcreteValue t))
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

liftValues :: Embed m e => [LispValue '(lvl,tp) e]
           -> m (LispValue '(S lvl,tp) e)
liftValues xs = do
  sz <- liftSizes (fmap size xs)
  val <- liftStructs (fmap value xs)
  return $ LispValue sz val

liftSizes :: Embed m e => [Size e lvl] -> m (Size e (S lvl))
liftSizes xs = liftSizes' (genericLength xs) xs

liftSizes' :: Embed m e => Integer -> [Size e lvl] -> m (Size e (S lvl))
liftSizes' len xs@(x:_) = case x of
  NoSize -> do
    sz <- embedConst (IntValueC len)
    return $ Size sz NoSize
  Size _ (_::Size e lvl') -> do
    sz <- liftSizeArr (Proxy::Proxy lvl') (fmap (\(Size x _) -> x) xs)
    szs <- liftSizes' len (fmap (\(Size _ r) -> r) xs)
    return $ Size sz szs
  where
    liftSizeArr :: (Embed m e,KnownNat n,GetType (LispType n IntType))
                => Proxy n
                -> [e (LispType n IntType)]
                -> m (e (LispType (S n) IntType))
    liftSizeArr lvl lst = do
      c <- embedConst (IntValueC 0)
      arr <- leveledConst lvl c
      listArray arr lst

liftStruct :: Embed m e
           => LispStruct ConcreteValue tps
           -> m (LispStruct (LispVal e Z) tps)
liftStruct = mapLispStructM (const $ fmap Val . embedConst)

liftStructs :: Embed m e
            => [LispStruct (LispVal e lvl) tp]
            -> m (LispStruct (LispVal e (S lvl)) tp)
liftStructs xs@(x:_) = case x of
  LSingleton _ -> fmap LSingleton $ liftVal (fmap (\(LSingleton x) -> x) xs)
  LStruct _ -> fmap LStruct (liftStructs' (fmap (\(LStruct x) -> x) xs))
  where
    liftStructs' :: Embed m e
                 => [StructArgs (LispVal e lvl) tp]
                 -> m (StructArgs (LispVal e (S lvl)) tp)
    liftStructs' (NoSArg:_) = return NoSArg
    liftStructs' xs@(SArg _ _:_) = do
      y <- liftStructs $ fmap (\(SArg x _) -> x) xs
      ys <- liftStructs' $ fmap (\(SArg _ x) -> x) xs
      return $ SArg y ys

liftVal :: Embed m e => [LispVal e lvl tp] -> m (LispVal e (S lvl) tp)
liftVal xs@(Val _:_) = fmap Val $ listArray' (fmap (\(Val x) -> x) xs)

deriveLispTypeCtx :: (KnownNat lvl,GetType tp) => Proxy lvl -> Proxy tp
                  -> Dict (GetType (LispType lvl tp))
deriveLispTypeCtx pr repr = case natPred pr of
  NoPred -> Dict
  Pred n -> case deriveLispTypeCtx n repr of
    Dict -> Dict

leveledConst :: (Embed m e,KnownNat lvl,GetType t)
             => Proxy lvl -> e t -> m (e (LispType lvl t))
leveledConst lvl (c::e t) = case natPred lvl of
  NoPred -> return c
  Pred lvl' -> case deriveLispTypeCtx lvl' (Proxy::Proxy t) of
    Dict -> do
      x <- leveledConst lvl' c
      embed $ App ConstArray (Arg x NoArg)

listArray' :: (Embed m e,GetType t) => [e t] -> m (e (ArrayType '[IntType] t))
listArray' (xs::[e t]) = do
  c <- embedConst $ defaultValue (Proxy::Proxy t)
  listArray c xs
  where
    defaultValue :: GetType t => Proxy t -> ConcreteValue t
    defaultValue (_::Proxy t) = case getType :: Repr t of
      BoolRepr -> BoolValueC False
      IntRepr -> IntValueC 0
      RealRepr -> RealValueC 0
      BitVecRepr _ -> BitVecValueC 0

listArray :: (Embed m e,GetType t) => e t -> [e t]
          -> m (e (ArrayType '[IntType] t))
listArray def els = do
  arr <- embed $ App ConstArray (Arg def NoArg)
  (arr',_) <- foldlM (\(arr,n) x -> do
                         i <- embedConst (IntValueC n)
                         arr' <- [expr| (store arr x i) |]
                         return (arr',n+1)
                     ) (arr,0) els
  return arr'

mapLispStruct :: (forall t. GetType t => LispIndex tp t -> e t -> e' t)
              -> LispStruct e tp
              -> LispStruct e' tp
mapLispStruct f = runIdentity . mapLispStructM (\i e -> return $ f i e)

mapLispStructM :: Monad m => (forall t. GetType t => LispIndex tp t -> e t -> m (e' t))
               -> LispStruct e tp
               -> m (LispStruct e' tp)
mapLispStructM f (LSingleton x) = fmap LSingleton (f ValGet x)
mapLispStructM f (LStruct xs) = do
  xs' <- mapStructArgsM (\p str -> mapLispStructM (\i e -> f (ValIdx p i) e) str
                        ) xs
  return (LStruct xs')

mapStructArgsM :: Monad m
               => (forall t n. (KnownNat n,IndexableStruct tps n)
                   => Proxy n -> LispStruct e (Idx tps n)
                              -> m (LispStruct e' (Idx tps n)))
               -> StructArgs e tps
               -> m (StructArgs e' tps)
mapStructArgsM f NoSArg = return NoSArg
mapStructArgsM f (SArg x xs) = do
  x' <- f (Proxy::Proxy Z) x
  xs' <- mapStructArgsM (\(_::Proxy n) str -> f (Proxy::Proxy (S n)) str
                        ) xs
  return $ SArg x' xs'

{-class (SMTValue (ValueType (ResultType t)) (ResultType t))
      => Indexable (t::Type) (i::Type) where
  type ResultType t :: Type
  canIndex :: Proxy t -> Bool
  index :: (forall p. (Indexable p i,ResultType p ~ ResultType t) => SMTExpr b p -> (a,SMTExpr b p))
        -> SMTExpr b t -> i -> (a,SMTExpr b t)
  deref :: i -> SMTExpr b t -> SMTExpr b (ResultType t)
  derefConst :: Proxy i -> t -> ResultType t
  reref :: i -> SMTExpr b (ResultType t) -> SMTExpr b t
  recIndexable :: t -> i -> Dict (Indexable (ResultType t) i,
                                  ResultType (ResultType t) ~ ResultType t)

instance Indexable IntType i where
  type ResultType IntType = IntType
  canIndex _ = False
  index _ _ _ = error "Cannot index integer type."
  deref _ = id
  derefConst _ = id
  reref _ = id
  recIndexable _ _ = Dict

instance Indexable BoolType i where
  type ResultType BoolType = BoolType
  canIndex _ = False
  index _ _ _ = error "Cannot index bool type."
  deref _ = id
  derefConst _ = id
  reref _ = id
  recIndexable _ _ = Dict

instance (Indexable a i,Liftable i,Unit (ArgAnnotation i)) => Indexable (SMTArray i a) i where
  type ResultType (SMTArray i a) = ResultType a
  canIndex _ = True
  index f arr idx = let (res,el) = f (select arr idx)
                    in (res,store arr idx el)
  deref _ _ = error "Cannot deref array type."
  derefConst _ _ = error "Cannot deref array type."
  reref _ _ = error "Cannot reref array type."
  recIndexable (_::SMTArray i a) ui = case recIndexable (undefined::a) ui of
    Dict -> Dict

data LispVal = forall t. Indexable t (SMTExpr Integer) => Val (SMTExpr t) deriving (Typeable)

data Size = Size { sizeElements :: [SizeElement] } deriving (Typeable,Show)

data SizeElement = forall t. (Indexable t (SMTExpr Integer),ResultType t ~ Integer)
                   => SizeElement (SMTExpr t)
                 deriving (Typeable)

data LispValue = LispValue { size :: Size
                           , value :: LispStruct LispVal }
                 deriving (Eq,Ord,Show,Typeable)

data LispType = LispType { typeLevel :: Integer
                         , typeBase :: LispStruct Sort }
                deriving (Eq,Ord,Show,Typeable)

data LispUValue = forall a. (Indexable a (SMTExpr Integer),
                             ResultType a ~ a,
                             Unit (SMTAnnotation a)) => LispUValue a
                | LispUArray [LispUValue]

data LispPValue = LispPEmpty
                | forall a. (Indexable a (SMTExpr Integer),
                             ResultType a ~ a,
                             Unit (SMTAnnotation a)) => LispPValue a
                | LispPArray [LispPValue]

data LispRev = SizeSpec Integer
             | ElementSpec [Integer]
             deriving (Eq,Ord,Show,Typeable)

boolType :: LispType
boolType = LispType 0 (Singleton (Fix BoolSort))

intType :: LispType
intType = LispType 0 (Singleton (Fix IntSort))

indexType :: LispType -> [Integer] -> Sort
indexType (LispType n tp) = indexType' tp
  where
    indexType' (Singleton s) [] = foldl (\cs _ -> Fix (ArraySort [Fix IntSort] cs)) s [1..n]
    indexType' (Struct tps) (i:is) = indexType' (tps `genericIndex` i) is

argITE :: Args arg => SMTExpr Bool -> arg -> arg -> arg
argITE cond x y = res
  where
    x' = fromArgs x
    y' = fromArgs y
    ites = zipWith (\x y -> entype (\x' -> UntypedExpr $ ite cond x' (castUntypedExpr y)) x
                   ) x' y'
    Just (res,[]) = toArgs (extractArgAnnotation x) ites

zipStruct :: (a -> b -> c) -> LispStruct a -> LispStruct b -> LispStruct c
zipStruct f (Singleton x) (Singleton y) = Singleton (f x y)
zipStruct f (Struct xs) (Struct ys) = Struct (zipWith (zipStruct f) xs ys)

linearizeStruct :: LispStruct a -> [a]
linearizeStruct (Singleton x) = [x]
linearizeStruct (Struct xs) = concat $ fmap linearizeStruct xs

accessStruct :: (a -> (b,a)) -> [Integer] -> LispStruct a -> (b,LispStruct a)
accessStruct f [] (Singleton x) = (res,Singleton nx)
  where
    (res,nx) = f x
accessStruct f (i:is) (Struct xs) = (res,Struct nxs)
  where
    (res,nxs) = modify i xs
    modify 0 (x:xs) = let (res,nx) = accessStruct f is x
                      in (res,nx:xs)
    modify n (x:xs) = let (res,nxs) = modify (n-1) xs
                      in (res,x:nxs)

accessValue :: (forall t. Indexable t (SMTExpr Integer) => SMTExpr t -> (a,SMTExpr t))
                  -> [Integer] -> [SMTExpr Integer] -> LispValue -> (a,LispValue)
accessValue f fields idx v@(LispValue sz val)
  = (res,LispValue sz nval)
  where
    (res,nval) = accessStruct (\(Val x) -> let (res,nx) = derefVal f x idx
                                           in (res,Val nx)) fields val

derefVal :: Indexable t (SMTExpr Integer)
            => (forall t. Indexable t (SMTExpr Integer)
                => SMTExpr t -> (a,SMTExpr t)) -> SMTExpr t
            -> [SMTExpr Integer] -> (a,SMTExpr t)
derefVal f val [] = f val
derefVal f val (i:is) = index (\e -> derefVal f e is) val i

accessSize :: (SMTExpr Integer -> (a,SMTExpr Integer)) -> [SMTExpr Integer] -> LispValue
           -> (a,LispValue)
accessSize f idx (LispValue (Size els) val) = (res,LispValue (Size nels) val)
  where
    (res,nels) = accessEls idx els
    accessEls [] (SizeElement e:es) = let (res,ne) = accessEl f idx e
                                      in (res,SizeElement ne:es)
    accessEls (_:is) (e:es) = let (res,nes) = accessEls is es
                              in (res,e:nes)
    accessEl :: (Indexable t (SMTExpr Integer),
                 ResultType t ~ Integer)
             => (SMTExpr Integer -> (a,SMTExpr Integer))
             -> [SMTExpr Integer] -> SMTExpr t
             -> (a,SMTExpr t)
    accessEl f [] e = let (res,ne) = f (deref (undefined::SMTExpr Integer) e)
                      in (res,reref (undefined::SMTExpr Integer) ne)
    accessEl f (i:is) e = index (accessEl f is) e i

accessSizeArr :: (forall t. (Indexable t (SMTExpr Integer),ResultType t ~ Integer)
                  => SMTExpr t -> (a,SMTExpr t))
              -> Integer -> LispValue -> (a,LispValue)
accessSizeArr f n (LispValue (Size szs) els) = (res,LispValue (Size nszs) els)
  where
    (res,nszs) = accessArr n szs
    accessArr 0 (SizeElement e:es) = let (res,ne) = f e
                                     in (res,SizeElement ne:es)
    accessArr n (e:es) = let (res,nes) = accessArr (n-1) es
                         in (res,e:nes)

instance Eq Size where
  Size xs == Size ys = and $ zipWith (\(SizeElement e1) (SizeElement e2)
                                      -> case cast e2 of
                                          Just e2' -> e1==e2'
                                          Nothing -> False
                                     ) xs ys

instance Ord Size where
  compare (Size xs) (Size ys) = compare' xs ys
    where
      compare' :: [SizeElement] -> [SizeElement] -> Ordering
      compare' [] [] = EQ
      compare' (SizeElement x:xs) (SizeElement y:ys) = case compareExprs x y of
        EQ -> compare' xs ys
        r -> r
      compare' [] _ = LT
      compare' _ [] = GT

instance Show SizeElement where
  show (SizeElement e) = show e

instance Eq LispVal where
  Val e1 == Val e2 = case compareExprs e1 e2 of
    EQ -> True
    _ -> False

instance Ord LispVal where
  compare (Val e1) (Val e2) = compareExprs e1 e2

instance Show LispVal where
  showsPrec p (Val expr) = showsPrec p expr

withLeveledArray :: (Indexable t i,ResultType t ~ t,Liftable i,Unit (ArgAnnotation i))
                 => t -> i -> Integer
                 -> (forall b. (Indexable b i,ResultType b ~ t) => b -> a)
                 -> a
withLeveledArray (_::t) (_::i) 0 f = f (undefined::t)
withLeveledArray ut (ui::i) n f
  = withLeveledArray ut ui (n-1) $
    \(_::p) -> f (undefined::SMTArray i p)

{-instance Args Size where
  type ArgAnnotation Size = Integer
  foldExprs f s ~(Size els) n = do
    (ns,nels) <- fold s els 0 n
    return (ns,Size nels)
    where
      fold s _ _ 0 = return (s,[])
      fold s ~(x:xs) i n = withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) i
                           (\(_::t) -> do
                               (s1,nx) <- f s (case x of
                                                SizeElement x -> case cast x of
                                                  Just x -> x) unit
                               (s2,nxs) <- fold s1 xs (i+1) (n-1)
                               return (s2,SizeElement (nx::SMTExpr t):nxs))
  foldsExprs f s lst n = do
    (ns,nlst,nel) <- fold s lst' 0 n
    return (ns,fmap Size nlst,Size nel)
    where
      lst' = fmap (\(Size x,b) -> (x,b)) lst
      fold s lst _ 0 = return (s,fmap (const []) lst,[])
      fold s lst i n = withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) i $
                       \(_::t) -> do
                         let heads = fmap (\(x,b) -> (case head x of
                                                       SizeElement x -> case cast x of
                                                         Just x -> x,b)) lst
                             tails = fmap (\(x,b) -> (tail x,b)) lst
                         (s1,nheads,nhead) <- f s heads unit
                         (s2,ntails,ntail) <- fold s1 tails (i+1) (n-1)
                         return (s2,zipWith (\nhead ntail -> SizeElement (nhead::SMTExpr t):ntail)
                                    nheads ntails,SizeElement nhead:ntail)
  extractArgAnnotation (Size els) = genericLength els
  toArgs n els = do
    (sz,rest) <- toArgs' 0 n els
    return (Size sz,rest)
    where
      toArgs' :: Integer -> Integer -> [SMTExpr Untyped] -> Maybe ([SizeElement],[SMTExpr Untyped])
      toArgs' _ 0 els = return ([],els)
      toArgs' i n (e:es) = withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) i $
                           \(_::t) -> do
                             (els,rest) <- toArgs' (i+1) (n-1) es
                             return (SizeElement (castUntypedExpr e::SMTExpr t):els,rest)
  fromArgs (Size els) = fmap (\(SizeElement x) -> UntypedExpr x) els
  getTypes _ n = [ withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) i $
                   \ut -> ProxyArg ut unit
                 | i <- [0..n-1] ]
  getArgAnnotation _ sorts = (genericLength sorts,[])-}

withIndexableSort :: i -> Sort -> (forall t. (Indexable t i,
                                              ResultType t ~ t,
                                              Unit (SMTAnnotation (ResultType t))
                                             ) => t -> a) -> a
withIndexableSort _ (Fix BoolSort) f = f (undefined::Bool)
withIndexableSort _ (Fix IntSort) f = f (undefined::Integer)

foldExprsWithIndex :: Monad m => (forall t. SMTType t => s -> LispRev -> SMTExpr t -> m (s,SMTExpr t))
                   -> s -> LispValue -> m (s,LispValue)
foldExprsWithIndex f s (LispValue (Size szs) els) = do
  (s1,nszs) <- foldSize s (0::Integer) szs
  (s2,nels) <- foldStruct s1 [] els
  return (s2,LispValue (Size nszs) nels)
  where
    foldSize s _ [] = return (s,[])
    foldSize s i (SizeElement e:es) = do
      (s1,ne) <- f s (SizeSpec i) e
      (s2,nes) <- foldSize s1 (i+1) es
      return (s2,SizeElement ne:nes)
    foldStruct s idx (Singleton (Val e)) = do
      (ns,ne) <- f s (ElementSpec idx) e
      return (ns,Singleton (Val ne))
    foldStruct s idx (Struct es) = do
      (ns,nes) <- foldStructs s 0 idx es
      return (ns,Struct nes)
    foldStructs s _ _ [] = return (s,[])
    foldStructs s i idx (e:es) = do
      (s1,ne) <- foldStruct s (idx++[i]) e
      (s2,nes) <- foldStructs s1 (i+1) idx es
      return (s2,ne:nes)

foldTypeWithIndex :: (forall t. (SMTType t,Unit (SMTAnnotation t))
                      => s -> LispRev -> t -> s)
                  -> s -> LispType -> s
foldTypeWithIndex f s (LispType lvl tp) = s2
  where
    s1 = foldl (\s n -> withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) n $
                        \ut -> f s (SizeSpec n) ut
               ) s [0..lvl-1]
    s2 = foldStruct s1 [] tp
    foldStruct s idx (Singleton sort)
      = withIndexableSort (undefined::SMTExpr Integer) sort $
        \ut -> withLeveledArray ut (undefined::SMTExpr Integer) lvl $
               \uarr -> f s (ElementSpec idx) uarr
    foldStruct s idx (Struct tps)
      = fst $ foldl (\(s,i) tp -> (foldStruct s (idx++[i]) tp,i+1)
                    ) (s,0::Integer) tps

foldStruct :: Monad m => (s -> a -> b -> m (s,a))
           -> s -> LispStruct a -> LispStruct b
           -> m (s,LispStruct a)
foldStruct f s ~(Singleton x) (Singleton y) = do
  (ns,nx) <- f s x y
  return (ns,Singleton nx)
foldStruct f s ~(Struct xs) (Struct ys) = do
  (ns,nxs) <- foldStruct' s xs ys
  return (ns,Struct nxs)
  where
    foldStruct' s _ [] = return (s,[])
    foldStruct' s ~(x:xs) (y:ys) = do
      (s1,nx) <- foldStruct f s x y
      (s2,nxs) <- foldStruct' s1 xs ys
      return (s2,nx:nxs)

foldsStruct :: (Monad m,Show a,Show b)
            => (s -> [(a,c)] -> b -> m (s,[a],a))
            -> s -> [(LispStruct a,c)] -> LispStruct b
            -> m (s,[LispStruct a],LispStruct a)
foldsStruct f s lst (Singleton x) = do
  (ns,nlst,res) <- f s (fmap (\(Singleton y,b) -> (y,b)) lst) x
  return (ns,fmap Singleton nlst,Singleton res)
foldsStruct f s lst (Struct xs) = do
  (ns,nys,res) <- foldsStruct' s (fmap (\(Struct ys,b) -> (ys,b)) lst) xs
  return (ns,fmap Struct nys,Struct res)
  where
    foldsStruct' s lst [] = return (s,fmap (const []) lst,[])
    foldsStruct' s lst (x:xs) = do
      (s1,ny,res) <- foldsStruct f s (fmap (\(~(y:ys),b) -> (y,b)) lst) x
      (s2,nys,ress) <- foldsStruct' s1 (fmap (\(~(y:ys),b) -> (ys,b)) lst) xs
      return (s2,zipWith (:) ny nys,res:ress)

toArgsStruct :: (b -> [SMTExpr Untyped] -> Maybe (a,[SMTExpr Untyped]))
             -> LispStruct b
             -> [SMTExpr Untyped]
             -> Maybe (LispStruct a,[SMTExpr Untyped])
toArgsStruct f (Singleton x) es = do
  (y,rest) <- f x es
  return (Singleton y,rest)
toArgsStruct f (Struct xs) es = do
  (ys,rest) <- toArgs' xs es
  return (Struct ys,rest)
  where
    toArgs' [] es = return ([],es)
    toArgs' (x:xs) es = do
      (y,es1) <- toArgsStruct f x es
      (ys,es2) <- toArgs' xs es1
      return (y:ys,es2)

getTypesStruct :: (a -> [ProxyArg]) -> LispStruct a
               -> [ProxyArg]
getTypesStruct f (Singleton x) = f x
getTypesStruct f (Struct xs) = concat $ fmap (getTypesStruct f) xs

foldLispVal :: Monad m => Integer
            -> (forall t. SMTType t => s -> SMTExpr t -> SMTAnnotation t -> m (s,SMTExpr t))
            -> s -> LispVal -> Sort
            -> m (s,LispVal)
foldLispVal lvl f s val sort
  = withIndexableSort (undefined::SMTExpr Integer) sort $
    \ut -> withLeveledArray ut (undefined::SMTExpr Integer) lvl $
           \(_::t) -> do
             (ns,ne) <- f s (case val of
                              Val e -> case cast e of
                                Just e' -> e') unit
             return (ns,Val (ne::SMTExpr t))

foldsLispVal :: Monad m => Integer
             -> (forall t. SMTType t => s -> [(SMTExpr t,b)] -> SMTAnnotation t
                 -> m (s,[SMTExpr t],SMTExpr t))
             -> s -> [(LispVal,b)] -> Sort
             -> m (s,[LispVal],LispVal)
foldsLispVal lvl f s lst sort
  = withIndexableSort (undefined::SMTExpr Integer) sort $
    \ut -> withLeveledArray ut (undefined::SMTExpr Integer) lvl $
           \(_::t) -> do
             (ns,nlst,res) <- f s (fmap (\(Val e,b) -> (case cast e of
                                                         Just e' -> e',b)) lst) unit
             return (ns,fmap Val nlst,Val (res::SMTExpr t))

toArgsLispVal :: Integer -> Sort -> [SMTExpr Untyped] -> Maybe (LispVal,[SMTExpr Untyped])
toArgsLispVal _ _ [] = Nothing
toArgsLispVal lvl sort (e:es)
  = withIndexableSort (undefined::SMTExpr Integer) sort $
    \ut -> withLeveledArray ut (undefined::SMTExpr Integer) lvl $
           \(_::t) -> return (Val (castUntypedExpr e::SMTExpr t),es)

getTypesLispVal :: Integer -> Sort -> [ProxyArg]
getTypesLispVal lvl sort
  = withIndexableSort (undefined::SMTExpr Integer) sort $
    \ut -> withLeveledArray ut (undefined::SMTExpr Integer) lvl $
           \ut -> [ProxyArg ut unit]

valueEq :: LispValue -> LispValue -> SMTExpr Bool
valueEq (LispValue (Size sz1) val1) (LispValue (Size sz2) val2)
  = app and' (szEq++valEq)
  where
    szEq = zipWith (\(SizeElement e1) (SizeElement e2) -> case cast e2 of
                     Just e2' -> e1 .==. e2') sz1 sz2
    valEq = linearizeStruct $ zipStruct (\(Val e1) (Val e2) -> case cast e2 of
                                          Just e2' -> e1 .==. e2'
                                        ) val1 val2

{-instance Args LispValue where
  type ArgAnnotation LispValue = LispType
  foldExprs f s ~(LispValue sz struct) (LispType lvl tp) = do
    (s1,nsz) <- foldExprs f s sz lvl
    (s2,nstruct) <- foldStruct (foldLispVal lvl f) s1 struct tp
    return (s2,LispValue nsz nstruct)
  foldsExprs f s lst (LispType lvl tp) = do
    let sizes = fmap (\(val,b) -> (case val of
                                    LispValue sz _ -> sz,b)) lst
        structs = fmap (\(val,b) -> (case val of
                                      LispValue _ str -> str,b)) lst
    (s1,nsizes,nsize) <- foldsExprs f s sizes lvl
    (s2,nstructs,nstruct) <- foldsStruct (foldsLispVal lvl f) s1 structs tp
    return (s2,zipWith LispValue nsizes nstructs,LispValue nsize nstruct)
  extractArgAnnotation (LispValue sz struct)
    = LispType (extractArgAnnotation sz) (extractStruct struct)
    where
      extractStruct (Singleton (Val (expr::SMTExpr t)))
        = let sort = getSort (undefined::t) (extractAnnotation expr)
          in Singleton $ stripSort sort
      extractStruct (Struct vals) = Struct $ fmap extractStruct vals
      stripSort (Fix (ArraySort _ el)) = stripSort el
      stripSort sort = sort
  toArgs (LispType lvl tp) es = do
    (sz,es1) <- toArgs lvl es
    (val,es2) <- toArgsStruct (toArgsLispVal lvl) tp es1
    return (LispValue sz val,es2)
  fromArgs (LispValue sz val) = fromArgs sz++fromStruct val
    where
      fromStruct (Singleton (Val expr)) = [UntypedExpr expr]
      fromStruct (Struct vals) = concat $ fmap fromStruct vals
  getTypes _ (LispType sz tp) = getTypes (undefined::Size) sz++
                                getTypesStruct (getTypesLispVal sz) tp

instance LiftArgs LispValue where
  type Unpacked LispValue = LispStruct LispUValue
  liftArgs val (LispType lvl tp) = LispValue (Size $ getSize lvl $ anySingleton val)
                                   (getValue val tp)
    where
      anySingleton (Singleton x) = x
      anySingleton (Struct xs) = anySingleton $ head xs
      getSize 0 (LispUValue _) = []
      getSize lvl (LispUArray vals)
        = let sz = SizeElement $ constant (genericLength vals::Integer)
              szs = snd $ foldl (\(p,cur) el
                                 -> (p+1,assemble p 0 cur (getSize (lvl-1) el))
                                ) (0,[ zeroArr (undefined::SMTExpr Integer) (undefined::Integer)
                                       n SizeElement | n <- [1..lvl-1] ]) vals
          in sz:szs
      assemble :: Integer -> Integer -> [SizeElement] -> [SizeElement] -> [SizeElement]
      assemble p i (SizeElement arr:arrs) (SizeElement sz:szs)
        = withLeveledArray (undefined::Integer) (undefined::SMTExpr Integer) i $
          \(_::t) -> case cast sz of
                      Just rsz -> case cast arr of
                        Just rarr -> SizeElement (store rarr (constant (p::Integer))
                                                  (rsz::SMTExpr t)):
                                     assemble p (i+1) arrs szs
      assemble _ _ [] [] = []
      getValue (Struct vals) (Struct tps) = Struct (zipWith getValue vals tps)
      getValue (Singleton val) (Singleton tp)
        = withIndexableSort (undefined::SMTExpr Integer) tp $
          \ut -> zeroArr (undefined::SMTExpr Integer) ut lvl $
                 \arr -> Singleton (Val (getValue' arr val))
      getValue' :: (Indexable t (SMTExpr Integer),
                    Unit (SMTAnnotation (ResultType t))) => SMTExpr t -> LispUValue -> SMTExpr t
      getValue' arr (LispUValue expr) = case cast (constant expr) of
        Just expr' -> reref (undefined::SMTExpr Integer) expr'
      getValue' arr (LispUArray vals)
        = fst $ foldl (\(arr,i) val -> (snd $ index (\e -> (undefined,getValue' e val))
                                        arr (constant i),i+1)
                      ) (arr,0::Integer) vals
      zeroArr :: (Indexable t i,ResultType t ~ t,
                  Liftable i,Unit (ArgAnnotation i))
                 => i -> t -> Integer
                 -> (forall a. (Indexable a i,
                                ResultType a ~ t) => SMTExpr a -> b) -> b
      zeroArr (_::i) (_::t) 0 f
        = f (defaultExpr unit::SMTExpr t)
      zeroArr (ui::i) (ut::t) i f
        = zeroArr ui ut (i-1) $
          \(arr::SMTExpr u) -> f (constArray arr unit
                                  ::SMTExpr (SMTArray i u))
  unliftArgs (LispValue (Size sz) val) f = unlift' val
    where
      unlift' (Struct vals) = do
        vals' <- mapM unlift' vals
        return (Struct vals')
      unlift' (Singleton (Val arr)) = do
        res <- unliftArr f sz arr
        return (Singleton res)

      unliftArr :: (Indexable t (SMTExpr Integer),
                    Monad m) => (forall a. SMTValue a => SMTExpr a -> m a)
                -> [SizeElement] -> SMTExpr t -> m LispUValue
      unliftArr f [] (arr::SMTExpr t) = case recIndexable (undefined::t)
                                             (undefined::SMTExpr Integer) of
        Dict -> do
          res <- f (deref (undefined::SMTExpr Integer) arr)
          return $ LispUValue res
      unliftArr f (SizeElement x:xs) arr = do
        sz <- f (deref (undefined::SMTExpr Integer) x)
        els <- mapM (\i -> fst $ index
                           (\narr -> (do
                                         let nxs = fmap (\(SizeElement x)
                                                         -> fst $ index (\y -> (SizeElement y,y))
                                                            x (constant i)) xs
                                         unliftArr f nxs narr,narr)
                           ) arr (constant i)
                    ) [0..sz-1]
        return $ LispUArray els

instance PartialArgs LispValue where
  type PartialValue LispValue = LispStruct LispPValue
  maskValue u (Singleton val) mask = (Singleton nval,nmask)
    where
      (nval,nmask) = maskVal val mask
      maskVal :: LispPValue -> [Bool] -> (LispPValue,[Bool])
      maskVal (LispPArray vals) (_:mask)
        = let (nmask,nvals) = mapAccumL (\mask val -> let (nval,nmask) = maskVal val mask
                                                      in (nmask,nval)
                                        ) mask vals
          in (LispPArray nvals,nmask)
      maskVal (LispPValue val) (True:mask) = (LispPValue val,mask)
      maskVal (LispPValue _) (False:mask) = (LispPEmpty,mask)
      maskVal LispPEmpty (_:mask) = (LispPEmpty,mask)
  maskValue u (Struct vals) mask = (Struct nvals,nmask)
    where
      (nmask,nvals) = mapAccumL (\mask val -> let (nval,nmask) = maskValue u val mask
                                              in (nmask,nval)
                                ) mask vals
  unmaskValue u (Singleton val) = Singleton (unmask val)
    where
      unmask (LispUArray vals) = LispPArray (fmap unmask vals)
      unmask (LispUValue val) = LispPValue val
  unmaskValue u (Struct vals) = Struct $ fmap (unmaskValue u) vals
  assignPartial (LispValue (Size sz) val) part
    = assign val part
    where
      assign (Singleton (Val val)) (Singleton part) = assign' sz val part
      assign (Struct vals) (Struct parts) = concat $ zipWith assign vals parts
      assign' :: (SMTType t,Indexable t (SMTExpr Integer))
                 => [SizeElement] -> SMTExpr t -> LispPValue -> [Maybe (SMTExpr Bool)]
      assign' _ _ LispPEmpty = [Nothing]
      assign' [] val (LispPValue x) = case cast (constant x) of
        Just x' -> [Just (val .==. x')]
        Nothing -> error $ "Can't assign "++show val++" with "++show x
      assign' (SizeElement e:es) arr (LispPArray vals)
        = (Just $ (deref (undefined::SMTExpr Integer) e)
           .==. (constant $ genericLength vals)):
          [ res
          | (i,val) <- zip [0..] vals
          , res <- fst $ index
                   (\arr' -> (assign' (fmap (\(SizeElement e)
                                              -> fst $ index (\x -> (SizeElement x,x))
                                                 e (constant (i::Integer))
                                            ) es)
                              arr' val,arr'))
                   arr (constant (i::Integer)) ]-}

instance Show LispUValue where
  showsPrec p (LispUValue val) = showsPrec p val
  showsPrec p (LispUArray vals) = showList vals

instance Eq LispUValue where
  (LispUValue x) == (LispUValue y) = case cast y of
    Nothing -> False
    Just y' -> x==y'
  (LispUArray xs) == (LispUArray ys) = xs==ys
  _ == _ = False

instance Ord LispUValue where
  compare (LispUValue x) (LispUValue y) = case compare (typeOf x) (typeOf y) of
    EQ -> case cast y of
      Just y' -> compare x y'
    r -> r
  compare (LispUValue _) _ = LT
  compare _ (LispUValue _) = GT
  compare (LispUArray xs) (LispUArray ys) = compare xs ys

instance Show LispPValue where
  showsPrec p LispPEmpty = showChar '*'
  showsPrec p (LispPValue val) = showsPrec p val
  showsPrec p (LispPArray vals) = showList vals

instance Eq LispPValue where
  (==) LispPEmpty LispPEmpty = True
  (==) (LispPValue x) (LispPValue y) = case cast y of
    Just y' -> x==y'
    Nothing -> False
  (==) (LispPArray xs) (LispPArray ys) = xs==ys
  (==) _ _ = False

instance Show a => Show (LispStruct a) where
  showsPrec p (Struct ps) = showList ps
  showsPrec p (Singleton x) = showsPrec p x
-}
