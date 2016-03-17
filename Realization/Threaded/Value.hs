module Realization.Threaded.Value where

import Args

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Interface as I
import Data.Map (Map)
import qualified Data.Map as Map
import LLVM.FFI hiding (Type,Value,Vector,ArrayType,GetType,getType,Select,Store)
import Foreign.Ptr (Ptr)
import Data.Typeable
import Data.List (genericIndex)
import Data.Traversable
import Data.Foldable
import System.IO.Unsafe
import Data.Maybe (catMaybes)
import Prelude hiding (sequence,mapM)
import Data.GADT.Show
import Data.GADT.Compare
import Text.Show

data Struct a = Singleton { singleton :: a }
              | Struct { struct :: [Struct a] }
              deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

newtype CompositeStruct a (e :: Type -> *) = CompositeStruct (Struct (a e))

data RevStruct e (tp :: Type) where
  RevStruct :: [Int] -> e tp -> RevStruct e tp

data SymVal e = ValBool { valBool :: e BoolType }
              | ValInt { valInt :: e IntType }
              | forall bw. ValBounded { valBounded :: e (BitVecType bw) }
              | ValPtr { valPtr :: Map MemoryPtr (e BoolType,[e IntType])
                       , valPtrType :: !(Struct SymType) }
              | ValThreadId { valThreadId :: Map (Ptr CallInst) (e BoolType) }
              | ValCondition { valCondition :: Map (Maybe (Ptr CallInst)) (e BoolType) }
              | ValVector { valVector :: [SymVal e] }

data SymArray e = ArrBool { arrBool :: e (ArrayType '[IntType] BoolType) }
                | ArrInt { arrInt :: e (ArrayType '[IntType] IntType) }
                | forall bw. ArrBounded { arrBounded :: e (ArrayType '[IntType] (BitVecType bw)) }
                | ArrPtr { arrPtr :: Map MemoryPtr (e (ArrayType '[IntType] BoolType),
                                                    [e (ArrayType '[IntType] IntType)])
                         , arrPtrType :: Struct SymType }
                | ArrThreadId { arrThreadId :: Map (Ptr CallInst) (e (ArrayType '[IntType] BoolType)) }
                | ArrCondition { arrCondition :: Map (Maybe (Ptr CallInst)) (e (ArrayType '[IntType] BoolType)) }
                | ArrVector { arrVector :: [SymArray e] }

data SymType = TpBool
             | TpInt
             | forall bw. TpBounded { tpBoundedBitwidth :: Natural bw }
             | TpPtr { tpPtr :: Map MemoryPtr ()
                     , tpPtrType :: Struct SymType }
             | TpThreadId { tpThreadId :: Map (Ptr CallInst) () }
             | TpCondition { tpCondition :: Map (Maybe (Ptr CallInst)) () }
             | TpVector { tpVector :: [SymType] }
             deriving (Typeable)

data AllocVal e = ValStatic [Struct (SymVal e)]
                | ValDynamic (Struct (SymArray e)) (e IntType)

data AllocType = TpStatic Int (Struct SymType)
               | TpDynamic (Struct SymType)
               deriving (Eq,Ord,Show,Typeable)

type MemoryLoc = Either (Ptr Instruction) (Ptr GlobalVariable)

data MemoryTrg = AllocTrg (Ptr Instruction)
               | GlobalTrg (Ptr GlobalVariable)
               | LocalTrg (Ptr GlobalVariable)
               deriving (Eq,Ord,Show,Typeable)

data MemoryPtr = MemoryPtr { memoryLoc :: MemoryTrg
                           , offsetPattern :: [AccessPattern]
                           } deriving (Eq,Ord,Typeable)

data AccessPattern = StaticAccess Integer
                   | DynamicAccess
                   deriving (Eq,Ord,Typeable)

data MemoryAccessResult e a
  = Success a
  | Invalid
  | TypeError
  | CondAccess (e BoolType) (MemoryAccessResult e a) (MemoryAccessResult e a)

data RevValue tp where
  RevInt :: RevValue IntType
  RevBool :: RevValue BoolType
  RevBounded :: Natural bw -> RevValue (BitVecType bw)
  PtrCond :: MemoryPtr -> RevValue BoolType
  PtrIdx :: MemoryPtr -> Int -> RevValue IntType
  ThreadIdCond :: Ptr CallInst -> RevValue BoolType
  ConditionCond :: Maybe (Ptr CallInst) -> RevValue BoolType
  RevVector :: Int -> RevValue tp -> RevValue tp

data RevArray tp where
  RevArray :: RevValue tp -> RevArray (ArrayType '[IntType] tp)

data RevAlloc tp where
  RevStatic :: Int -> [Int] -> RevValue tp -> RevAlloc tp
  RevDynamic :: [Int] -> RevValue tp -> RevAlloc (ArrayType '[IntType] tp)
  RevSize :: RevAlloc IntType

instance GetType RevValue where
  getType RevInt = int
  getType (RevBounded bw) = bitvec bw
  getType RevBool = bool
  getType (PtrCond _) = bool
  getType (PtrIdx _ _) = int
  getType (ThreadIdCond _) = bool
  getType (ConditionCond _) = bool
  getType (RevVector _ rev) = getType rev

instance GetType RevArray where
  getType (RevArray rev) = array (List.list1 int) (getType rev)

instance GetType RevAlloc where
  getType (RevStatic _ _ rev) = getType rev
  getType (RevDynamic _ rev) = array (List.list1 int) (getType rev)
  getType RevSize = int

showAssoc :: (a -> ShowS) -> (b -> ShowS) -> Map a b -> ShowS
showAssoc f g mp = showListWith (\(x,y) -> f x . showString " ~> " . g y) (Map.toList mp)

symType :: GetType e => SymVal e -> SymType
symType (ValBool _) = TpBool
symType (ValInt _) = TpInt
symType (ValBounded e) = case getType e of
  BitVecRepr bw -> TpBounded bw
symType (ValPtr conds tp) = TpPtr (fmap (const ()) conds) tp
symType (ValThreadId conds) = TpThreadId (fmap (const ()) conds)
symType (ValCondition conds) = TpCondition (fmap (const ()) conds)
symType (ValVector vals) = TpVector (fmap symType vals)

symArrType :: GetType e => SymArray e -> SymType
symArrType (ArrBool _) = TpBool
symArrType (ArrInt _) = TpInt
symArrType (ArrBounded e) = case getType e of
  ArrayRepr _ (BitVecRepr bw) -> TpBounded bw
symArrType (ArrPtr mp tp) = TpPtr (fmap (const ()) mp) tp
symArrType (ArrThreadId mp) = TpThreadId (fmap (const ()) mp)
symArrType (ArrCondition mp) = TpCondition (fmap (const ()) mp)
symArrType (ArrVector arrs) = TpVector (fmap symArrType arrs)

typeIntersection :: SymType -> SymType -> Maybe SymType
typeIntersection TpBool TpBool = Just TpBool
typeIntersection TpInt TpInt = Just TpInt
typeIntersection (TpBounded bw1) (TpBounded bw2) = case geq bw1 bw2 of
  Just Refl -> Just (TpBounded bw1)
  Nothing -> Nothing
typeIntersection (TpPtr trg1 tp1) (TpPtr trg2 tp2) = do
  ntp <- sequence $ zipStruct typeIntersection tp1 tp2
  return $ TpPtr (Map.intersection trg1 trg2) ntp
typeIntersection (TpCondition t1) (TpCondition t2)
  = Just $ TpCondition (Map.intersection t1 t2)
typeIntersection (TpVector v1) (TpVector v2) = do
  ntps <- sequence $ zipWith typeIntersection v1 v2
  return $ TpVector ntps
typeIntersection _ _ = Nothing

typeUnion :: SymType -> SymType -> Maybe SymType
typeUnion TpBool TpBool = Just TpBool
typeUnion TpInt TpInt = Just TpInt
typeUnion (TpBounded bw1) (TpBounded bw2) = case geq bw1 bw2 of
  Just Refl -> Just (TpBounded bw1)
  Nothing -> Nothing
typeUnion (TpPtr trg1 tp1) (TpPtr trg2 tp2) = do
  ntp <- sequence $ zipStruct typeUnion tp1 tp2
  return $ TpPtr (Map.union trg1 trg2) ntp
typeUnion (TpCondition t1) (TpCondition t2)
  = Just $ TpCondition (Map.union t1 t2)
typeUnion (TpVector v1) (TpVector v2) = do
  ntps <- sequence $ zipWith typeUnion v1 v2
  return $ TpVector ntps
typeUnion (TpThreadId t1) (TpThreadId t2)
  = Just $ TpThreadId $ Map.union t1 t2
typeUnion _ _ = Nothing

zipStruct :: (a -> b -> c) -> Struct a -> Struct b -> Struct c
zipStruct f (Singleton x) (Singleton y) = Singleton (f x y)
zipStruct f (Struct xs) (Struct ys)
  = Struct (zipWith (zipStruct f) xs ys)

defaultConst :: SymType -> SymVal ConcreteValue
defaultConst TpBool = ValBool (BoolValueC False)
defaultConst TpInt = ValInt (IntValueC 0)
defaultConst (TpBounded bw) = ValBounded (BitVecValueC 0 bw)
defaultConst (TpPtr mp tp)
  = ValPtr (Map.mapWithKey (\trg _ -> (BoolValueC False,[IntValueC 0
                                                        | DynamicAccess <- offsetPattern trg ])
                           ) mp) tp
defaultConst (TpThreadId mp)
  = ValThreadId (fmap (const (BoolValueC False)) mp)
defaultConst (TpCondition mp)
  = ValCondition (fmap (const (BoolValueC False)) mp)
defaultConst (TpVector tps) = ValVector (fmap defaultConst tps)

defaultValue :: Embed m e => SymType -> m (SymVal e)
defaultValue tp = foldExprs (\_ -> embedConst) (defaultConst tp)

valEq :: (Embed m e,GetType e) => SymVal e -> SymVal e -> m (e BoolType)
valEq (ValBool x) (ValBool y) = embed $ x :==: y
valEq (ValInt x) (ValInt y) = embed $ x :==: y
valEq (ValBounded e1) (ValBounded e2) = case (getType e1,getType e2) of
  (BitVecRepr bw1,BitVecRepr bw2) -> case geq bw1 bw2 of
    Just Refl -> embed $ e1 :==: e2
valEq (ValPtr x _) (ValPtr y _) = do
  mp <- sequence $ Map.intersectionWith ptrEq x y
  case catMaybes $ Map.elems mp of
    [] -> embedConst (BoolValueC False)
    [x] -> return x
    xs -> embed $ OrLst xs
  where
    ptrEq (c1,i1) (c2,i2) = do
      conds <- idxEq i1 i2
      case conds of
        Just conds' -> do
          res <- embed $ AndLst (c1:c2:conds')
          return $ Just res
        Nothing -> return Nothing
    idxEq [] [] = return (Just [])
    idxEq (x:xs) (y:ys) = do
      rest <- idxEq xs ys
      case rest of
        Nothing -> return Nothing
        Just rest' -> do
          c <- embed $ x :==: y
          return $ Just (c:rest')
valEq (ValThreadId x) (ValThreadId y) = do
  mp <- sequence $ Map.intersectionWith condEq x y
  case Map.elems mp of
    [] -> embedConst (BoolValueC False)
    [x] -> return x
    xs -> embed $ OrLst xs
  where
    condEq c1 c2 = embed $ c1 :&: c2
valEq (ValCondition x) (ValCondition y) = do
  mp <- sequence $ Map.intersectionWith condEq x y
  case Map.elems mp of
    [] -> embedConst (BoolValueC False)
    [x] -> return x
    xs -> embed $ OrLst xs
  where
    condEq c1 c2 = embed $ c1 :&: c2
valEq (ValVector xs) (ValVector ys) = do
  lst <- sequence $ zipWith valEq xs ys
  embed $ AndLst lst

idxList :: [AccessPattern] -> [e IntType] -> [Either Integer (e IntType)]
idxList [] [] = []
idxList (StaticAccess n:xs) dyn = Left n:idxList xs dyn
idxList (DynamicAccess:xs) (i:dyn) = Right i:idxList xs dyn

derefPattern :: [Maybe Integer] -> [AccessPattern] -> [AccessPattern]
derefPattern is [] = fmap (maybe DynamicAccess StaticAccess) is
derefPattern (Just i:is) [StaticAccess j] = StaticAccess (i+j):
                                            fmap (maybe DynamicAccess StaticAccess) is
derefPattern (_:is) [_] = DynamicAccess:
                          fmap (maybe DynamicAccess StaticAccess) is
derefPattern idx (i:is) = i:derefPattern idx is

derefPointer :: (Embed m e)
             => [Either Integer (e IntType)]
             -> Map MemoryPtr (e BoolType,[e IntType])
             -> m (Map MemoryPtr (e BoolType,[e IntType]))
derefPointer idx mp
  = sequence $ Map.fromListWith
    (\el1 el2 -> do
        (c1,dyn1) <- el1
        (c2,dyn2) <- el2
        rc <- c1 .|. c2
        rdyn <- sequence $ zipWith (\d1 d2 -> ite c1 d1 d2) dyn1 dyn2
        return (rc,rdyn))
    [ (loc { offsetPattern = pat },do
          d <- dyn
          return (cond,d))
    | (loc,(cond,dyns)) <- Map.toList mp
    , let (pat,dyn) = deref (offsetPattern loc) dyns idx ]
  where
    deref :: (Embed m e)
          => [AccessPattern] -> [e IntType] -> [Either Integer (e IntType)]
          -> ([AccessPattern],m [e IntType])
    deref [] [] is = let (pat,dyn) = toAccess is
                     in (pat,return dyn)
    deref [StaticAccess n] [] (Left i:is)
      = let (restPat,restDyn) = toAccess is
        in (StaticAccess (n+i):restPat,return restDyn)
    deref [StaticAccess n] [] (Right i:is)
      = let (restPat,restDyn) = toAccess is
        in (DynamicAccess:restPat,do
               nn <- embedConst (IntValueC n)
               ni <- embed $ i :+: nn
               return $ nn:restDyn)
    deref [DynamicAccess] [n] (Left i:is)
      = let (restPat,restDyn) = toAccess is
        in (DynamicAccess:restPat,do
               ri <- embedConst (IntValueC i)
               ni <- embed $ ri :+: n
               return (ni:restDyn))
    deref [DynamicAccess] [n] (Right i:is)
      = let (restPat,restDyn) = toAccess is
        in (DynamicAccess:restPat,do
               ni <- embed $ n :+: i
               return (ni:restDyn))
    deref (StaticAccess n:pat) dyn idx
      = let (restPat,restDyn) = deref pat dyn idx
        in (StaticAccess n:restPat,restDyn)
    deref (DynamicAccess:pat) (n:dyn) idx
      = let (restPat,restDyn) = deref pat dyn idx
        in (DynamicAccess:restPat,fmap (n:) restDyn)
    toAccess (Left i:is) = let (restPat,restDyn) = toAccess is
                           in (StaticAccess i:restPat,restDyn)
    toAccess (Right i:is) = let (restPat,restDyn) = toAccess is
                            in (DynamicAccess:restPat,i:restDyn)
    toAccess [] = ([],[])

withOffset :: (Show b,Monad m)
            => (Struct b -> c -> m (MemoryAccessResult e a,Struct b,c))
            -> Integer
            -> Struct b
            -> c
            -> m (MemoryAccessResult e a,Struct b,c)
withOffset f n (Struct xs) st = do
  (res,nxs,nst) <- withStruct n xs
  return (res,Struct nxs,nst)
  where
    withStruct 0 (x:xs) = do
      (res,nx,nst) <- f x st
      return (res,nx:xs,nst)
    withStruct n (x:xs) = do
      (res,nxs,nst) <- withStruct (n-1) xs
      return (res,x:nxs,nst)
    withStruct _ [] = return (Invalid,[],st)
withOffset _ n obj st = error $ "withOffset: Cannot index "++show obj++" with "++show n

symITE :: forall m e. (GShow e,GetType e,Embed m e)
       => e BoolType -> SymVal e -> SymVal e -> m (SymVal e)
symITE cond (ValBool x) (ValBool y) = fmap ValBool $ ite cond x y
symITE cond (ValInt x) (ValInt y) = fmap ValInt $ ite cond x y
symITE cond (ValBounded x) (ValBounded y) = case (getType x,getType y) of
  (BitVecRepr bx,BitVecRepr by) -> case geq bx by of
    Just Refl -> fmap ValBounded $ ite cond x y
symITE cond (ValPtr x tp) (ValPtr y _) = do
  z <- sequence $ Map.mergeWithKey
       (\_ (pc,pi) (qc,qi)
        -> Just (do
                    nc <- ite cond pc qc
                    ni <- sequence $ zipWith (\p q -> ite cond p q) pi qi
                    return (nc,ni)))
       (fmap (\(pc,pi) -> do
                 nc <- pc .&. cond
                 return (nc,pi)))
       (fmap (\(qc,qi) -> do
                 nc <- qc .&. (not' cond :: m (e BoolType))
                 return (nc,qi))) x y
  return (ValPtr z tp)
symITE cond (ValThreadId x) (ValThreadId y)
  = fmap ValThreadId
    (sequence $ Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
     (fmap (\c -> c .&. cond))
     (fmap (\c -> c .&. (not' cond))) x y)
symITE cond (ValCondition x) (ValCondition y)
  = fmap ValCondition
    (sequence $ Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
     (fmap (\c -> c .&. cond))
     (fmap (\c -> embed (Not cond) >>= embed.(c :&:))) x y)
symITE cond (ValVector v1) (ValVector v2)
  = fmap ValVector $ sequence $ zipWith (symITE cond) v1 v2
symITE cond v1 v2 = error $ "Cannot ITE differently typed values "++show v1++" and "++show v2

symITEs :: (GShow e,GetType e,Embed m e) => [(SymVal e,e BoolType)] -> m (SymVal e)
symITEs [(val,_)] = return val
symITEs ((val,c):rest) = do
  rval <- symITEs rest
  symITE c val rval

arrITE :: forall m e. (GShow e,GetType e,Embed m e) => e BoolType -> SymArray e -> SymArray e
       -> m (SymArray e)
arrITE cond (ArrBool x) (ArrBool y) = fmap ArrBool (ite cond x y)
arrITE cond (ArrInt x) (ArrInt y) = fmap ArrInt (ite cond x y)
arrITE cond (ArrBounded x) (ArrBounded y) = case (getType x,getType y) of
  (ArrayRepr _ (BitVecRepr bx),ArrayRepr _ (BitVecRepr by))
    -> case geq bx by of
    Just Refl -> fmap ArrBounded $ ite cond x y
arrITE cond (ArrPtr x tp) (ArrPtr y _) = do
  z <- sequence $ Map.mergeWithKey
       (\_ (pc,pi) (qc,qi)
        -> Just (do
                    nc <- ite cond pc qc
                    ni <- sequence $ zipWith (\p q -> ite cond p q) pi qi
                    return (nc,ni)))
       (fmap (\(pc,pi) -> do
                 nc <- ite cond pc (constArray (int ::: Nil) false)
                 return (nc,pi)))
       (fmap (\(qc,qi) -> do
                 nc <- ite cond (constArray (int ::: Nil) false) qc
                 return (nc,qi))) x y
  return (ArrPtr z tp)
arrITE cond (ArrThreadId x) (ArrThreadId y)
  = fmap ArrThreadId
    (sequence $ Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
     (fmap (\c -> ite cond c (constArray (int ::: Nil) false)))
     (fmap (\c -> ite cond (constArray (int ::: Nil) false) c)) x y)
arrITE cond (ArrCondition x) (ArrCondition y)
  = fmap ArrCondition
    (sequence $ Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
     (fmap (\c -> ite cond c (constArray (int ::: Nil) false)))
     (fmap (\c -> ite cond (constArray (int ::: Nil) false) c)) x y)
arrITE cond (ArrVector x) (ArrVector y)
  = fmap ArrVector $ sequence $ zipWith (arrITE cond) x y

structITE :: (Embed m e)
          => (e BoolType -> b -> b -> m b)
          -> e BoolType -> Struct b -> Struct b -> m (Struct b)
structITE ite cond (Singleton x) (Singleton y)
  = fmap Singleton $ ite cond x y
structITE ite cond (Struct xs) (Struct ys)
  = fmap Struct $ sequence $ zipWith (structITE ite cond) xs ys

structITEs :: (Embed m e)
           => ([(b,e BoolType)] -> m b)
           -> [(Struct b,e BoolType)]
           -> m (Struct b)
structITEs comb xs@(fst.head -> Singleton _) = fmap Singleton (comb $ fmap (\(Singleton x,c) -> (x,c)) xs)
structITEs comb xs = fmap Struct (sequence $ zipStructs (fmap (\(Struct x,c) -> (x,c)) xs))
  where
    zipStructs (([],_):_) = []
    zipStructs xs = (structITEs comb (fmap (\(x:_,c) -> (x,c)) xs)):
                    zipStructs (fmap (\(_:xs,c) -> (xs,c)) xs)

withDynOffset :: (Embed m e)
              => (e BoolType -> b -> b -> m b)
              -> (Struct b -> c -> m (MemoryAccessResult e a,Struct b,c))
              -> e IntType
              -> [Struct b]
              -> c
              -> m (MemoryAccessResult e a,[Struct b],c)
withDynOffset ite f n xs st = with (0::Integer) xs st
  where
    with i (x:xs) st = do
      (res,nx,st1) <- f x st
      (ress,nxs,st2) <- with (i+1) xs st1
      cond <- n .==. (I.constant i)
      nx' <- structITE ite cond nx x
      return (CondAccess cond res ress,
              nx':nxs,
              st2)
    with i [] st = return (Invalid,[],st)

accessStruct :: (Embed m e,Show b)
              => (e BoolType -> b -> b -> m b)
              -> (b -> c -> m (MemoryAccessResult e a,b,c))
              -> [Either Integer (e IntType)]
              -> Struct b
              -> c
              -> m (MemoryAccessResult e a,Struct b,c)
accessStruct _ f [] (Singleton x) st = do
  (res,nx,nst) <- f x st
  return (res,Singleton nx,nst)
accessStruct ite f (Left i:is) s st
  = withOffset (accessStruct ite f is) i s st
accessStruct ite f (Right i:is) (Struct s) st = do
  (res,ns,nst) <- withDynOffset ite (accessStruct ite f is) i s st
  return (res,Struct ns,nst)


accessArray :: (GetType e,Embed m e)
            => (SymVal e -> c -> m (MemoryAccessResult e a,SymVal e,c))
            -> e IntType
            -> SymArray e
            -> c
            -> m (MemoryAccessResult e a,SymArray e,c)
accessArray f idx arr st = do
  el <- extractValue idx arr
  (res,nval,nst) <- f el st
  narr <- insertValue idx nval arr
  return (res,narr,nst)

extractValue :: (Embed m e) => e IntType -> SymArray e -> m (SymVal e)
extractValue idx (ArrBool arr) = fmap ValBool $ select1 arr idx
extractValue idx (ArrInt arr) = fmap ValInt $ select1 arr idx
extractValue idx (ArrBounded arr) = fmap ValBounded $ select1 arr idx
extractValue idx (ArrPtr arr tp) = do
  mp <- mapM (\(conds,idxs) -> do
                 cond <- select1 conds idx
                 idx <- mapM (\i -> select1 i idx) idxs
                 return (cond,idx)
             ) arr
  return $ ValPtr mp tp
extractValue idx (ArrThreadId arr)
  = fmap ValThreadId (mapM (\conds -> select1 conds idx) arr)
extractValue idx (ArrCondition arr)
  = fmap ValCondition (mapM (\conds -> select1 conds idx) arr)
extractValue idx (ArrVector arrs)
  = fmap ValVector (mapM (extractValue idx) arrs)

insertValue :: (GetType e,Embed m e) => e IntType -> SymVal e -> SymArray e -> m (SymArray e)
insertValue idx (ValBool b) (ArrBool arr) = fmap ArrBool $ store1 arr idx b
insertValue idx (ValInt i) (ArrInt arr) = fmap ArrInt $ store1 arr idx i
insertValue idx (ValBounded v) (ArrBounded arr) = case (getType v,getType arr) of
  (BitVecRepr bw1,ArrayRepr _ (BitVecRepr bw2)) -> case geq bw1 bw2 of
    Just Refl -> fmap ArrBounded $ store1 arr idx v
insertValue idx (ValPtr p _) (ArrPtr ps tp) = do
  mp <- sequence $ Map.intersectionWith
        (\(ncond,noff) (conds,offs) -> do
            rcond <- store1 conds idx ncond
            roffs <- sequence $ zipWith (\noff offs -> store1 offs idx noff) noff offs
            return (rcond,roffs)
        ) p ps
  return (ArrPtr mp tp)
insertValue idx (ValThreadId t) (ArrThreadId ts)
  = fmap ArrThreadId $ sequence $ Map.intersectionWith
    (\nval arr -> store1 arr idx nval)
    t ts
insertValue idx (ValCondition t) (ArrCondition ts)
  = fmap ArrCondition $ sequence $ Map.intersectionWith
    (\nval arr -> store1 arr idx nval)
    t ts
insertValue idx (ValVector vals) (ArrVector arr)
  = fmap ArrVector $ sequence $ zipWith (insertValue idx) vals arr

accessAlloc :: (Embed m e,GetType e,GShow e)
            => (SymVal e -> c -> m (MemoryAccessResult e a,SymVal e,c))
            -> [Either Integer (e IntType)]
            -> AllocVal e
            -> c
            -> m (MemoryAccessResult e a,AllocVal e,c)
accessAlloc f idx@(Left i:is) (ValStatic s) st = do
  (res,ns,nst) <- accessStatic i s
  return (res,ValStatic ns,nst)
  where
    accessStatic 0 (s:ss) = do
      (res,ns,nst) <- accessStruct symITE f is s st
      return (res,ns:ss,nst)
    accessStatic n (s:ss) = do
      (res,nss,nst) <- accessStatic (n-1) ss
      return (res,s:nss,nst)
    accessStatic _ [] = return (Invalid,[],st)
accessAlloc f (Right i:is) (ValStatic s) st = do
  (res,ns,nst) <- withDynOffset symITE (accessStruct symITE f is) i s st
  return (res,ValStatic ns,nst)
accessAlloc f [] (ValStatic (x:xs)) st = do
  (res,nx,nst) <- accessStruct symITE f [] x st
  return (res,ValStatic $ nx:xs,nst)
accessAlloc f (i:is) (ValDynamic arrs sz) st = do
  i' <- case i of
    Left i -> embedConst (IntValueC i)
    Right i -> return i
  (res,narrs,nst) <- accessStruct arrITE (accessArray (nf i') i') is arrs st
  return (res,ValDynamic narrs sz,nst)
  where
    nf i val st = do
      (acc,res,nst) <- f val st
      cond <- embed $ i :>=: sz
      return (CondAccess cond Invalid acc,res,nst)
    
accessAllocTyped :: (Embed m e,GetType e,GShow e)
                 => SymType
                 -> (SymVal e -> c -> m (a,SymVal e,c))
                 -> [Either Integer (e IntType)]
                 -> AllocVal e
                 -> c
                 -> m (MemoryAccessResult e a,AllocVal e,c)
accessAllocTyped tp f idx val st
  = accessAlloc (\val st -> if sameType tp (symType val)
                            then do
                              (obj,nval,nst) <- f val st
                              return (Success obj,nval,nst)
                            else return (TypeError,val,st)
                ) idx val st

accessAllocTypedIgnoreErrors :: (Embed m e,GetType e,GShow e)
                             => SymType
                             -> (SymVal e -> c -> m (SymVal e,c))
                             -> [Either Integer (e IntType)]
                             -> AllocVal e
                             -> c
                             -> m (SymVal e,AllocVal e,c)
accessAllocTypedIgnoreErrors tp f idx val st = do
  (res,nval,nst) <- accessAllocTyped tp (\val st -> do
                                            (nval,nst) <- f val st
                                            return (nval,nval,nst)) idx val st
  res' <- combine res
  return (res',nval,nst)
  where
    combine (Success x) = return x
    combine (CondAccess c x y) = do
      x' <- combine x
      y' <- combine y
      symITE c x' y'
    combine _ = defaultValue tp

sameType :: SymType -> SymType -> Bool
sameType TpBool TpBool = True
sameType TpInt TpInt = True
sameType (TpBounded bw1) (TpBounded bw2) = defaultEq bw1 bw2
sameType (TpPtr _ tp1) (TpPtr _ tp2) = sameStructType tp1 tp2
sameType (TpThreadId _) (TpThreadId _) = True
sameType (TpCondition _) (TpCondition _) = True
sameType (TpVector v1) (TpVector v2) = sameVector v1 v2
  where
    sameVector [] [] = True
    sameVector (x:xs) (y:ys) = sameType x y && sameVector xs ys
    sameVector _ _ = False
sameType _ _ = False

sameStructType :: Struct SymType -> Struct SymType -> Bool
sameStructType (Singleton t1) (Singleton t2) = sameType t1 t2
sameStructType (Struct t1) (Struct t2) = sameStruct t1 t2
  where
    sameStruct [] [] = True
    sameStruct (x:xs) (y:ys) = sameStructType x y &&
                               sameStruct xs ys
    sameStruct _ _ = False
sameStructType _ _ = False

sameValueType :: GetType e => Struct (SymVal e) -> Struct (SymVal e) -> Bool
sameValueType x1 x2 = sameStructType
                      (fmap symType x1)
                      (fmap symType x2)

sameArrayType :: GetType e => Struct (SymArray e) -> Struct (SymArray e) -> Bool
sameArrayType x1 x2 = sameStructType
                      (fmap symArrType x1)
                      (fmap symArrType x2)

compositeITE :: (Embed m e,GetType e,Composite arg) => e BoolType -> arg e -> arg e -> m (arg e)
compositeITE c arg1 arg2
  = foldExprs (\rev e1 -> do
                  let e2 = accessComposite rev arg2
                  embed $ ITE c e1 e2
              ) arg1

compositeITEs :: (Embed m e,GetType e,Composite arg) => [(arg e,e BoolType)] -> m (arg e)
compositeITEs [(x,_)] = return x
compositeITEs ((x,c):xs) = do
  xs' <- compositeITEs xs
  compositeITE c x xs'

firstType :: Struct SymType -> SymType
firstType (Singleton tp) = tp
firstType (Struct (tp:_)) = firstType tp

offsetStruct :: [AccessPattern] -> Struct SymType -> Struct SymType
offsetStruct [] x = x
offsetStruct (StaticAccess n:pat) (Struct tps)
  = offsetStruct pat (tps `genericIndex` n)
offsetStruct (DynamicAccess:pat) (Struct tps)
  = offsetStruct pat (head tps)

offsetAlloc :: [AccessPattern] -> AllocType -> Struct SymType
offsetAlloc [] (TpStatic _ tp) = offsetStruct [] tp
offsetAlloc [] (TpDynamic tp) = offsetStruct [] tp
offsetAlloc (_:pat) (TpStatic _ tp) = offsetStruct pat tp
offsetAlloc (_:pat) (TpDynamic tp) = offsetStruct pat tp

mapTypes :: (SymType -> SymType) -> AllocType -> AllocType
mapTypes f (TpStatic n tp) = TpStatic n (fmap f tp)
mapTypes f (TpDynamic tp) = TpDynamic (fmap f tp)

mapMTypes :: Monad m => (SymType -> m SymType) -> AllocType -> m AllocType
mapMTypes f (TpStatic n tp) = mapM f tp >>= return.TpStatic n
mapMTypes f (TpDynamic tp) = mapM f tp >>= return.TpDynamic 

mapPointer :: (Struct SymType -> Map MemoryPtr () -> Map MemoryPtr ())
           -> SymType -> SymType
mapPointer f (TpPtr trgs tp)
  = let ntrgs = f tp trgs
        ntp = fmap (mapPointer f) tp
    in TpPtr ntrgs ntp
mapPointer _ tp = tp

patternMatch :: (Embed m e)
             => [AccessPattern] -> [AccessPattern]
             -> [e IntType] -> [e IntType]
             -> m (Maybe [e BoolType])
patternMatch [] [] [] [] = return (Just [])
patternMatch (StaticAccess x:xs) (StaticAccess y:ys) ix iy
  | x==y = patternMatch xs ys ix iy
  | otherwise = return Nothing
patternMatch (DynamicAccess:xs) (StaticAccess y:ys) (ix:ixs) iy = do
  rest <- patternMatch xs ys ixs iy
  case rest of
    Nothing -> return Nothing
    Just rest' -> do
      c <- ix .==. (I.constant y)
      return $ Just $ c:rest'
patternMatch (StaticAccess x:xs) (DynamicAccess:ys) ix (iy:iys) = do
  rest <- patternMatch xs ys ix iys
  case rest of
    Nothing -> return Nothing
    Just rest' -> do
      c <- iy .==. (I.constant x)
      return $ Just $ c:rest'
patternMatch (DynamicAccess:xs) (DynamicAccess:ys) (ix:ixs) (iy:iys) = do
  rest <- patternMatch xs ys ixs iys
  case rest of
    Nothing -> return Nothing
    Just rest' -> do
      c <- ix .==. iy
      return $ Just $ c:rest'
patternMatch _ _ _ _ = return Nothing

allocITE :: (Embed m e,GetType e,GShow e) => e BoolType -> AllocVal e -> AllocVal e
         -> m (AllocVal e)
allocITE cond (ValStatic xs) (ValStatic ys) = do
  res <- ites xs ys
  return (ValStatic res)
  where
    ites [] [] = return []
    ites (x:xs) (y:ys) = do
      z <- structITE symITE cond x y
      zs <- ites xs ys
      return (z:zs)
allocITE cond (ValDynamic x sx) (ValDynamic y sy) = do
  z <- structITE arrITE cond x y
  sz <- ite cond sx sy
  return $ ValDynamic z sz

instance Composite SymVal where
  type CompDescr SymVal = SymType
  type RevComp SymVal = RevValue
  compositeType TpBool = ValBool BoolRepr
  compositeType TpInt = ValInt IntRepr
  compositeType (TpBounded bw) = ValBounded (BitVecRepr bw)
  compositeType (TpPtr mp tp)
    = ValPtr (Map.mapWithKey
              (\ptr _ -> (BoolRepr,[IntRepr | DynamicAccess <- offsetPattern ptr])) mp) tp
  compositeType (TpThreadId mp)
    = ValThreadId $ fmap (const BoolRepr) mp
  compositeType (TpCondition mp)
    = ValCondition $ fmap (const BoolRepr) mp
  compositeType (TpVector tps)
    = ValVector $ fmap compositeType tps
  foldExprs f (ValBool e) = fmap ValBool $ f RevBool e
  foldExprs f (ValInt e) = fmap ValInt $ f RevInt e
  foldExprs f (ValBounded e) = case getType e of
    BitVecRepr bw -> fmap ValBounded $ f (RevBounded bw) e
  foldExprs f (ValPtr mp tp) = do
    nmp <- sequence $ Map.mapWithKey
           (\ptr (c,idx) -> do
               nc <- f (PtrCond ptr) c
               nidx <- sequence $ zipWith (\i -> f (PtrIdx ptr i)) [0..] idx
               return (nc,nidx)
           ) mp
    return (ValPtr nmp tp)
  foldExprs f (ValThreadId mp)
    = fmap ValThreadId $ sequence $ Map.mapWithKey
      (\th -> f (ThreadIdCond th)) mp
  foldExprs f (ValCondition mp)
    = fmap ValCondition $ sequence $ Map.mapWithKey
      (\th -> f (ConditionCond th)) mp
  foldExprs f (ValVector vec)
    = fmap ValVector $ sequence $
      zipWith (\i -> foldExprs (\rev -> f (RevVector i rev))) [0..] vec
  createComposite f TpBool = fmap ValBool $ f BoolRepr RevBool
  createComposite f TpInt = fmap ValInt $ f IntRepr RevInt
  createComposite f (TpBounded bw) = fmap ValBounded $ f (BitVecRepr bw) (RevBounded bw)
  createComposite f (TpPtr mp tp) = do
    nmp <- sequence $ Map.mapWithKey
           (\ptr _ -> do
               c <- f BoolRepr (PtrCond ptr)
               idx <- mapM (\(i,_) -> f IntRepr (PtrIdx ptr i))
                      (zip [0..] [ () | DynamicAccess <- offsetPattern ptr ])
               return (c,idx)
           ) mp
    return (ValPtr nmp tp)
  createComposite f (TpThreadId mp)
    = fmap ValThreadId $ sequence $ Map.mapWithKey
      (\th _ -> f BoolRepr (ThreadIdCond th)) mp
  createComposite f (TpCondition mp)
    = fmap ValCondition $ sequence $ Map.mapWithKey
      (\th _ -> f BoolRepr (ConditionCond th)) mp
  createComposite f (TpVector tps)
    = fmap ValVector $ sequence $
      zipWith (\i -> createComposite (\tp rev -> f tp (RevVector i rev)))
      [0..] tps
  accessComposite RevBool (ValBool v) = v
  accessComposite RevInt (ValInt v) = v
  accessComposite (RevBounded bw1) (ValBounded v) = case getType v of
    BitVecRepr bw2 -> case geq bw1 bw2 of
      Just Refl -> v
  accessComposite (PtrCond ptr) (ValPtr mp tp) = case Map.lookup ptr mp of
    Just (c,_) -> c
  accessComposite (PtrIdx ptr i) (ValPtr mp tp) = case Map.lookup ptr mp of
    Just (_,idx) -> idx!!i
  accessComposite (ThreadIdCond th) (ValThreadId mp) = case Map.lookup th mp of
    Just r -> r
  accessComposite (ConditionCond th) (ValCondition mp) = case Map.lookup th mp of
    Just r -> r
  accessComposite (RevVector i rev) (ValVector vec) = accessComposite rev (vec!!i)
  eqComposite = valEq

mkArr :: Repr tp -> Repr (ArrayType '[IntType] tp)
mkArr = ArrayRepr (IntRepr ::: Nil)

instance Composite SymArray where
  type CompDescr SymArray = SymType
  type RevComp SymArray = RevArray
  compositeType TpBool = ArrBool (mkArr BoolRepr)
  compositeType TpInt = ArrInt (mkArr IntRepr)
  compositeType (TpBounded bw) = ArrBounded (mkArr (BitVecRepr bw))
  compositeType (TpPtr mp tp)
    = ArrPtr (Map.mapWithKey
              (\ptr _ -> (mkArr BoolRepr,
                          [mkArr IntRepr | DynamicAccess <- offsetPattern ptr])) mp) tp
  compositeType (TpThreadId mp)
    = ArrThreadId $ fmap (const (mkArr BoolRepr)) mp
  compositeType (TpCondition mp)
    = ArrCondition $ fmap (const (mkArr BoolRepr)) mp
  compositeType (TpVector tps)
    = ArrVector $ fmap compositeType tps
  foldExprs f (ArrBool e) = fmap ArrBool $ f (RevArray RevBool) e
  foldExprs f (ArrInt e) = fmap ArrInt $ f (RevArray RevInt) e
  foldExprs f (ArrBounded e) = case getType e of
    ArrayRepr _ (BitVecRepr bw) -> fmap ArrBounded $ f (RevArray (RevBounded bw)) e
  foldExprs f (ArrPtr mp tp) = do
    nmp <- sequence $ Map.mapWithKey
           (\ptr (c,idx) -> do
               nc <- f (RevArray $ PtrCond ptr) c
               nidx <- sequence $ zipWith (\i -> f (RevArray $ PtrIdx ptr i)) [0..] idx
               return (nc,nidx)
           ) mp
    return (ArrPtr nmp tp)
  foldExprs f (ArrThreadId mp)
    = fmap ArrThreadId $ sequence $ Map.mapWithKey
      (\th -> f (RevArray $ ThreadIdCond th)) mp
  foldExprs f (ArrCondition mp)
    = fmap ArrCondition $ sequence $ Map.mapWithKey
      (\th -> f (RevArray $ ConditionCond th)) mp
  foldExprs f (ArrVector vec)
    = fmap ArrVector $ sequence $
      zipWith (\i -> foldExprs (\(RevArray rev) -> f (RevArray $ RevVector i rev)))
      [(0::Int)..] vec
  accessComposite (RevArray RevBool) (ArrBool v) = v
  accessComposite (RevArray RevInt) (ArrInt v) = v
  accessComposite (RevArray (RevBounded bw1)) (ArrBounded v) = case getType v of
    ArrayRepr _ (BitVecRepr bw2) -> case geq bw1 bw2 of
      Just Refl -> v
  accessComposite (RevArray (PtrCond ptr)) (ArrPtr mp tp) = case Map.lookup ptr mp of
    Just (c,_) -> c
  accessComposite (RevArray (PtrIdx ptr i)) (ArrPtr mp tp) = case Map.lookup ptr mp of
    Just (_,idx) -> idx!!i
  accessComposite (RevArray (ThreadIdCond th)) (ArrThreadId mp) = case Map.lookup th mp of
    Just r -> r
  accessComposite (RevArray (ConditionCond th)) (ArrCondition mp) = case Map.lookup th mp of
    Just r -> r
  accessComposite (RevArray (RevVector i rev)) (ArrVector vec)
    = accessComposite (RevArray rev) (vec!!i)

instance Composite arg => Composite (CompositeStruct arg) where
  type CompDescr (CompositeStruct arg) = Struct (CompDescr arg)
  type RevComp (CompositeStruct arg) = RevStruct (RevComp arg)
  compositeType (Singleton tp) = CompositeStruct (Singleton (compositeType tp))
  compositeType (Struct tps) = CompositeStruct
                               (Struct $ fmap (\tp -> let CompositeStruct tp' = compositeType tp
                                                      in tp') tps)
  foldExprs f (CompositeStruct (Singleton x)) = do
    nx <- foldExprs (\rev -> f (RevStruct [] rev)) x
    return (CompositeStruct (Singleton nx))
  foldExprs f (CompositeStruct (Struct xs)) = do
    nxs <- mapM (\(i,x) -> do
                    CompositeStruct nx <- foldExprs
                                          (\(RevStruct is rev) -> f (RevStruct (i:is) rev))
                                          (CompositeStruct x)
                    return nx
                ) $ zip [0..] xs
    return (CompositeStruct (Struct nxs))
  accessComposite (RevStruct [] rev) (CompositeStruct (Singleton x))
    = accessComposite rev x
  accessComposite (RevStruct (i:is) rev) (CompositeStruct (Struct xs))
    = accessComposite (RevStruct is rev) (CompositeStruct (xs!!i))

instance Composite AllocVal where
  type CompDescr AllocVal = AllocType
  type RevComp AllocVal = RevAlloc
  compositeType (TpStatic sz tp) = ValStatic (replicate sz val)
    where
      CompositeStruct val = compositeType tp
  compositeType (TpDynamic tp) = ValDynamic val IntRepr
    where
      CompositeStruct val = compositeType tp
  foldExprs f (ValStatic vals) = do
    nvals <- mapM (\(i,x) -> do
                      CompositeStruct nx <- foldExprs (\(RevStruct is rev)
                                                       -> f (RevStatic i is rev)
                                                      ) (CompositeStruct x)
                      return nx
                  ) $ zip [0..] vals
    return (ValStatic nvals)
  foldExprs f (ValDynamic arr sz) = do
    CompositeStruct narr <- foldExprs (\(RevStruct is (RevArray rev))
                                       -> f (RevDynamic is rev)
                                      ) (CompositeStruct arr)
    nsz <- f RevSize sz
    return (ValDynamic narr nsz)
  accessComposite (RevStatic i is rev) (ValStatic vals)
    = accessComposite (RevStruct is rev) (CompositeStruct (vals!!i))
  accessComposite (RevDynamic is rev) (ValDynamic arr _)
    = accessComposite (RevStruct is (RevArray rev)) (CompositeStruct arr)
  accessComposite RevSize (ValDynamic _ sz) = sz

showMemoryLoc :: MemoryLoc -> ShowS
showMemoryLoc (Left alloc) = unsafePerformIO $ do
  n <- getNameString alloc
  blk <- instructionGetParent alloc
  fun <- basicBlockGetParent blk
  fn <- getNameString fun
  return $ showChar '#' . showString fn . showChar '.' . showString n
showMemoryLoc (Right global) = unsafePerformIO $ do
  n <- getNameString global
  return $ showChar '@' . showString n

showMemoryTrg :: MemoryTrg -> ShowS
showMemoryTrg (AllocTrg alloc) = unsafePerformIO $ do
  n <- getNameString alloc
  blk <- instructionGetParent alloc
  fun <- basicBlockGetParent blk
  fn <- getNameString fun
  return $ showChar '#' . showString fn . showChar '.' . showString n
showMemoryTrg (GlobalTrg global) = unsafePerformIO $ do
  n <- getNameString global
  return $ showChar '@' . showString n
showMemoryTrg (LocalTrg global) = unsafePerformIO $ do
  n <- getNameString global
  return $ showString "@@" . showString n

showValue :: ValueC v => Ptr v -> ShowS
showValue v = unsafePerformIO $ do
  hasN <- hasName v
  if hasN
    then do
    n <- getNameString v
    return $ showString n
    else return $ showsPrec 0 v

showBlock :: (Ptr BasicBlock,Int) -> ShowS
showBlock (blk,n) = unsafePerformIO $ do
  fun <- basicBlockGetParent blk
  funHasName <- hasName fun
  fname <- if funHasName
           then do
             n <- getNameString fun
             return $ showString n
           else return $ showsPrec 0 fun
  blkHasName <- hasName blk
  bname <- if blkHasName
           then do
             n <- getNameString blk
             return $ showString n
           else return $ showsPrec 0 blk
  return $ fname .
    showChar '.' .
    bname .
    (if n==0 then id
     else showChar '.' .
          showsPrec 0 n)

instance Show MemoryPtr where
  showsPrec _ ptr = showMemoryTrg (memoryLoc ptr) .
                    case offsetPattern ptr of
                     [] -> id
                     xs -> showsPrec 0 xs

instance Show AccessPattern where
  showsPrec p (StaticAccess i) = showParen (p>10) $
                                 showString "stat " .
                                 showsPrec 0 i
  showsPrec _ DynamicAccess = showString "dyn"

instance Show a => Show (Struct a) where
  showsPrec p (Singleton x) = showsPrec p x
  showsPrec p (Struct x) = showParen (p>10) $
                           showString "struct " .
                           showsPrec 0 x

instance GShow e => Show (AllocVal e) where
  showsPrec p (ValStatic lst) = showParen (p>10) $
                                showString "static " .
                                showsPrec 11 lst
  showsPrec p (ValDynamic dyn sz) = showParen (p>10) $
                                    showString "dyn " .
                                    showsPrec 11 dyn .
                                    showChar ' ' .
                                    gshowsPrec 11 sz

instance GShow e => Show (SymVal e) where
  showsPrec p (ValBool b) = showParen (p>10) $
                            showString "bool " .
                            gshowsPrec 11 b
  showsPrec p (ValInt i) = showParen (p>10) $
                           showString "int " .
                           gshowsPrec 11 i
  showsPrec p (ValBounded e) = showParen (p>10) $
                               showString "bw " .
                               gshowsPrec 11 e
  showsPrec p (ValPtr mp tp) = showParen (p>10) $
                               showString "ptr " .
                               showsPrec 11 tp .
                               showChar ' ' .
                               showAssoc (showsPrec 9)
                               (\(c,idx) -> gshowsPrec 9 c .
                                            showListWith (gshowsPrec 9) idx
                               ) mp
  showsPrec p (ValThreadId ths) = showParen (p>10) $
                                  showString "thread-id " .
                                  showAssoc (showsPrec 9) (gshowsPrec 9) ths
  showsPrec p (ValCondition mp) = showParen (p>10) $
                                  showString "cond " .
                                  showAssoc (showsPrec 9) (gshowsPrec 9) mp
  showsPrec p (ValVector vec) = showParen (p>10) $
                                showString "vec " .
                                showsPrec 11 vec

instance GShow e => Show (SymArray e) where
  showsPrec p (ArrBool b) = showParen (p>10) $
                            showString "bool " .
                            gshowsPrec 11 b
  showsPrec p (ArrInt i) = showParen (p>10) $
                           showString "int " .
                           gshowsPrec 11 i
  showsPrec p (ArrBounded b) = showParen (p>10) $
                               showString "bw " .
                               gshowsPrec 11 b
  showsPrec p (ArrPtr mp tp) = showParen (p>10) $
                               showString "ptr " .
                               showsPrec 11 tp .
                               showChar ' ' .
                               showAssoc (showsPrec 9)
                               (\(c,idx) -> gshowsPrec 9 c .
                                            showListWith (gshowsPrec 9) idx
                               ) mp
  showsPrec p (ArrThreadId ths) = showParen (p>10) $
                                  showString "thread-id " .
                                  showAssoc (showsPrec 9) (gshowsPrec 9) ths
  showsPrec p (ArrCondition mp) = showParen (p>10) $
                                  showString "cond " .
                                  showAssoc (showsPrec 9) (gshowsPrec 9) mp
  showsPrec p (ArrVector vec) = showParen (p>10) $
                                showString "vec " .
                                showsPrec 11 vec

instance Show (RevValue tp) where
  showsPrec p RevInt = showString "int"
  showsPrec p RevBool = showString "bool"
  showsPrec p (RevBounded bw) = showParen (p>10) $
                                showString "bw " . showsPrec 11 (naturalToInteger bw)
  showsPrec p (PtrCond loc) = showString "ptrcond"
  showsPrec p (PtrIdx loc i) = showString "ptridx"
  showsPrec p (ThreadIdCond th) = showString"threadid"
  showsPrec p (ConditionCond th) = showString "condition"
  showsPrec p (RevVector i rev)
    = showParen (p>10) $
      showString "vec " .
      showsPrec 11 i .
      showChar ' ' .
      showsPrec 11 rev

instance Show (RevArray tp) where
  showsPrec p (RevArray rev) = showParen (p>10) $
                               showString "array " .
                               showsPrec 11 rev

instance GShow RevValue where
  gshowsPrec = showsPrec

instance GShow RevArray where
  gshowsPrec = showsPrec

instance GEq RevValue where
  geq RevInt RevInt = Just Refl
  geq RevBool RevBool = Just Refl
  geq (RevBounded bw1) (RevBounded bw2) = do
    Refl <- geq bw1 bw2
    return Refl
  geq (PtrCond p1) (PtrCond p2) = if p1==p2
                                  then Just Refl
                                  else Nothing
  geq (PtrIdx p1 i1) (PtrIdx p2 i2)
    = if p1==p2 && i1==i2
      then Just Refl
      else Nothing
  geq (ThreadIdCond c1) (ThreadIdCond c2)
    = if c1==c2
      then Just Refl
      else Nothing
  geq (ConditionCond c1) (ConditionCond c2)
    = if c1==c2
      then Just Refl
      else Nothing
  geq (RevVector i1 r1) (RevVector i2 r2) = case geq r1 r2 of
    Just Refl -> if i1==i2
                 then Just Refl
                 else Nothing
    Nothing -> Nothing
  geq _ _ = Nothing

instance GEq RevArray where
  geq (RevArray r1) (RevArray r2) = case geq r1 r2 of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare RevValue where
  gcompare RevInt RevInt = GEQ
  gcompare RevInt _ = GLT
  gcompare _ RevInt = GGT
  gcompare RevBool RevBool = GEQ
  gcompare RevBool _ = GLT
  gcompare _ RevBool = GGT
  gcompare (RevBounded bw1) (RevBounded bw2) = case gcompare bw1 bw2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevBounded _) _ = GLT
  gcompare _ (RevBounded _) = GGT
  gcompare (PtrCond p1) (PtrCond p2) = case compare p1 p2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (PtrCond _) _ = GLT
  gcompare _ (PtrCond _) = GGT
  gcompare (PtrIdx p1 i1) (PtrIdx p2 i2) = case compare (p1,i1) (p2,i2) of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (PtrIdx _ _) _ = GLT
  gcompare _ (PtrIdx _ _) = GGT
  gcompare (ThreadIdCond t1) (ThreadIdCond t2) = case compare t1 t2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (ThreadIdCond _) _ = GLT
  gcompare _ (ThreadIdCond _) = GGT
  gcompare (ConditionCond t1) (ConditionCond t2) = case compare t1 t2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (ConditionCond _) _ = GLT
  gcompare _ (ConditionCond _) = GLT
  gcompare (RevVector i1 r1) (RevVector i2 r2) = case compare i1 i2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT

instance GCompare RevArray where
  gcompare (RevArray r1) (RevArray r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance Show (RevAlloc tp) where
  show (RevStatic top idx val)
    = "static"++(if top==0 then "" else "@"++show top)++
      (if null idx then "" else show idx)++"{"++show val++"}"
  show (RevDynamic idx val)
    = "dynamic"++(if null idx then "" else show idx)++"{"++show val++"}"
  show RevSize = "size"

instance GEq e => GEq (RevStruct e) where
  geq (RevStruct i1 e1) (RevStruct i2 e2)
    = if i1==i2
      then case geq e1 e2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing

instance GCompare e => GCompare (RevStruct e) where
  gcompare (RevStruct i1 e1) (RevStruct i2 e2)
    = case compare i1 i2 of
    EQ -> case gcompare e1 e2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT

instance GShow e => Show (RevStruct e tp) where
  showsPrec p (RevStruct i e) = showParen (p>10) $
                                showString "index " .
                                showsPrec 11 i .
                                showChar ' ' .
                                gshowsPrec 11 e

instance GShow e => GShow (RevStruct e) where
  gshowsPrec = showsPrec

instance GEq RevAlloc where
  geq (RevStatic i1 is1 rev1) (RevStatic i2 is2 rev2)
    = if i1==i2 && is1==is2
      then case geq rev1 rev2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq (RevDynamic i1 rev1) (RevDynamic i2 rev2)
    = if i1==i2
      then case geq rev1 rev2 of
      Just Refl -> Just Refl
      Nothing -> Nothing
      else Nothing
  geq RevSize RevSize = Just Refl
  geq _ _ = Nothing

instance GCompare RevAlloc where
  gcompare (RevStatic i1 is1 rev1) (RevStatic i2 is2 rev2)
    = case compare (i1,is1) (i2,is2) of
    EQ -> case gcompare rev1 rev2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (RevStatic _ _ _) _ = GLT
  gcompare _ (RevStatic _ _ _) = GGT
  gcompare (RevDynamic i1 rev1) (RevDynamic i2 rev2) = case compare i1 i2 of
    EQ -> case gcompare rev1 rev2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (RevDynamic _ _) _ = GLT
  gcompare _ (RevDynamic _ _) = GGT
  gcompare RevSize RevSize = GEQ

instance GShow RevAlloc where
  gshowsPrec = showsPrec

showSymType :: Map (Ptr CallInst) String -> SymType -> ShowS
showSymType _ TpBool = showString "bool"
showSymType _ TpInt = showString "int"
showSymType _ (TpBounded bw)
  = showString "bw[" .
    showsPrec 0 (naturalToInteger bw) .
    showChar ']'
showSymType mp (TpPtr trgs tp) = showString "ptr[" .
                                 showStruct (showSymType mp) tp .
                                 showString "]" .
                                 showsPrec 0 (Map.keys trgs)
showSymType mp (TpThreadId trgs)
  = showString "thread-id" .
    showListWith
    (\trg -> case Map.lookup trg mp of
      Just name -> showString name)
    (Map.keys trgs)
showSymType mp (TpCondition trgs)
  = showString "condition" .
    showListWith
    (\trg -> case trg of
      Nothing -> showString "main"
      Just th -> case Map.lookup th mp of
        Just name -> showString name)
    (Map.keys trgs)
showSymType mp (TpVector tps)
  = showListWith (showSymType mp) tps

showStruct :: (a -> ShowS) -> Struct a -> ShowS
showStruct f (Singleton x) = f x
showStruct f (Struct xs)
  = showListWith (showStruct f) xs

showAllocType :: Map (Ptr CallInst) String -> AllocType -> ShowS
showAllocType mp (TpStatic sz tp)
  = showString "static[" .
    showsPrec 0 sz .
    showString "][" .
    showStruct (showSymType mp) tp .
    showChar ']'
showAllocType mp (TpDynamic tp)
  = showString "dynamic[" .
    showStruct (showSymType mp) tp .
    showChar ']'

showSymValue :: GShow e => Map (Ptr CallInst) String -> SymVal e -> ShowS
showSymValue mp (ValBool e) = gshowsPrec 0 e
showSymValue mp (ValInt e) = gshowsPrec 0 e
showSymValue mp (ValBounded e) = gshowsPrec 0 e
showSymValue mp (ValPtr trgs tp)
  = showString "ptr[" .
    showStruct (showSymType mp) tp .
    showString "]" .
    showListWith
    (\(trg,(cond,idx)) -> showsPrec 0 trg .
                          showString " ~> " .
                          (case idx of
                            [] -> gshowsPrec 0 cond
                            _ -> gshowsPrec 0 cond .
                                 showListWith (gshowsPrec 0) idx))
    (Map.toList trgs)
showSymValue mp (ValThreadId trgs)
  = showString "thread-id" .
    showListWith
    (\(th,cond) -> case Map.lookup th mp of
      Just name -> showString name .
                   showString " ~> " .
                   gshowsPrec 0 cond) (Map.toList trgs)
showSymValue mp (ValCondition trgs)
  = showString "condition" .
    showListWith
    (\(th,cond) -> (case th of
                     Nothing -> showString "main"
                     Just th' -> case Map.lookup th' mp of
                       Just name -> showString name) .
                   showString " ~> " .
                   gshowsPrec 0 cond) (Map.toList trgs)
showSymValue mp (ValVector vals)
  = showListWith (showSymValue mp) vals

showAllocVal :: GShow e => Map (Ptr CallInst) String -> AllocVal e -> ShowS
showAllocVal mp (ValStatic els) = showListWith (showStruct (showSymValue mp)) els
--showAllocVal mp (ValDynamic 

instance Eq SymType where
  (==) TpBool TpBool = True
  (==) TpInt TpInt = True
  (==) (TpBounded b1) (TpBounded b2) = defaultEq b1 b2
  (==) (TpPtr trg1 tp1) (TpPtr trg2 tp2) = trg1==trg2 && tp1==tp2
  (==) (TpThreadId t1) (TpThreadId t2) = t1==t2
  (==) (TpCondition t1) (TpCondition t2) = t1==t2
  (==) (TpVector v1) (TpVector v2) = v1==v2
  (==) _ _ = False

instance Ord SymType where
  compare TpBool TpBool = EQ
  compare TpBool _ = LT
  compare _ TpBool = GT
  compare TpInt TpInt = EQ
  compare TpInt _ = LT
  compare _ TpInt = GT
  compare (TpBounded b1) (TpBounded b2) = defaultCompare b1 b2
  compare (TpBounded _) _ = LT
  compare _ (TpBounded _) = GT
  compare (TpPtr trg1 tp1) (TpPtr trg2 tp2) = case compare trg1 trg2 of
    EQ -> compare tp1 tp2
    r -> r
  compare (TpPtr _ _) _ = LT
  compare _ (TpPtr _ _) = GT
  compare (TpThreadId t1) (TpThreadId t2) = compare t1 t2
  compare (TpThreadId _) _ = LT
  compare _ (TpThreadId _) = GT
  compare (TpCondition t1) (TpCondition t2) = compare t1 t2
  compare (TpCondition _) _ = LT
  compare _ (TpCondition _) = GT
  compare (TpVector v1) (TpVector v2) = compare v1 v2

instance Show SymType where
  showsPrec _ TpBool = showString "Bool"
  showsPrec _ TpInt = showString "Int"
  showsPrec _ (TpBounded bw)
    = showString "(_ BitVec " . showsPrec 11 (naturalToInteger bw) . showChar ')'
  showsPrec p (TpPtr trg tp)
    = showParen (p>10) $ showString "Ptr " .
      showsPrec 11 (Map.keys trg) .
      showChar ' ' .
      showsPrec 11 tp
  showsPrec p (TpThreadId trg)
    = showParen (p>10) $ showString "Thread " .
      showsPrec 11 (Map.keys trg)
  showsPrec p (TpCondition trg)
    = showParen (p>10) $ showString "Condition " .
      showsPrec 11 (Map.keys trg)
  showsPrec p (TpVector vec)
    = showParen (p>10) $ showString "Vector " .
      showsPrec 11 vec
