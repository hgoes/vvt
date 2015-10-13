{-# LANGUAGE DeriveDataTypeable,TypeFamilies,ExistentialQuantification,
             ScopedTypeVariables,ViewPatterns,FlexibleInstances,DeriveFunctor,
             DeriveTraversable,DeriveFoldable #-}
module Realization.Threaded.Value where

import Gates

import Language.SMTLib2
import Language.SMTLib2.Internals
import Data.Map (Map)
import qualified Data.Map as Map
import LLVM.FFI
import Foreign.Ptr (Ptr)
import Data.Typeable
import Data.List (genericIndex,genericReplicate,genericLength)
import Prelude hiding (mapM)
import Data.Traversable
import Data.Foldable
import System.IO.Unsafe
import Data.Maybe (mapMaybe,catMaybes)
import Debug.Trace

data Struct a = Singleton { singleton :: a }
              | Struct { struct :: [Struct a] }
              deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

data SymVal = ValBool { valBool :: !(SMTExpr Bool) }
            | ValInt { valInt :: !(SMTExpr Integer) }
            | ValPtr { valPtr :: !(Map MemoryPtr (SMTExpr Bool,[SMTExpr Integer]))
                     , valPtrType :: !(Struct SymType) }
            | ValThreadId { valThreadId :: !(Map (Ptr CallInst) (SMTExpr Bool)) }
            | ValVector { valVector :: ![SymVal] }
            deriving (Eq,Ord,Show,Typeable)

data SymArray = ArrBool { arrBool :: SMTExpr (SMTArray (SMTExpr Integer) Bool) }
              | ArrInt { arrInt :: SMTExpr (SMTArray (SMTExpr Integer) Integer) }
              | ArrPtr { arrPtr :: Map MemoryPtr (SMTExpr (SMTArray (SMTExpr Integer) Bool),
                                                  [SMTExpr (SMTArray (SMTExpr Integer) Integer)])
                       , arrPtrType :: Struct SymType }
              | ArrThreadId { arrThreadId :: Map (Ptr CallInst) (SMTExpr (SMTArray (SMTExpr Integer) Bool)) }
              | ArrVector { arrVector :: [SymArray] }
              deriving (Eq,Ord,Show,Typeable)

data SymType = TpBool
             | TpInt
             | TpPtr { tpPtr :: Map MemoryPtr ()
                     , tpPtrType :: Struct SymType }
             | TpThreadId { tpThreadId :: Map (Ptr CallInst) () }
             | TpVector { tpVector :: [SymType] }
             deriving (Eq,Ord,Show,Typeable)

data AllocVal = ValStatic [Struct SymVal]
              | ValDynamic (Struct SymArray) (SMTExpr Integer)
              deriving (Eq,Ord,Show,Typeable)

data AllocType = TpStatic Integer (Struct SymType)
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

data MemoryAccessResult a
  = Success a
  | Invalid
  | TypeError
  | CondAccess (SMTExpr Bool) (MemoryAccessResult a) (MemoryAccessResult a)
  deriving (Eq,Ord,Typeable)

defaultIf :: SMTExpr Bool -> SymVal -> SymVal
defaultIf cond (ValBool v) = ValBool (ite cond (constant False) v)
defaultIf cond (ValInt v) = ValInt (ite cond (constant 0) v)
defaultIf cond (ValPtr ptr tp) = ValPtr (fmap (\(c,idx) -> (constant False,
                                                            fmap (const $ constant 0) idx)
                                              ) ptr) tp
defaultIf cond (ValThreadId mp) = ValThreadId $ fmap (const $ constant False) mp
defaultIf cond (ValVector vals) = ValVector $ fmap (defaultIf cond) vals

defaultValue :: SymType -> SymVal
defaultValue TpBool = ValBool (constant False)
defaultValue TpInt = ValInt (constant 0)
defaultValue (TpPtr mp tp)
  = ValPtr (Map.mapWithKey
            (\trg _ -> (constant False,[constant 0
                                       | DynamicAccess <- offsetPattern trg ])
            ) mp) tp
defaultValue (TpThreadId mp)
  = ValThreadId (fmap (const $ constant False) mp)
defaultValue (TpVector tps) = ValVector (fmap defaultValue tps)

valEq :: SymVal -> SymVal -> SMTExpr Bool
valEq (ValBool x) (ValBool y) = x .==. y
valEq (ValInt x) (ValInt y) = x .==. y
valEq (ValPtr x _) (ValPtr y _) = case catMaybes $ Map.elems mp of
  [] -> constant False
  [x] -> x
  xs -> app or' xs
  where
    mp = Map.intersectionWith ptrEq x y
    ptrEq (c1,i1) (c2,i2) = do
      conds <- idxEq i1 i2
      return $ app and' (c1:c2:conds)
    idxEq [] [] = Just []
    idxEq (x:xs) (y:ys) = do
      rest <- idxEq xs ys
      return $ (x.==.y):rest
valEq (ValThreadId x) (ValThreadId y) = case Map.elems mp of
  [] -> constant False
  [x] -> x
  xs -> app or' xs
  where
    mp = Map.intersectionWith condEq x y
    condEq c1 c2 = c1 .&&. c2
valEq (ValVector xs) (ValVector ys)
  = app and' (zipWith valEq xs ys)

idxList :: [AccessPattern] -> [SMTExpr Integer] -> [Either Integer (SMTExpr Integer)]
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

derefPointer :: [Either Integer (SMTExpr Integer)]
             -> Map MemoryPtr (SMTExpr Bool,[SMTExpr Integer])
             -> Map MemoryPtr (SMTExpr Bool,[SMTExpr Integer])
derefPointer idx mp
  = Map.fromListWith
    (\(c1,dyn1) (c2,dyn2) -> (c1 .||. c2,zipWith (ite c1) dyn1 dyn2))
    [ (loc { offsetPattern = pat },(cond,dyn))
    | (loc,(cond,dyns)) <- Map.toList mp
    , let (pat,dyn) = deref (offsetPattern loc) dyns idx ]
  where
    deref :: [AccessPattern] -> [SMTExpr Integer] -> [Either Integer (SMTExpr Integer)]
          -> ([AccessPattern],[SMTExpr Integer])
    deref [] [] is = toAccess is
    deref [StaticAccess n] [] (Left i:is)
      = let (restPat,restDyn) = toAccess is
        in (StaticAccess (n+i):restPat,
            restDyn)
    deref [StaticAccess n] [] (Right i:is)
      = let (restPat,restDyn) = toAccess is
        in (DynamicAccess:restPat,
            i + constant n:restDyn)
    deref [DynamicAccess] [n] (Left i:is)
      = let (restPat,restDyn) = toAccess is
        in (DynamicAccess:restPat,
            (n+constant i):restDyn)
    deref [DynamicAccess] [n] (Right i:is)
      = let (restPat,restDyn) = toAccess is
        in (DynamicAccess:restPat,
            (n+i):restDyn)
    deref (StaticAccess n:pat) dyn idx
      = let (restPat,restDyn) = deref pat dyn idx
        in (StaticAccess n:restPat,restDyn)
    deref (DynamicAccess:pat) (n:dyn) idx
      = let (restPat,restDyn) = deref pat dyn idx
        in (DynamicAccess:restPat,n:restDyn)
    toAccess (Left i:is) = let (restPat,restDyn) = toAccess is
                           in (StaticAccess i:restPat,restDyn)
    toAccess (Right i:is) = let (restPat,restDyn) = toAccess is
                            in (DynamicAccess:restPat,i:restDyn)
    toAccess [] = ([],[])

withOffset :: Show b
            => (Struct b -> c -> (MemoryAccessResult a,Struct b,c))
            -> Integer
            -> Struct b
            -> c
            -> (MemoryAccessResult a,Struct b,c)
withOffset f n (Struct xs) st = (res,Struct nxs,nst)
  where
    (res,nxs,nst) = withStruct n xs
    withStruct 0 (x:xs) = let (res,nx,nst) = f x st
                          in (res,nx:xs,nst)
    withStruct n (x:xs) = let (res,nxs,nst) = withStruct (n-1) xs
                          in (res,x:nxs,nst)
    withStruct _ [] = (Invalid,[],st)
withOffset _ n obj st = error $ "withOffset: Cannot index "++show obj++" with "++show n

symITE :: SMTExpr Bool -> SymVal -> SymVal -> SymVal
symITE cond (ValBool x) (ValBool y) = ValBool (ite cond x y)
symITE cond (ValInt x) (ValInt y) = ValInt (ite cond x y)
symITE cond (ValPtr x tp) (ValPtr y _)
  = ValPtr (Map.mergeWithKey (\_ (pc,pi) (qc,qi) -> Just (ite cond pc qc,
                                                          zipWith (ite cond) pi qi))
            (fmap (\(pc,pi) -> (pc .&&. cond,pi))) (fmap (\(qc,qi) -> (qc .&&. (not' cond),qi))) x y)
    tp
symITE cond (ValThreadId x) (ValThreadId y)
  = ValThreadId (Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
                 (fmap (.&&. cond)) (fmap (.&&. (not' cond))) x y)
symITE cond (ValVector v1) (ValVector v2)
  = ValVector $ zipWith (symITE cond) v1 v2
symITE cond v1 v2 = error $ "Cannot ITE differently typed values "++show v1++" and "++show v2

symITEs :: [(SymVal,SMTExpr Bool)] -> SymVal
symITEs [(val,_)] = val
symITEs ((val,c):rest) = symITE c val rval
  where
    rval = symITEs rest

arrITE :: SMTExpr Bool -> SymArray -> SymArray -> SymArray
arrITE cond (ArrBool x) (ArrBool y) = ArrBool (ite cond x y)
arrITE cond (ArrInt x) (ArrInt y) = ArrInt (ite cond x y)
arrITE cond (ArrPtr x tp) (ArrPtr y _)
  = ArrPtr (Map.mergeWithKey (\_ (pc,pi) (qc,qi) -> Just (ite cond pc qc,
                                                          zipWith (ite cond) pi qi))
            (fmap (\(pc,pi) -> (ite cond pc (constArray (constant False) ()),pi)))
            (fmap (\(qc,qi) -> (ite cond (constArray (constant False) ()) qc,qi))) x y)
    tp
arrITE cond (ArrThreadId x) (ArrThreadId y)
  = ArrThreadId $ Map.intersectionWith (ite cond) x y
arrITE cond (ArrVector x) (ArrVector y)
  = ArrVector $ zipWith (arrITE cond) x y

structITE :: (SMTExpr Bool -> b -> b -> b)
          -> SMTExpr Bool -> Struct b -> Struct b -> Struct b
structITE ite cond (Singleton x) (Singleton y)
  = Singleton $ ite cond x y
structITE ite cond (Struct xs) (Struct ys)
  = Struct $ zipWith (structITE ite cond) xs ys

structITEs :: ([(b,SMTExpr Bool)] -> b)
          -> [(Struct b,SMTExpr Bool)]
          -> Struct b
structITEs comb xs@(fst.head -> Singleton _) = Singleton (comb $ fmap (\(Singleton x,c) -> (x,c)) xs)
structITEs comb xs = Struct (zipStructs (fmap (\(Struct x,c) -> (x,c)) xs))
  where
    zipStructs (([],_):_) = []
    zipStructs xs = (structITEs comb (fmap (\(x:_,c) -> (x,c)) xs)):
                    zipStructs (fmap (\(_:xs,c) -> (xs,c)) xs)

withDynOffset :: (SMTExpr Bool -> b -> b -> b)
               -> (Struct b -> c -> (MemoryAccessResult a,Struct b,c))
               -> SMTExpr Integer
               -> [Struct b]
               -> c
               -> (MemoryAccessResult a,[Struct b],c)
withDynOffset ite f n xs st = with 0 xs st
  where
    with i (x:xs) st = let (res,nx,st1) = f x st
                           (ress,nxs,st2) = with (i+1) xs st1
                           cond = n .==. (constant i)
                       in (CondAccess cond res ress,
                           structITE ite cond nx x:nxs,
                           st2)
    with i [] st = (Invalid,[],st)

accessStruct :: Show b
              => (SMTExpr Bool -> b -> b -> b)
              -> (b -> c -> (MemoryAccessResult a,b,c))
              -> [Either Integer (SMTExpr Integer)]
              -> Struct b
              -> c
              -> (MemoryAccessResult a,Struct b,c)
accessStruct _ f [] (Singleton x) st = (res,Singleton nx,nst)
  where
    (res,nx,nst) = f x st
accessStruct ite f (Left i:is) s st
  = withOffset (accessStruct ite f is) i s st
accessStruct ite f (Right i:is) (Struct s) st
  = (res,Struct ns,nst)
  where
    (res,ns,nst) = withDynOffset ite (accessStruct ite f is) i s st

accessArray :: (SymVal -> c -> (MemoryAccessResult a,SymVal,c))
            -> SMTExpr Integer
            -> SymArray
            -> c
            -> (MemoryAccessResult a,SymArray,c)
accessArray f idx arr st
  = (res,insertValue idx nval arr,nst)
  where
    (res,nval,nst) = f (extractValue idx arr) st

extractValue :: SMTExpr Integer -> SymArray -> SymVal
extractValue idx (ArrBool arr) = ValBool (select arr idx)
extractValue idx (ArrInt arr) = ValInt (select arr idx)
extractValue idx (ArrPtr arr tp)
  = ValPtr (fmap (\(conds,idxs) -> (select conds idx,fmap (\i -> select i idx) idxs)) arr) tp
extractValue idx (ArrThreadId arr)
  = ValThreadId (fmap (\conds -> select conds idx) arr)
extractValue idx (ArrVector arrs)
  = ValVector (fmap (extractValue idx) arrs)

insertValue :: SMTExpr Integer -> SymVal -> SymArray -> SymArray
insertValue idx (ValBool b) (ArrBool arr) = ArrBool (store arr idx b)
insertValue idx (ValInt i) (ArrInt arr) = ArrInt (store arr idx i)
insertValue idx (ValPtr p _) (ArrPtr ps tp)
  = ArrPtr (Map.intersectionWith
            (\(ncond,noff) (conds,offs)
             -> (store conds idx ncond,
                 zipWith (\noff offs -> store offs idx noff) noff offs)
            ) p ps) tp
insertValue idx (ValThreadId t) (ArrThreadId ts)
  = ArrThreadId (Map.intersectionWith
                 (\nval arr -> store arr idx nval)
                 t ts)
insertValue idx (ValVector vals) (ArrVector arr)
  = ArrVector (zipWith (insertValue idx) vals arr)

{-accessAlloc' :: (SymVal -> c -> (a,SymVal,c))
             -> [Either Integer (SMTExpr Integer)]
             -> AllocVal
             -> c
             -> (MemoryAccessResult a,AllocVal,c)
accessAlloc' f (Left i:is) (ValStatic s) st
  =
  where-}
    

accessAlloc :: (SymVal -> c -> (MemoryAccessResult a,SymVal,c))
            -> [Either Integer (SMTExpr Integer)]
            -> AllocVal
            -> c
            -> (MemoryAccessResult a,AllocVal,c)
accessAlloc f idx@(Left i:is) (ValStatic s) st
  = (res,ValStatic ns,nst)
  where
    (res,ns,nst) = accessStatic i s
    accessStatic 0 (s:ss) = let (res,ns,nst) = accessStruct symITE f is s st
                            in (res,ns:ss,nst)
    accessStatic n (s:ss) = let (res,nss,nst) = accessStatic (n-1) ss
                            in (res,s:nss,nst)
    accessStatic _ [] = (Invalid,[],st)
accessAlloc f (Right i:is) (ValStatic s) st
  = (res,ValStatic ns,nst)
  where
    (res,ns,nst) = withDynOffset symITE (accessStruct symITE f is) i s st
accessAlloc f [] (ValStatic (x:xs)) st
  = (res,ValStatic $ nx:xs,nst)
  where
    (res,nx,nst) = accessStruct symITE f [] x st
accessAlloc f (i:is) (ValDynamic arrs sz) st
  = (res,ValDynamic narrs sz,nst)
  where
    (res,narrs,nst) = accessStruct arrITE (accessArray nf i') is arrs st
    nf val st = let (acc,res,nst) = f val st
                in (CondAccess (i' .>=. sz) Invalid acc,res,nst)
    i' = case i of
      Left i -> constant i
      Right i -> i

accessAllocTyped :: SymType
                 -> (SymVal -> c -> (a,SymVal,c))
                 -> [Either Integer (SMTExpr Integer)]
                 -> AllocVal
                 -> c
                 -> (MemoryAccessResult a,AllocVal,c)
accessAllocTyped tp f idx val st
  = accessAlloc (\val st -> if sameType tp (extractArgAnnotation val)
                            then (let (obj,nval,nst) = f val st
                                  in (Success obj,nval,nst))
                            else (TypeError,val,st)
                ) idx val st

accessAllocTypedIgnoreErrors :: SymType
                             -> (SymVal -> c -> (SymVal,c))
                             -> [Either Integer (SMTExpr Integer)]
                             -> AllocVal
                             -> c
                             -> (SymVal,AllocVal,c)
accessAllocTypedIgnoreErrors tp f idx val st
  = (combine res,nval,nst)
  where
    (res,nval,nst) = accessAllocTyped tp (\val st -> let (nval,nst) = f val st
                                                     in (nval,nval,nst)) idx val st
    combine (Success x) = x
    combine (CondAccess c x y) = symITE c (combine x) (combine y)
    combine _ = defaultValue tp

sameType :: SymType -> SymType -> Bool
sameType TpBool TpBool = True
sameType TpInt TpInt = True
sameType (TpPtr _ tp1) (TpPtr _ tp2) = sameStructType tp1 tp2
sameType (TpThreadId _) (TpThreadId _) = True
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

sameValueType :: Struct SymVal -> Struct SymVal -> Bool
sameValueType x1 x2 = sameStructType
                      (extractArgAnnotation x1)
                      (extractArgAnnotation x2)

sameArrayType :: Struct SymArray -> Struct SymArray -> Bool
sameArrayType x1 x2 = sameStructType
                      (extractArgAnnotation x1)
                      (extractArgAnnotation x2)

addSymGate :: Args inp => GateMap inp -> SymType -> (inp -> SymVal) -> Maybe String
              -> (SymVal,GateMap inp)
addSymGate gts TpBool f name
  = let (expr,ngts) = addGate gts (Gate { gateTransfer = valBool.f
                                        , gateAnnotation = ()
                                        , gateName = name })
    in (ValBool expr,ngts)
addSymGate gts TpInt f name
  = let (expr,ngts) = addGate gts (Gate { gateTransfer = valInt.f
                                        , gateAnnotation = ()
                                        , gateName = name })
    in (ValInt expr,ngts)
addSymGate gts (TpPtr trgs tp) f name
  = let (ngts,trgExprs) = Map.mapAccumWithKey
                          (\gts loc _ -> let gt = Gate { gateTransfer = \x -> case Map.lookup loc (valPtr $ f x) of
                                                                                Just (r,_) -> r
                                                                                Nothing -> constant False
                                                       , gateAnnotation = ()
                                                       , gateName = name }
                                             (cond,gts1) = addGate gts gt
                                             ((_,gts2),idx) = mapAccumL
                                                              (\(n,gts) _ -> let gt = Gate { gateTransfer = (!!n).snd.(Map.! loc).valPtr.f
                                                                                           , gateAnnotation = ()
                                                                                           , gateName = name }
                                                                                 (idx,ngts) = addGate gts gt
                                                                             in ((n+1,ngts),idx)
                                                              ) (0,gts1) [ () | DynamicAccess <- offsetPattern loc ]
                                         in (gts2,(cond,idx))
                          ) gts trgs
    in (ValPtr trgExprs tp,ngts)
addSymGate gts (TpThreadId trgs) f name
  = let (ngts,trgExprs) = Map.mapAccumWithKey
                          (\gts th _ -> let gt = Gate { gateTransfer = (Map.! th).valThreadId.f
                                                      , gateAnnotation = ()
                                                      , gateName = name }
                                            (cond,ngts) = addGate gts gt
                                        in (ngts,cond)
                          ) gts trgs
    in (ValThreadId trgExprs,ngts)
addSymGate gts (TpVector tps) f name
  = let (ngts,nvals) = mapAccumL (\gts (tp,i) -> let (val,ngts) = addSymGate gts tp ((!!i).valVector.f) name
                                                 in (ngts,val)
                                 ) gts (zip tps [0..])
    in (ValVector nvals,ngts)

addSymArrGate :: Args inp => GateMap inp -> SymType -> (inp -> SymArray) -> Maybe String
              -> (SymArray,GateMap inp)
addSymArrGate gts TpBool f name
  = let (arr,ngts) = addGate gts (Gate { gateTransfer = arrBool.f
                                       , gateAnnotation = ((),())
                                       , gateName = name })
    in (ArrBool arr,ngts)
addSymArrGate gts TpInt f name
  = let (arr,ngts) = addGate gts (Gate { gateTransfer = arrInt.f
                                       , gateAnnotation = ((),())
                                       , gateName = name })
    in (ArrInt arr,ngts)
addSymArrGate gts (TpPtr trgs tp) f name = (ArrPtr conds tp,ngts)
  where
    (ngts,conds) = Map.mapAccumWithKey
                   (\gts loc _ -> addPtrGate gts loc) gts trgs
    addPtrGate gts loc = let gt = Gate { gateTransfer = fst.(Map.! loc).arrPtr.f
                                       , gateAnnotation = ((),())
                                       , gateName = name }
                             (cond,gts1) = addGate gts gt
                             ((_,gts2),idx) = mapAccumL (addIdxGate loc) (0,gts1)
                                              [ () | DynamicAccess <- offsetPattern loc ]
                         in (gts2,(cond,idx))
    addIdxGate loc (n,gts) _ = let gt = Gate { gateTransfer = (!!n).snd.(Map.! loc).arrPtr.f
                                             , gateAnnotation = ((),())
                                             , gateName = name }
                                   (idx,ngts) = addGate gts gt
                               in ((n+1,ngts),idx)
--addSymArrGate gts (TpThreadId trgs) f name = (ArrThreadId conds,ngts)

addStructGate :: Args inp => (GateMap inp -> a -> (inp -> b) -> Maybe String -> (b,GateMap inp))
              -> GateMap inp -> Struct a
              -> (inp -> Struct b) -> Maybe String
              -> (Struct b,GateMap inp)
addStructGate add gts (Singleton tp) f name
  = let (nval,ngts) = add gts tp (singleton.f) name
    in (Singleton nval,ngts)
addStructGate add gts (Struct tps) f name
  = let ((ngts,_),nvals) = mapAccumL
                           (\(gts,n) tp
                            -> let (nval,ngts) = addStructGate add gts tp ((!!n).struct.f) name
                               in ((ngts,n+1),nval)
                           ) (gts,0) tps
    in (Struct nvals,ngts)

addArgGate :: (Args inp,Args outp) => GateMap inp
           -> ArgAnnotation outp
           -> (inp -> outp)
           -> Maybe String
           -> (outp,GateMap inp)
addArgGate gts ann (f::inp -> outp) name = (arg,ngts)
  where
    tps = getTypes (undefined::outp) ann
    ((_,ngts),vals) = mapAccumL addElGate (0,gts) tps
    Just (arg,[]) = toArgs ann vals
    addElGate (n,gts) (ProxyArg (_::a) ann)
      = let gt :: Gate inp a
            gt = Gate { gateTransfer = castUntypedExpr.(!!n).fromArgs.f
                      , gateAnnotation = ann
                      , gateName = name }
            (expr,ngts) = addGate gts gt
        in ((n+1,ngts),UntypedExpr expr)

argITE :: Args arg => SMTExpr Bool -> arg -> arg -> arg
argITE cond x y = res
  where
    x' = fromArgs x
    y' = fromArgs y
    ites = zipWith (\x y -> entype (\x' -> UntypedExpr $ ite cond x' (castUntypedExpr y)) x
                   ) x' y'
    Just (res,[]) = toArgs (extractArgAnnotation x) ites

argITEs :: Args arg => [(arg,SMTExpr Bool)] -> arg
argITEs [(x,_)] = x
argITEs ((x,c):xs) = argITE c x (argITEs xs)

ptrAnnotation :: Map MemoryPtr () -> Map MemoryPtr ((),[()])
ptrAnnotation = Map.mapWithKey (\loc _ -> ((),[() | DynamicAccess <- offsetPattern loc]))

ptrArrAnnotation :: Map MemoryPtr () -> Map MemoryPtr (((),()),[((),())])
ptrArrAnnotation = Map.mapWithKey (\loc _ -> (((),()),[((),()) | DynamicAccess <- offsetPattern loc]))

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

patternMatch :: [AccessPattern] -> [AccessPattern]
             -> [SMTExpr Integer] -> [SMTExpr Integer]
             -> Maybe [SMTExpr Bool]
patternMatch [] [] [] [] = Just []
patternMatch (StaticAccess x:xs) (StaticAccess y:ys) ix iy
  | x==y = patternMatch xs ys ix iy
  | otherwise = Nothing
patternMatch (DynamicAccess:xs) (StaticAccess y:ys) (ix:ixs) iy = do
  rest <- patternMatch xs ys ixs iy
  return $ (ix .==. (constant y)):rest
patternMatch (StaticAccess x:xs) (DynamicAccess:ys) ix (iy:iys) = do
  rest <- patternMatch xs ys ix iys
  return $ (iy .==. (constant x)):rest
patternMatch (DynamicAccess:xs) (DynamicAccess:ys) (ix:ixs) (iy:iys) = do
  rest <- patternMatch xs ys ixs iys
  return $ (ix .==. iy):rest
patternMatch _ _ _ _ = Nothing

allocITE :: SMTExpr Bool -> AllocVal -> AllocVal -> AllocVal
allocITE cond (ValStatic xs) (ValStatic ys)
  = ValStatic (ites xs ys)
  where
    ites [] [] = []
    ites (x:xs) (y:ys) = (structITE symITE cond x y):ites xs ys
allocITE cond (ValDynamic x sx) (ValDynamic y sy)
  = ValDynamic (structITE arrITE cond x y) (ite cond sx sy)

instance Args SymVal where
  type ArgAnnotation SymVal = SymType
  foldExprs f s ~(ValBool e) TpBool = do
    (s',e') <- f s e ()
    return (s',ValBool e')
  foldExprs f s ~(ValInt e) TpInt = do
    (s',e') <- f s e ()
    return (s',ValInt e')
  foldExprs f s ~(ValPtr conds _) (TpPtr ptrs tp) = do
    (s',conds') <- foldExprs f s conds (ptrAnnotation ptrs)
    return (s',ValPtr conds' tp)
  foldExprs f s ~(ValThreadId conds) (TpThreadId ths) = do
    (s',conds') <- foldExprs f s conds ths
    return (s',ValThreadId conds')
  foldExprs f s ~(ValVector vals) (TpVector tps) = do
    (s',vals') <- foldExprs f s vals tps
    return (s',ValVector vals')
  foldsExprs f s lst TpBool = do
    let lst' = fmap (\(x,y) -> (valBool x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ()
    return (ns,fmap ValBool rlst,ValBool res)
  foldsExprs f s lst TpInt = do
    let lst' = fmap (\(x,y) -> (valInt x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ()
    return (ns,fmap ValInt rlst,ValInt res)
  foldsExprs f s lst (TpPtr conds tp) = do
    let lst' = fmap (\(x,y) -> (valPtr x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' (ptrAnnotation conds)
    return (ns,fmap (\x -> ValPtr x tp) rlst,ValPtr res tp)
  foldsExprs f s lst (TpVector tps) = do
    let lst' = fmap (\(x,y) -> (valVector x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' tps
    return (ns,fmap ValVector rlst,ValVector res)
  extractArgAnnotation (ValBool _) = TpBool
  extractArgAnnotation (ValInt _) = TpInt
  extractArgAnnotation (ValPtr conds tp) = TpPtr (fmap (const ()) conds) tp
  extractArgAnnotation (ValThreadId conds) = TpThreadId (fmap (const ()) conds)
  extractArgAnnotation (ValVector vals) = TpVector (fmap extractArgAnnotation vals)
  toArgs TpBool es = case es of
    [] -> Nothing
    e:es -> do
      e' <- entype cast e
      return (ValBool e',es)
  toArgs TpInt es = case es of
    [] -> Nothing
    e:es -> do
      e' <- entype cast e
      return (ValInt e',es)
  toArgs (TpPtr trgs tp) es = do
    (conds,rest) <- toArgs (ptrAnnotation trgs) es
    return (ValPtr conds tp,rest)
  toArgs (TpThreadId ths) es = do
    (conds,rest) <- toArgs ths es
    return (ValThreadId conds,rest)
  toArgs (TpVector tps) es = do
    (vals,rest) <- toArgs tps es
    return (ValVector vals,rest)
  getTypes _ TpBool = [ProxyArg (undefined::Bool) ()]
  getTypes _ TpInt = [ProxyArg (undefined::Integer) ()]
  getTypes _ (TpPtr trgs tp) = getTypes (undefined::Map MemoryPtr (SMTExpr Bool)) trgs
  getTypes _ (TpThreadId ths) = getTypes (undefined::Map (Ptr CallInst) (SMTExpr Bool)) ths
  getTypes _ (TpVector tps) = getTypes (undefined::[SymVal]) tps
  fromArgs (ValBool e) = [UntypedExpr e]
  fromArgs (ValInt e) = [UntypedExpr e]
  fromArgs (ValPtr conds _) = fromArgs conds
  fromArgs (ValThreadId conds) = fromArgs conds
  fromArgs (ValVector vals) = fromArgs vals

instance Args SymArray where
  type ArgAnnotation SymArray = SymType
  foldExprs f s ~(ArrBool e) TpBool = do
    (s',e') <- f s e ((),())
    return (s',ArrBool e')
  foldExprs f s ~(ArrInt e) TpInt = do
    (s',e') <- f s e ((),())
    return (s',ArrInt e')
  foldExprs f s ~(ArrPtr conds _) (TpPtr ptrs tp) = do
    (s',conds') <- foldExprs f s conds (ptrArrAnnotation ptrs)
    return (s',ArrPtr conds' tp)
  foldExprs f s ~(ArrThreadId conds) (TpThreadId ths) = do
    (s',conds') <- foldExprs f s conds (fmap (\_ -> ((),())) ths)
    return (s',ArrThreadId conds')
  foldExprs f s ~(ArrVector arrs) (TpVector tps) = do
    (s',arrs') <- foldExprs f s arrs tps
    return (s',ArrVector arrs')
  foldsExprs f s lst TpBool = do
    let lst' = fmap (\(ArrBool x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ((),())
    return (ns,fmap ArrBool rlst,ArrBool res)
  foldsExprs f s lst TpInt = do
    let lst' = fmap (\(ArrInt x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ((),())
    return (ns,fmap ArrInt rlst,ArrInt res)
  foldsExprs f s lst (TpPtr conds tp) = do
    let lst' = fmap (\(ArrPtr x _,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' (ptrArrAnnotation conds)
    return (ns,fmap (\x -> ArrPtr x tp) rlst,ArrPtr res tp)
  foldsExprs f s lst (TpThreadId conds) = do
    let lst' = fmap (\(ArrThreadId x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' (fmap (\_ -> ((),())) conds)
    return (ns,fmap ArrThreadId rlst,ArrThreadId res)
  foldsExprs f s lst (TpVector tps) = do
    let lst' = fmap (\(ArrVector x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' tps
    return (ns,fmap ArrVector rlst,ArrVector res)
  extractArgAnnotation (ArrBool _) = TpBool
  extractArgAnnotation (ArrInt _) = TpInt
  extractArgAnnotation (ArrPtr mp tp) = TpPtr (fmap (const ()) mp) tp
  extractArgAnnotation (ArrThreadId mp) = TpThreadId (fmap (const ()) mp)
  extractArgAnnotation (ArrVector arrs) = TpVector (fmap extractArgAnnotation arrs)
  toArgs TpBool es = do
    (arr,rest) <- toArgs ((),()) es
    return (ArrBool arr,rest)
  toArgs TpInt es = do
    (arr,rest) <- toArgs ((),()) es
    return (ArrInt arr,rest)
  toArgs (TpPtr trgs tp) es = do
    (conds,rest) <- toArgs (ptrArrAnnotation trgs) es
    return (ArrPtr conds tp,rest)
  toArgs (TpThreadId trgs) es = do
    (conds,rest) <- toArgs (fmap (const ((),())) trgs) es
    return (ArrThreadId conds,rest)
  toArgs (TpVector arrs) es = do
    (arrs,rest) <- toArgs arrs es
    return (ArrVector arrs,rest)
  getTypes _ TpBool = [ProxyArg (undefined::SMTArray (SMTExpr Integer) Bool) ((),())]
  getTypes _ TpInt = [ProxyArg (undefined::SMTArray (SMTExpr Integer) Integer) ((),())]
  getTypes _ (TpPtr trgs tp)
    = getTypes (undefined::Map MemoryPtr (SMTExpr (SMTArray (SMTExpr Integer) Bool)))
      (fmap (const ((),())) trgs)
  getTypes _ (TpThreadId trgs)
    = getTypes (undefined::Map (Ptr CallInst) (SMTExpr (SMTArray (SMTExpr Integer) Bool)))
      (fmap (const ((),())) trgs)
  getTypes _ (TpVector tps)
    = getTypes (undefined::[SymArray]) tps
  fromArgs (ArrBool arr) = [UntypedExpr arr]
  fromArgs (ArrInt arr) = [UntypedExpr arr]
  fromArgs (ArrPtr arrs _) = fromArgs arrs
  fromArgs (ArrThreadId arrs) = fromArgs arrs
  fromArgs (ArrVector arrs) = fromArgs arrs
  
instance Args a => Args (Struct a) where
  type ArgAnnotation (Struct a) = Struct (ArgAnnotation a)
  foldExprs f s ~(Singleton v) (Singleton tp) = do
    (s',nv) <- foldExprs f s v tp
    return (s',Singleton nv)
  foldExprs f s ~(Struct xs) (Struct tps) = do
    (s',nxs) <- foldExprs f s xs tps
    return (s',Struct nxs)
  foldsExprs f s lst (Singleton tp) = do
    let lst' = fmap (\(Singleton x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' tp
    return (ns,fmap Singleton rlst,Singleton res)
  foldsExprs f s lst (Struct tps) = do
    let lst' = fmap (\(Struct x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' tps
    return (ns,fmap Struct rlst,Struct res)
  extractArgAnnotation (Singleton x) = Singleton (extractArgAnnotation x)
  extractArgAnnotation (Struct xs) = Struct (fmap extractArgAnnotation xs)
  toArgs (Singleton tp) es = do
    (val,rest) <- toArgs tp es
    return (Singleton val,rest)
  toArgs (Struct tps) es = do
    (vals,rest) <- toArgs tps es
    return (Struct vals,rest)
  getTypes (_::Struct a) (Singleton tp) = getTypes (undefined::a) tp
  getTypes (_::Struct a) (Struct tps) = getTypes (undefined::[Struct a]) tps
  fromArgs (Singleton x) = fromArgs x
  fromArgs (Struct vals) = fromArgs vals

instance Args AllocVal where
  type ArgAnnotation AllocVal = AllocType
  foldExprs f s ~(ValStatic xs) (TpStatic sz tp) = do
    (s',xs') <- foldExprs f s xs (genericReplicate sz tp)
    return (s',ValStatic xs')
  foldExprs f s ~(ValDynamic arr sz) (TpDynamic tp) = do
    (s',(nsz,narr)) <- foldExprs f s (sz,arr) ((),tp)
    return (s',ValDynamic narr nsz)
  foldsExprs f s lst (TpStatic sz tp) = do
    let lst' = fmap (\(ValStatic x,y) -> (x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' (genericReplicate sz tp)
    return (ns,fmap ValStatic rlst,ValStatic res)
  foldsExprs f s lst (TpDynamic tp) = do
    let lst' = fmap (\(ValDynamic arr sz,y) -> ((sz,arr),y)) lst
    (ns,rlst,(rsz,rarr)) <- foldsExprs f s lst' ((),tp)
    return (ns,fmap (\(nsz,narr) -> ValDynamic narr nsz) rlst,ValDynamic rarr rsz)
  extractArgAnnotation (ValStatic xs)
    = TpStatic (genericLength xs) (extractArgAnnotation $ head xs)
  extractArgAnnotation (ValDynamic arr sz)
    = TpDynamic (extractArgAnnotation arr)
  toArgs (TpStatic sz tp) es = do
    (xs,rest) <- toArgs (genericReplicate sz tp) es
    return (ValStatic xs,rest)
  toArgs (TpDynamic tp) es = do
    ((sz,arr),rest) <- toArgs ((),tp) es
    return (ValDynamic arr sz,rest)
  getTypes _ (TpStatic sz tp)
    = getTypes (undefined::[Struct SymVal]) (genericReplicate sz tp)
  getTypes _ (TpDynamic tp)
    = [ProxyArg (undefined::Integer) ()]++
      getTypes (undefined::Struct SymArray) tp
  fromArgs (ValStatic xs) = fromArgs xs
  fromArgs (ValDynamic arrs sz)
    = [UntypedExpr sz]++fromArgs arrs

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
  n <- getNameString v
  return $ showString n

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
