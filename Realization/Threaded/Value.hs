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
import Data.Maybe (mapMaybe)
import Debug.Trace

data Struct a = Singleton { singleton :: a }
              | Struct { struct :: [Struct a] }
              deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

data SymVal = ValBool { valBool :: SMTExpr Bool }
            | ValInt { valInt :: SMTExpr Integer }
            | ValPtr { valPtr :: Map MemoryPtr (SMTExpr Bool,[SMTExpr Integer])
                     , valPtrType :: Struct SymType }
            | ValThreadId { valThreadId :: Map (Ptr CallInst) (SMTExpr Bool) }
            deriving (Eq,Ord,Show,Typeable)

data SymArray = ArrBool { arrBool :: SMTExpr (SMTArray (SMTExpr Integer) Bool) }
              | ArrInt { arrInt :: SMTExpr (SMTArray (SMTExpr Integer) Integer) }
              | ArrPtr { arrPtr :: Map MemoryPtr (SMTExpr (SMTArray (SMTExpr Integer) Bool),
                                                  [SMTExpr (SMTArray (SMTExpr Integer) Integer)])
                       , arrPtrType :: Struct SymType }
              | ArrThreadId { arrThreadId :: Map (Ptr CallInst) (SMTExpr (SMTArray (SMTExpr Integer) Bool)) }
              deriving (Eq,Ord,Show,Typeable)

data SymType = TpBool
             | TpInt
             | TpPtr { tpPtr :: Map MemoryPtr ()
                     , tpPtrType :: Struct SymType }
             | TpThreadId { tpThreadId :: Map (Ptr CallInst) () }
             deriving (Eq,Ord,Show,Typeable)

data AllocVal = ValStatic [Struct SymVal]
              | ValDynamic (Struct SymArray) (SMTExpr Integer)
              deriving (Eq,Ord,Show,Typeable)

data AllocType = TpStatic Integer (Struct SymType)
               | TpDynamic (Struct SymType)
               deriving (Eq,Ord,Show,Typeable)

type MemoryLoc = Either (Ptr Instruction) (Ptr GlobalVariable)

data MemoryPtr = MemoryPtr { memoryLoc :: MemoryLoc
                           , offsetPattern :: [AccessPattern]
                           } deriving (Eq,Ord,Typeable)

data AccessPattern = StaticAccess Integer
                   | DynamicAccess
                   deriving (Eq,Ord,Typeable)

defaultIf :: SMTExpr Bool -> SymVal -> SymVal
defaultIf cond (ValBool v) = ValBool (ite cond (constant False) v)
defaultIf cond (ValInt v) = ValInt (ite cond (constant 0) v)
defaultIf cond (ValPtr ptr tp) = ValPtr (fmap (\(c,idx) -> (constant False,
                                                            fmap (const $ constant 0) idx)
                                              ) ptr) tp
defaultIf cond (ValThreadId mp) = ValThreadId $ fmap (const $ constant False) mp

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


withOffset :: (Struct b -> Maybe (a,Struct b)) -> Integer
           -> Struct b -> Maybe (a,Struct b)
withOffset f n (Struct xs) = do
  (res,nxs) <- withStruct n xs
  return (res,Struct nxs)
  where
    withStruct 0 (x:xs) = do
      (res,nx) <- f x
      return (res,nx:xs)
    withStruct n (x:xs) = do
      (res,nxs) <- withStruct (n-1) xs
      return (res,x:nxs)

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
              -> ([(a,SMTExpr Bool)] -> a)
              -> (Struct b -> Maybe (a,Struct b))
              -> SMTExpr Integer
              -> Struct b -> Maybe (a,Struct b)
withDynOffset ite comb f n (Struct xs)
  = case mapMaybe (\(_,r) -> case r of
                              Just (c,res,_) -> Just (res,c)
                              Nothing -> Nothing
                  ) lst of
     [] -> Nothing
     conds -> Just (comb conds,
                    Struct $ fmap (\(x,r) -> case r of
                                    Just (c,_,nx) -> structITE ite c nx x
                                    Nothing -> x
                                  ) lst)
  where
    lst = zipWith (\i x -> (x,case f x of
                             Just (res,nx) -> Just (n .==. (constant i),res,nx)
                             Nothing -> Nothing)
                  ) [0..] xs

accessStruct :: (SMTExpr Bool -> b -> b -> b)
             -> ([(a,SMTExpr Bool)] -> a)
             -> (b -> Maybe (a,b))
             -> [Either Integer (SMTExpr Integer)]
             -> Struct b
             -> Maybe (a,Struct b)
accessStruct _ _ f [] (Singleton x) = do
  (res,nx) <- f x
  return (res,Singleton nx)
accessStruct ite comb f (Left i:is) s
  = withOffset (accessStruct ite comb f is) i s
accessStruct ite comb f (Right i:is) s
  = withDynOffset ite comb (accessStruct ite comb f is) i s

accessArray :: (SymVal -> Maybe (a,SymVal)) -> SMTExpr Integer
            -> SymArray
            -> Maybe (a,SymArray)
accessArray f idx (ArrBool arr) = do
  (res,ValBool nval) <- f (ValBool $ select arr idx)
  return (res,ArrBool $ store arr idx nval)
accessArray f idx (ArrInt arr) = do
  (res,ValInt nval) <- f (ValInt $ select arr idx)
  return (res,ArrInt $ store arr idx nval)
accessArray f idx (ArrPtr arr tp) = do
  let val = fmap (\(conds,idxs) -> (select conds idx,fmap (\i -> select i idx) idxs)) arr
  (res,ValPtr nval _) <- f (ValPtr val tp)
  let narr = Map.intersectionWith
             (\(ncond,noff) (conds,offs)
              -> (store conds idx ncond,
                  zipWith (\noff offs -> store offs idx noff) noff offs))
             nval arr
  return (res,ArrPtr narr tp)
accessArray f idx (ArrThreadId arr) = do
  let val = fmap (\arr -> select arr idx) arr
  (res,ValThreadId nval) <- f (ValThreadId val)
  let narr = Map.intersectionWith
             (\nval arr -> store arr idx nval)
             nval arr
  return (res,ArrThreadId narr)

accessAlloc :: ([(a,SMTExpr Bool)] -> a)
            -> (SymVal -> Maybe (a,SymVal))
            -> [Either Integer (SMTExpr Integer)]
            -> AllocVal
            -> Maybe (a,AllocVal)
accessAlloc comb f idx@(Left i:is) (ValStatic s)
  = do
  (res,ns) <- accessStatic i s
  return (res,ValStatic ns)
  where
    accessStatic 0 (s:ss) = do
      (res,ns) <- accessStruct symITE comb f is s
      return (res,ns:ss)
    accessStatic n (s:ss) = do
      (res,nss) <- accessStatic (n-1) ss
      return (res,s:nss)
accessAlloc comb f (Right i:is) (ValStatic s)
  = case mapMaybe (\(_,r) -> case r of
                    Nothing -> Nothing
                    Just (c,res,_) -> Just (res,c)
                  ) lst of
     [] -> Nothing
     conds -> Just (comb conds,
                    ValStatic $ fmap (\(x,r) -> case r of
                                       Nothing -> x
                                       Just (c,_,nx) -> structITE symITE c nx x
                                     ) lst)
  where
    lst = zipWith (\j x -> (x,case accessStruct symITE comb f is x of
                               Nothing -> Nothing
                               Just (res,nx) -> Just (i .==. (constant j),res,nx))
                  ) [0..] s
accessAlloc comb f [] (ValStatic (x:xs)) = do
  (res,nx) <- accessStruct symITE comb f [] x
  return (res,ValStatic (nx:xs))
accessAlloc comb f (i:is) (ValDynamic arrs sz)
  = do
  (res,narrs) <- accessStruct arrITE comb (accessArray nf i') is arrs
  return (res,ValDynamic narrs sz)
  where
     -- Make sure that the model stays deterministic by loading default values for out-of-bounds indices
    nf val = f (defaultIf ((i' .>=. sz) .||. (i' .<. 0)) val)
    i' = case i of
      Left i -> constant i
      Right i -> i

accessAllocTyped :: SymType
                 -> ([(a,SMTExpr Bool)] -> a)
                 -> (SymVal -> (a,SymVal))
                 -> [Either Integer (SMTExpr Integer)]
                 -> AllocVal
                 -> (a,AllocVal)
accessAllocTyped tp comb f idx val
  = case accessAlloc comb (\val -> if sameType tp (extractArgAnnotation val)
                                   then Just (f val)
                                   else Nothing
                          ) idx val of
     Just res -> res
     Nothing -> error $ "accessAllocTyped: Type error while accessing "++show val++" with "++show idx

sameType :: SymType -> SymType -> Bool
sameType TpBool TpBool = True
sameType TpInt TpInt = True
sameType (TpPtr _ tp1) (TpPtr _ tp2) = sameStructType tp1 tp2
sameType (TpThreadId _) (TpThreadId _) = True
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
                          (\gts loc _ -> let gt = Gate { gateTransfer = fst.(Map.! loc).valPtr.f
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
argITE cond x y = trace ("argITE("++show x++","++show y++") ~> "++show res) res
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
  extractArgAnnotation (ValBool _) = TpBool
  extractArgAnnotation (ValInt _) = TpInt
  extractArgAnnotation (ValPtr conds tp) = TpPtr (fmap (const ()) conds) tp
  extractArgAnnotation (ValThreadId conds) = TpThreadId (fmap (const ()) conds)
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
  getTypes _ TpBool = [ProxyArg (undefined::Bool) ()]
  getTypes _ TpInt = [ProxyArg (undefined::Integer) ()]
  getTypes _ (TpPtr trgs tp) = getTypes (undefined::Map MemoryPtr (SMTExpr Bool)) trgs
  getTypes _ (TpThreadId ths) = getTypes (undefined::Map (Ptr CallInst) (SMTExpr Bool)) ths
  fromArgs (ValBool e) = [UntypedExpr e]
  fromArgs (ValInt e) = [UntypedExpr e]
  fromArgs (ValPtr conds _) = fromArgs conds
  fromArgs (ValThreadId conds) = fromArgs conds

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
  extractArgAnnotation (ArrBool _) = TpBool
  extractArgAnnotation (ArrInt _) = TpInt
  extractArgAnnotation (ArrPtr mp tp) = TpPtr (fmap (const ()) mp) tp
  extractArgAnnotation (ArrThreadId mp) = TpThreadId (fmap (const ()) mp)
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
  getTypes _ TpBool = [ProxyArg (undefined::SMTArray (SMTExpr Integer) Bool) ((),())]
  getTypes _ TpInt = [ProxyArg (undefined::SMTArray (SMTExpr Integer) Integer) ((),())]
  getTypes _ (TpPtr trgs tp)
    = getTypes (undefined::Map MemoryPtr (SMTExpr (SMTArray (SMTExpr Integer) Bool)))
      (fmap (const ((),())) trgs)
  getTypes _ (TpThreadId trgs)
    = getTypes (undefined::Map (Ptr CallInst) (SMTExpr (SMTArray (SMTExpr Integer) Bool)))
      (fmap (const ((),())) trgs)
  fromArgs (ArrBool arr) = [UntypedExpr arr]
  fromArgs (ArrInt arr) = [UntypedExpr arr]
  fromArgs (ArrPtr arrs _) = fromArgs arrs
  fromArgs (ArrThreadId arrs) = fromArgs arrs
  
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

showValue :: ValueC v => Ptr v -> ShowS
showValue v = unsafePerformIO $ do
  n <- getNameString v
  return $ showString n

instance Show MemoryPtr where
  showsPrec _ ptr = showMemoryLoc (memoryLoc ptr) .
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
