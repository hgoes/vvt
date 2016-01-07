{-# LANGUAGE RankNTypes,TypeFamilies,MultiParamTypeClasses,FlexibleContexts,
             FlexibleInstances,ScopedTypeVariables,GADTs,DeriveDataTypeable,
             DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
module Realization.Lisp.Value where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances (compareExprs,withSort)
import Data.Unit
import Data.Fix
import PartialArgs

import Data.List (genericIndex,genericLength)
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Data.Constraint
import Prelude hiding (mapM,foldl,and,concat)

import Debug.Trace

data LispStruct a = Singleton a
                  | Struct [LispStruct a]
                  deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

class (SMTType t,SMTValue (ResultType t),Unit (SMTAnnotation t),Unit (SMTAnnotation (ResultType t)))
      => Indexable t i where
  type ResultType t
  canIndex :: t -> Bool
  index :: (forall p. (Indexable p i,ResultType p ~ ResultType t) => SMTExpr p -> (a,SMTExpr p))
        -> SMTExpr t -> i -> (a,SMTExpr t)
  deref :: i -> SMTExpr t -> SMTExpr (ResultType t)
  derefConst :: i -> t -> ResultType t
  reref :: i -> SMTExpr (ResultType t) -> SMTExpr t
  recIndexable :: t -> i -> Dict (Indexable (ResultType t) i,
                                  ResultType (ResultType t) ~ ResultType t)

instance Indexable Integer i where
  type ResultType Integer = Integer
  canIndex _ = False
  index _ _ _ = error "Cannot index integer type."
  deref _ = id
  derefConst _ = id
  reref _ = id
  recIndexable _ _ = Dict

instance Indexable Bool i where
  type ResultType Bool = Bool
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

instance Args Size where
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
  getArgAnnotation _ sorts = (genericLength sorts,[])

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
  = case szEq++valEq of
  [] -> constant True
  [x] -> x
  xs -> app and' xs
  where
    szEq = zipWith (\(SizeElement e1) (SizeElement e2) -> case cast e2 of
                     Just e2' -> e1 .==. e2') sz1 sz2
    valEq = linearizeStruct $ zipStruct (\(Val e1) (Val e2) -> case cast e2 of
                                          Just e2' -> e1 .==. e2'
                                        ) val1 val2

instance Args LispValue where
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
                   arr (constant (i::Integer)) ]

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
