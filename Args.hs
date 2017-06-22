module Args where

import Language.SMTLib2
import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Embed
import qualified Language.SMTLib2.Internals.Expression as E
import Language.SMTLib2.Internals.Interface
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Backend

import Data.GADT.Compare
import Data.GADT.Show
import Data.Proxy
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Functor.Identity
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader

class (Ord (CompDescr arg),GCompare (RevComp arg),GShow (RevComp arg))
      => Composite (arg :: (Type -> *) -> *) where
  type CompDescr arg
  type RevComp arg :: Type -> *
  compositeType :: CompDescr arg -> arg Repr
  foldExprs :: (Monad m,GetType e)
            => (forall t. RevComp arg t -> e t -> m (e' t))
            -> arg e
            -> m (arg e')
  accessComposite :: GetType e => RevComp arg t -> arg e -> e t
  createComposite :: (Monad m)
                  => (forall t. Repr t -> RevComp arg t -> m (e t))
                  -> CompDescr arg
                  -> m (arg e)
  createComposite f descr
    = foldExprs (\rev tp -> f tp rev)
      (compositeType descr)
  eqComposite :: (Embed m e,Monad m,GetType e) => arg e -> arg e -> m (e BoolType)
  eqComposite e1 e2 = do
    eqs <- execWriterT $ foldExprs
           (\rev x -> do
               let y = accessComposite rev e2
               c <- lift $ x .==. y
               tell [c]
               return x) e1
    case eqs of
      [] -> true
      [x] -> return x
      _ -> and' eqs
  revName :: Proxy arg -> RevComp arg tp -> String
  revName _ _ = "rev"
  revType :: Proxy arg -> CompDescr arg -> RevComp arg tp -> Repr tp
  revType (_::Proxy arg) descr rev = accessComposite rev (compositeType descr :: arg Repr)

data CompositeExpr a t
  = CompositeExpr { compositeDescr :: CompDescr a
                  , compositeExpr :: E.Expression (RevComp a) E.NoVar E.NoFun E.NoVar E.NoVar (CompositeExpr a) t }

instance Composite a => GetType (CompositeExpr a) where
  getType (CompositeExpr descr e :: CompositeExpr a t)
    = runIdentity $ E.expressionType
      (return . revType (Proxy::Proxy a) descr)
      (return.getType) (return.getFunType) (return.getType)
      (return.getType) (return.getType) e

declareComposite :: forall arg m e.
                    (Composite arg,Monad m)
                 => (forall t. Repr t -> String -> m (e t))
                 -> CompDescr arg
                 -> m (arg e)
declareComposite f descr
  = createComposite (\tp rev -> f tp (revName (Proxy::Proxy arg) rev)) descr

createRevComp :: (Composite arg,Embed m e,Monad m,GetType e)
              => (forall t. Repr t -> RevComp arg t -> m (EmVar m e t))
              -> CompDescr arg
              -> m (arg e,DMap (EmVar m e) (RevComp arg))
createRevComp f descr
  = runStateT (createComposite (\tp rev -> do
                                   v <- lift (f tp rev)
                                   e <- lift (embed (pure $ Var v))
                                   modify (DMap.insert v rev)
                                   return e
                               ) descr
              ) DMap.empty

instance Composite a => GEq (CompositeExpr a) where
  geq (CompositeExpr dx x) (CompositeExpr dy y)
    = if dx==dy
      then geq x y
      else Nothing
instance Composite a => GCompare (CompositeExpr a) where
  gcompare (CompositeExpr dx x) (CompositeExpr dy y)
    = case compare dx dy of
    EQ -> gcompare x y
    LT -> GLT
    GT -> GGT
instance Composite a => Eq (CompositeExpr a t) where
  (==) = defaultEq
instance Composite a => Ord (CompositeExpr a t) where
  compare = defaultCompare

instance Composite a => Show (CompositeExpr a t) where
  showsPrec p (CompositeExpr _ e) = E.renderExprDefault E.SMTRendering e

instance Composite a => GShow (CompositeExpr a) where
  gshowsPrec = showsPrec

instance (Composite a,d ~ CompDescr a) => Embed (Reader d) (CompositeExpr a) where
  type EmVar (Reader d) (CompositeExpr a) = RevComp a
  type EmQVar (Reader d) (CompositeExpr a) = E.NoVar
  type EmFun (Reader d) (CompositeExpr a) = E.NoFun
  type EmFunArg (Reader d) (CompositeExpr a) = E.NoVar
  type EmLVar (Reader d) (CompositeExpr a) = E.NoVar
  embed e = do
    descr <- ask
    re <- e
    return (CompositeExpr descr re)
  embedQuantifier _ _ _ = error "CompositeExpr does not support quantifier"
  embedTypeOf = return getType

instance Composite a => Extract () (CompositeExpr a) where
  type ExVar () (CompositeExpr a) = RevComp a
  type ExQVar () (CompositeExpr a) = E.NoVar
  type ExFun () (CompositeExpr a) = E.NoFun
  type ExFunArg () (CompositeExpr a) = E.NoVar
  type ExLVar () (CompositeExpr a) = E.NoVar
  extract _ (CompositeExpr _ x) = Just x

mkCompExpr :: Composite arg
           => (arg (CompositeExpr arg) -> Reader (CompDescr arg) (CompositeExpr arg tp))
           -> CompDescr arg
           -> CompositeExpr arg tp
mkCompExpr f descr
  = runReader (do
                  arg <- createComposite (\_ rev -> return (CompositeExpr descr (Var rev))) descr
                  f arg) descr

concretizeExpr :: (Embed m e,Monad m,GetType e,Composite arg)
               => arg e
               -> CompositeExpr arg tp
               -> m (e tp)
concretizeExpr arg (CompositeExpr _ (E.Var rev))
  = return (accessComposite rev arg)
concretizeExpr arg (CompositeExpr _ (E.App fun args)) = do
  nfun <- E.mapFunction undefined fun
  nargs <- List.mapM (concretizeExpr arg) args
  embed (pure $ E.App nfun nargs)
concretizeExpr arg (CompositeExpr _ (E.Const c)) = constant c
concretizeExpr arg (CompositeExpr _ (E.AsArray fun)) = do
  nfun <- E.mapFunction undefined fun
  embed (pure $ E.AsArray nfun)

relativizeExpr :: (Backend b,Composite arg)
               => CompDescr arg
               -> DMap (Var b) (RevComp arg)
               -> Expr b tp
               -> SMT b (CompositeExpr arg tp)
relativizeExpr descr mp expr = do
  st <- get
  return $ relativizeExpr' descr mp DMap.empty (BackendInfo (backend st)) expr

relativizeExpr' :: (Extract i e,Composite arg,GShow (ExVar i e))
                => CompDescr arg
                -> DMap (ExVar i e) (RevComp arg)
                -> DMap (ExLVar i e) (CompositeExpr arg)
                -> i
                -> e tp
                -> CompositeExpr arg tp
relativizeExpr' descr mp lmp info e = case extract info e of
  Just (E.Var v) -> case DMap.lookup v mp of
    Just rev -> CompositeExpr descr (E.Var rev)
    Nothing -> error $ "Failed to relativize: "++gshowsPrec 0 v ""
  Just (E.LVar v) -> case DMap.lookup v lmp of
    Just e -> e
  Just (E.App fun args)
    -> let nfun = runIdentity $ E.mapFunction undefined fun
           nargs = runIdentity $ List.mapM (return . relativizeExpr' descr mp lmp info) args
       in CompositeExpr descr (E.App nfun nargs)
  Just (E.Const c) -> CompositeExpr descr (E.Const c)
  Just (E.AsArray fun)
    -> let nfun = runIdentity $ E.mapFunction undefined fun
       in CompositeExpr descr (E.AsArray nfun)
  -- TODO: Find a way not to flatten let bindings
  Just (E.Let bind body) -> relativizeExpr' descr mp nlmp info body
    where
      nlmp = foldl (\lmp (E.LetBinding v e)
                     -> DMap.insert v
                        (relativizeExpr' descr mp lmp info e) lmp
                   ) lmp bind

collectRevVars :: Composite arg
               => DMap (RevComp arg) E.NoVar
               -> CompositeExpr arg tp
               -> DMap (RevComp arg) E.NoVar
collectRevVars mp (CompositeExpr _ (E.Var v))
  = DMap.insert v E.NoVar' mp
collectRevVars mp (CompositeExpr _ (E.App fun args))
  = runIdentity $ List.foldM (\mp e -> return $ collectRevVars mp e) mp args
collectRevVars mp (CompositeExpr _ (E.Const _)) = mp
collectRevVars mp (CompositeExpr _ (E.AsArray _)) = mp
