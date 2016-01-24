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
  foldExprs :: (Monad m)
            => (forall t. RevComp arg t -> e t -> m (e' t))
            -> arg e
            -> m (arg e')
  accessComposite :: RevComp arg t -> arg e -> e t
  createComposite :: (Monad m)
                  => (forall t. Repr t -> RevComp arg t -> m (e t))
                  -> CompDescr arg
                  -> m (arg e)
  createComposite f descr
    = foldExprs (\rev tp -> f tp rev)
      (compositeType descr)
  eqComposite :: (Embed m e,GetType e) => arg e -> arg e -> m (e BoolType)
  eqComposite e1 e2 = do
    eqs <- execWriterT $ foldExprs
           (\rev x -> do
               let y = accessComposite rev e2
               c <- lift $ embed $ x :==: y
               tell [c]
               return x) e1
    case eqs of
      [] -> embedConst (BoolValueC True)
      [x] -> return x
      _ -> embed $ AndLst eqs
  revName :: Proxy arg -> RevComp arg tp -> String
  revName _ _ = "rev"
  revType :: Proxy arg -> CompDescr arg -> RevComp arg tp -> Repr tp
  revType (_::Proxy arg) descr rev = accessComposite rev (compositeType descr :: arg Repr)

data CompositeExpr a t
  = CompositeExpr { compositeDescr :: CompDescr a
                  , compositeExpr :: E.Expression (RevComp a) E.NoVar E.NoFun E.NoCon E.NoField E.NoVar E.NoVar (CompositeExpr a) t }

instance Composite a => GetType (CompositeExpr a) where
  getType (CompositeExpr descr e :: CompositeExpr a t)
    = runIdentity $ E.expressionType
      (return . revType (Proxy::Proxy a) descr)
      (return.getType) (return.getFunType) (return.getConType)
      (return.getFieldType) (return.getType) (return.getType) (return.getType) e

createRevComp :: (Composite arg,Embed m e,GetType e)
              => (forall t. Repr t -> RevComp arg t -> m (EmVar m e t))
              -> CompDescr arg
              -> m (arg e,DMap (EmVar m e) (RevComp arg))
createRevComp f descr
  = runStateT (createComposite (\tp rev -> do
                                   v <- lift (f tp rev)
                                   e <- lift (embed (Var v))
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
  type EmConstr (Reader d) (CompositeExpr a) = E.NoCon
  type EmField (Reader d) (CompositeExpr a) = E.NoField
  type EmFunArg (Reader d) (CompositeExpr a) = E.NoVar
  type EmLVar (Reader d) (CompositeExpr a) = E.NoVar
  embed e = do
    descr <- ask
    return (CompositeExpr descr e)
  embedQuantifier _ _ = error "CompositeExpr does not support quantifier"
  embedConstrTest _ _ _ = error "CompositeExpr does not support datatypes"
  embedGetField _ _ _ _ _ = error "CompositeExpr does not support datatypes"
  embedConst c = do
    descr <- ask
    v <- valueFromConcrete (\_ _ -> error "CompositeExpr does not support datatypes") c
    return (CompositeExpr descr (E.Const v))
  embedTypeOf = return.getType

instance Composite a => Extract () (CompositeExpr a) where
  type ExVar () (CompositeExpr a) = RevComp a
  type ExQVar () (CompositeExpr a) = E.NoVar
  type ExFun () (CompositeExpr a) = E.NoFun
  type ExConstr () (CompositeExpr a) = E.NoCon
  type ExField () (CompositeExpr a) = E.NoField
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

concretizeExpr :: (Embed m e,Composite arg)
               => arg e
               -> CompositeExpr arg tp
               -> m (e tp)
concretizeExpr arg (CompositeExpr _ (E.Var rev))
  = return (accessComposite rev arg)
concretizeExpr arg (CompositeExpr _ (E.App fun args)) = do
  nfun <- E.mapFunction undefined undefined undefined fun
  nargs <- List.mapM (concretizeExpr arg) args
  embed (E.App nfun nargs)
concretizeExpr arg (CompositeExpr _ (E.Const c)) = do
  nc <- mapValue undefined c
  embed (E.Const nc)
concretizeExpr arg (CompositeExpr _ (E.AsArray fun)) = do
  nfun <- E.mapFunction undefined undefined undefined fun
  embed (E.AsArray nfun)

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
    -> let nfun = runIdentity $ E.mapFunction undefined undefined undefined fun
           nargs = runIdentity $ List.mapM (return . relativizeExpr' descr mp lmp info) args
       in CompositeExpr descr (E.App nfun nargs)
  Just (E.Const c)
    -> let nc = runIdentity $ mapValue undefined c
       in CompositeExpr descr (E.Const nc)
  Just (E.AsArray fun)
    -> let nfun = runIdentity $ E.mapFunction undefined undefined undefined fun
       in CompositeExpr descr (E.AsArray nfun)
  -- TODO: Find a way not to flatten let bindings
  Just (E.Let bind body) -> relativizeExpr' descr mp nlmp info body
    where
      nlmp = runIdentity $ List.foldM (\lmp bind -> return $ DMap.insert (E.letVar bind)
                                                    (relativizeExpr' descr mp lmp info (E.letExpr bind)) lmp
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
