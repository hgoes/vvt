{-# LANGUAGE TypeFamilies,ScopedTypeVariables #-}
module PartialArgs where

import Args

import Language.SMTLib2.LowLevel
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import qualified Language.SMTLib2.Internals.Backend as B

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import Data.Typeable
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

type Lifting m e con = (forall v qv fun field fv t. GetType t
                         => Expression v qv fun con field fv e t -> m (e t))

defLifting :: (Backend b,Monad m) => (forall a. SMT b a -> m a)
           -> Lifting m (B.Expr b) (B.Constr b)
defLifting lift e = do
  e' <- mapExpr err err err return err err return e
  lift $ updateBackend $ \b -> B.toBackend b e'
  where
    err = error "PartialArgs.defLifting: Can't be used on expression with variables/functions/etc."

class Composite a => LiftComp a where
  type Unpacked a :: (([Type],*) -> *) -> *
  liftComp :: Monad m => Lifting m e con
           -> Unpacked a con
           -> m (a e)
  unliftComp :: Monad m => (forall t. GetType t => e t -> m (Value con t))
             -> Lifting m e con
             -> a e
             -> m (Unpacked a con)

newtype UArgs' tps con = UArgs' (Args (Value con) tps)

instance GetTypes tps => LiftComp (Args' tps) where
  type Unpacked (Args' tps) = UArgs' tps
  liftComp f (UArgs' NoArg) = return (Args' NoArg)
  liftComp f (UArgs' (Arg x xs)) = do
    x' <- f (Const x)
    Args' xs' <- liftComp f (UArgs' xs)
    return (Args' (Arg x' xs'))
  unliftComp f _ (Args' NoArg) = return (UArgs' NoArg)
  unliftComp f g (Args' (Arg x xs)) = do
    x' <- f x
    UArgs' xs' <- unliftComp f g (Args' xs)
    return $ UArgs' (Arg x' xs')

class LiftComp a => PartialComp a where
  type Partial a :: (([Type],*) -> *) -> *
  maskValue :: Proxy a -> Partial a con -> [Bool] -> (Partial a con,[Bool])
  unmaskValue :: Proxy a -> Unpacked a con -> Partial a con
  assignPartial :: Monad m => (forall t. GetType t => e t -> Value con t -> m p)
                -> Lifting m e con
                -> a e -> Partial a con -> m [Maybe p]

data PValue con t = NoPValue
                  | PValue (Value con t)

newtype PArgs' tps con = PArgs' (Args (PValue con) tps)

instance GetTypes tps => PartialComp (Args' tps) where
  type Partial (Args' tps) = PArgs' tps
  maskValue _ = mask'
    where
      mask' :: PArgs' tps' con -> [Bool] -> (PArgs' tps' con,[Bool])
      mask' (PArgs' NoArg) xs = (PArgs' NoArg,xs)
      mask' (PArgs' (Arg v vs)) (x:xs)
        = let (PArgs' vs',xs') = mask' (PArgs' vs) xs
          in (PArgs' (Arg (if x then v else NoPValue) vs'),xs')
