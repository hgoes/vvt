{-# LANGUAGE TypeFamilies,ScopedTypeVariables #-}
module PartialArgs where

import Args

import Language.SMTLib2
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import qualified Language.SMTLib2.Internals.Backend as B

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import Data.Typeable
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare
import Data.GADT.Show

class (Composite a,Ord (Unpacked a),Show (Unpacked a)) => LiftComp a where
  type Unpacked a
  liftComp :: Embed m e
           => Unpacked a
           -> m (a e)
  unliftComp :: Embed m e => (forall t. GetType t => e t -> m (ConcreteValue t))
             -> a e
             -> m (Unpacked a)

class (LiftComp a,Ord (Partial a),Show (Partial a)) => PartialComp a where
  type Partial a
  maskValue :: Proxy a -> Partial a -> [Bool] -> (Partial a,[Bool])
  unmaskValue :: Proxy a -> Unpacked a -> Partial a
  assignPartial :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
                -> a e -> Partial a -> m [Maybe p]

data PValue t where
  NoPValue :: GetType t => PValue t
  PValue :: GetType t => ConcreteValue t -> PValue t

instance GEq PValue where
  geq (NoPValue::PValue a) (NoPValue::PValue b) = case eqT :: Maybe (a :~: b) of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq NoPValue _ = Nothing
  geq _ NoPValue = Nothing
  geq (PValue v1) (PValue v2) = case geq v1 v2 of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare PValue where
  gcompare (NoPValue::PValue a) (NoPValue::PValue b) = case eqT :: Maybe (a :~: b) of
    Just Refl -> GEQ
    Nothing -> case compare (typeRep (Proxy::Proxy a)) (typeRep (Proxy::Proxy b)) of
      LT -> GLT
      GT -> GGT

instance Show (PValue t) where
  showsPrec p NoPValue = showChar '*'
  showsPrec p (PValue c) = gshowsPrec p c

instance GShow PValue where
  gshowsPrec = showsPrec

assignEq :: (Embed m e,GetType t) => e t -> ConcreteValue t -> m (e BoolType)
assignEq var c = do
  val <- embedConst c
  [expr| (= var val) |]
