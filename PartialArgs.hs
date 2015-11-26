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

class Composite a => LiftComp a where
  type Unpacked a
  liftComp :: Embed m e
           => Unpacked a
           -> m (a e)
  unliftComp :: Embed m e => (forall t. GetType t => e t -> m (ConcreteValue t))
             -> a e
             -> m (Unpacked a)

class LiftComp a => PartialComp a where
  type Partial a
  maskValue :: Proxy a -> Partial a -> [Bool] -> (Partial a,[Bool])
  unmaskValue :: Proxy a -> Unpacked a -> Partial a
  assignPartial :: Embed m e => (forall t. GetType t => e t -> ConcreteValue t -> m p)
                -> a e -> Partial a -> m [Maybe p]

data PValue t = NoPValue
              | PValue (ConcreteValue t)

assignEq :: (Embed m e,GetType t) => e t -> ConcreteValue t -> m (e BoolType)
assignEq var c = do
  val <- embedConst c
  [expr| (= var val) |]
