{-# LANGUAGE TypeFamilies,ScopedTypeVariables #-}
module PartialArgs where

import Args

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed

import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show

class (Composite a,Ord (Unpacked a),Show (Unpacked a)) => LiftComp a where
  type Unpacked a
  liftComp :: (Embed m e,GetType e)
           => Unpacked a
           -> m (a e)
  unliftComp :: (Embed m e,GetType e) => (forall t. e t -> m (ConcreteValue t))
             -> a e
             -> m (Unpacked a)

class (LiftComp a,Ord (Partial a),Show (Partial a)) => PartialComp a where
  type Partial a
  maskValue :: Proxy a -> Partial a -> [Bool] -> (Partial a,[Bool])
  unmaskValue :: Proxy a -> Unpacked a -> Partial a
  assignPartial :: (Embed m e,GetType e) => (forall t. e t -> ConcreteValue t -> m p)
                -> a e -> Partial a -> m [Maybe p]

data PValue t where
  NoPValue :: Repr t -> PValue t
  PValue :: ConcreteValue t -> PValue t

instance GEq PValue where
  geq (NoPValue tp1) (NoPValue tp2) = case geq tp1 tp2 of
    Just Refl -> Just Refl
    Nothing -> Nothing
  geq (NoPValue _) _ = Nothing
  geq _ (NoPValue _) = Nothing
  geq (PValue v1) (PValue v2) = case geq v1 v2 of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare PValue where
  gcompare (NoPValue tp1) (NoPValue tp2) = case gcompare tp1 tp2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (NoPValue _) _ = GLT
  gcompare _ (NoPValue _) = GGT
  gcompare (PValue v1) (PValue v2) = case gcompare v1 v2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance Show (PValue t) where
  showsPrec p (NoPValue _) = showChar '*'
  showsPrec p (PValue c) = gshowsPrec p c

instance GShow PValue where
  gshowsPrec = showsPrec

assignEq :: (Embed m e,GetType e) => e t -> ConcreteValue t -> m (e BoolType)
assignEq var c = do
  val <- embedConst c
  embed $ Eq (var ::: val ::: Nil)
