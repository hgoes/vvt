{-# LANGUAGE TypeFamilies,MultiParamTypeClasses,FlexibleContexts #-}
module Realization where

import Gates
import PartialArgs

import LLVM.FFI
import Foreign.Ptr
import Language.SMTLib2
import Control.Monad.State (MonadIO)

class (Args (State t),Args (Input t),PartialArgs (State t),PartialArgs (Input t))
      => TransitionRelation t where
  type State t
  type Input t
  type RevState t
  createStateVars :: (Functor m,MonadIO m) => String -> t -> SMT' m (State t)
  createInputVars :: (Functor m,MonadIO m) => String -> t -> SMT' m (Input t)
  initialState :: t -> State t -> SMTExpr Bool
  stateInvariant :: t -> State t -> SMTExpr Bool
  declareNextState :: (Functor m,MonadIO m) => t -> State t -> Input t -> RealizedGates
                      -> SMT' m (State t,RealizedGates)
  declareAssertions :: (Functor m,MonadIO m) => t -> State t -> Input t -> RealizedGates
                       -> SMT' m ([SMTExpr Bool],RealizedGates)
  declareAssumptions :: (Functor m,MonadIO m) => t -> State t -> Input t -> RealizedGates
                        -> SMT' m ([SMTExpr Bool],RealizedGates)
  createRevState :: (Functor m,MonadIO m) => String -> t -> SMT' m (State t,RevState t)
  relativizeExpr :: SMTType a => t -> RevState t -> SMTExpr a -> (State t -> SMTExpr a)
  annotationState :: t -> ArgAnnotation (State t)
  annotationInput :: t -> ArgAnnotation (Input t)
  renderPartialState :: MonadIO m => t -> PartialValue (State t) -> m String
  suggestedPredicates :: t -> [State t -> SMTExpr Bool]
  suggestedPredicates _ = []
