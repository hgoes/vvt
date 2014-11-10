{-# LANGUAGE TypeFamilies,MultiParamTypeClasses,FlexibleContexts #-}
module Realization where

import Gates
import PartialArgs

import Language.SMTLib2
import Control.Monad.State (MonadIO)

class (Args (State t),Args (Input t),PartialArgs (State t),PartialArgs (Input t))
      => TransitionRelation t where
  type State t
  type Input t
  type RevState t
  type PredicateExtractor t
  createStateVars :: (Functor m,MonadIO m) => String -> t -> SMT' m (State t)
  createInputVars :: (Functor m,MonadIO m) => String -> t -> SMT' m (Input t)
  initialState :: t -> State t -> SMTExpr Bool
  stateInvariant :: t -> State t -> SMTExpr Bool
  declareNextState :: (Functor m,MonadIO m) => t -> State t -> Input t -> Maybe InterpolationGroup
                      -> RealizedGates
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
  -- | Returns a list of suggested predicates and a boolean indicating whether they are guaranteed to be unique
  suggestedPredicates :: t -> [(Bool,State t -> SMTExpr Bool)]
  suggestedPredicates _ = []
  defaultPredicateExtractor :: MonadIO m => t -> m (PredicateExtractor t)
  extractPredicates :: MonadIO m => t -> PredicateExtractor t
                       -> Unpacked (State t)
                       -> PartialValue (State t)
                       -> m (PredicateExtractor t,
                             [State t -> SMTExpr Bool])
