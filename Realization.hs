{-# LANGUAGE TypeFamilies,MultiParamTypeClasses,FlexibleContexts #-}
module Realization where

import PartialArgs

import Language.SMTLib2
import Control.Monad.State (MonadIO)

class (Args (State t),Args (Input t),PartialArgs (State t),PartialArgs (Input t))
      => TransitionRelation t where
  type State t
  type Input t
  type RevState t
  type PredicateExtractor t
  type RealizationProgress t
  createStateVars :: (Functor m,MonadIO m) => String -> t -> SMT' m (State t)
  createInputVars :: (Functor m,MonadIO m) => String -> t -> SMT' m (Input t)
  initialState :: t -> State t -> SMTExpr Bool
  stateInvariant :: t -> State t -> SMTExpr Bool
  declareNextState :: (Functor m,MonadIO m) => t -> State t -> Input t -> Maybe InterpolationGroup
                      -> RealizationProgress t
                      -> SMT' m (State t,RealizationProgress t)
  declareAssertions :: (Functor m,MonadIO m) => t -> State t -> Input t -> RealizationProgress t
                       -> SMT' m ([SMTExpr Bool],RealizationProgress t)
  declareAssumptions :: (Functor m,MonadIO m) => t -> State t -> Input t -> RealizationProgress t
                        -> SMT' m ([SMTExpr Bool],RealizationProgress t)
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
  startingProgress :: t -> RealizationProgress t
