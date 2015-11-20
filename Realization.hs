{-# LANGUAGE TypeFamilies,MultiParamTypeClasses,FlexibleContexts,ScopedTypeVariables #-}
module Realization where

import Args
import PartialArgs

import Language.SMTLib2
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Embed

import Control.Monad.State (MonadIO)
import Data.Proxy
import Data.Typeable

class (PartialComp (State t),PartialComp (Input t))
      => TransitionRelation t where
  type State t :: (Type -> *) -> *
  type Input t :: (Type -> *) -> *
  type PredicateExtractor t
  type RealizationProgress t :: (Type -> *) -> *
  stateAnnotation :: t -> CompDescr (State t)
  inputAnnotation :: t -> CompDescr (Input t)
  initialState :: (Embed m e,Typeable (EmConstr m e))
               => t
               -> State t e
               -> m (e BoolType)
  stateInvariant :: (Embed m e,Typeable (EmConstr m e))
                 => t -> State t e -> Input t e
                 -> m (e BoolType)
  declareNextState :: (Embed m e,Typeable (EmConstr m e))
                   => (forall t. GetType t
                       => Maybe String -> e t -> m (e t))
                   -> t
                   -> State t e -> Input t e
                   -> RealizationProgress t e
                   -> m (State t e,RealizationProgress t e)
  declareAssumptions :: (Embed m e,Typeable (EmConstr m e))
                     => (forall t. GetType t
                         => Maybe String -> e t -> m (e t))
                     -> t
                     -> State t e -> Input t e
                     -> RealizationProgress t e
                     -> m ([e BoolType],RealizationProgress t e)
  declareAssertions :: (Embed m e,Typeable (EmConstr m e))
                    => (forall t. GetType t
                        => Maybe String -> e t -> m (e t))
                    -> t
                    -> State t e -> Input t e
                    -> RealizationProgress t e
                    -> m ([e BoolType],RealizationProgress t e)
  {-createRevState :: Backend b => String -> t -> SMT b (State t (Expr b),RevState t)
  relativizeExpr :: (GetType a,Backend b) => t -> RevState t -> Expr b a -> (State t (Expr b) -> SMT b (Expr b a))
  renderPartialState :: Backend b => t -> Partial (State t) (Constr b) -> SMT b String
  renderPartialInput :: Backend b => t -> Partial (Input t) (Constr b) -> SMT b String
  -- | Returns a list of suggested predicates and a boolean indicating whether they are guaranteed to be unique
  suggestedPredicates :: Embed e => t -> [(Bool,State t e -> e BoolType)]
  suggestedPredicates _ = []
  defaultPredicateExtractor :: MonadIO m => t -> m (PredicateExtractor t)
  extractPredicates :: (MonadIO m,Embed e) => t -> PredicateExtractor t
                       -> Unpacked (State t e)
                       -> PartialValue (State t e)
                       -> m (PredicateExtractor t,
                             [State t e -> e BoolType])-}
  startingProgress :: t -> RealizationProgress t e

{-renderState :: (TransitionRelation t,MonadIO m) => t -> Unpacked (State t) -> m String
renderState (mdl::t) st = renderPartialState mdl
                          (unmaskValue (Proxy::Proxy (State t)) st)

renderInput :: (TransitionRelation t,MonadIO m) => t -> Unpacked (Input t) -> m String
renderInput (mdl::t) st = renderPartialInput mdl
                          (unmaskValue (Proxy::Proxy (Input t)) st)
-}
