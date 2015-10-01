{-# LANGUAGE TypeFamilies,MultiParamTypeClasses,FlexibleContexts,ScopedTypeVariables #-}
module Realization where

import PartialArgs

import Language.SMTLib2.LowLevel
import Control.Monad.State (MonadIO)
import Data.Proxy

class (PartialComp (State t),PartialComp (Input t))
      => TransitionRelation t where
  type State t :: (Type -> *) -> *
  type Input t :: (Type -> *) -> *
  type RevState t
  type PredicateExtractor t
  type RealizationProgress t :: (Type -> *) -> *
  createState :: Monad m
              => (forall t. GetType t => Maybe String -> m (e t))
              -> t
              -> String
              -> m (State t e)
  createInput :: Monad m
              => (forall t. GetType t => Maybe String -> m (e t))
              -> t
              -> String
              -> m (Input t e)
  initialState :: Backend b => t -> State t (Expr b) -> SMT b (Expr b BoolType)
  {-initialState :: Monad m
               => (forall t. GetType t
                   => Expression v qv fun con field fv e t
                   -> m (e t))
               -> t
               -> State t e
               -> m (e BoolType)-}
  stateInvariant :: Backend b => t -> Input t (Expr b) -> State t (Expr b) -> SMT b (Expr b BoolType)
  declareNextState :: Backend b => t -> State t (Expr b) -> Input t (Expr b)
                   -> RealizationProgress t (Expr b)
                   -> SMT b (State t (Expr b),RealizationProgress t (Expr b))
  declareAssertions :: Backend b => t -> State t (Expr b) -> Input t (Expr b)
                    -> RealizationProgress t (Expr b)
                    -> SMT b ([Expr b BoolType],RealizationProgress t (Expr b))
  declareAssumptions :: Backend b => t -> State t (Expr b) -> Input t (Expr b)
                     -> RealizationProgress t (Expr b)
                     -> SMT b ([Expr b BoolType],RealizationProgress t (Expr b))
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
  startingProgress :: Backend b => t -> SMT b (RealizationProgress t (Expr b))

{-renderState :: (TransitionRelation t,MonadIO m) => t -> Unpacked (State t) -> m String
renderState (mdl::t) st = renderPartialState mdl
                          (unmaskValue (Proxy::Proxy (State t)) st)

renderInput :: (TransitionRelation t,MonadIO m) => t -> Unpacked (Input t) -> m String
renderInput (mdl::t) st = renderPartialInput mdl
                          (unmaskValue (Proxy::Proxy (Input t)) st)
-}
