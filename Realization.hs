{-# LANGUAGE TypeFamilies,MultiParamTypeClasses,FlexibleContexts,ScopedTypeVariables #-}
module Realization where

import Args
import PartialArgs

import Language.SMTLib2
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Monad (embedSMT)
import qualified Language.SMTLib2.Internals.Backend as B

import Control.Monad.State (MonadIO)
import Data.Proxy
import Data.Typeable
import Data.Dependent.Map (DMap)

class (PartialComp (State t),PartialComp (Input t))
      => TransitionRelation t where
  type State t :: (Type -> *) -> *
  type Input t :: (Type -> *) -> *
  type PredicateExtractor t
  type RealizationProgress t :: (Type -> *) -> *
  stateAnnotation :: t -> CompDescr (State t)
  inputAnnotation :: t -> CompDescr (Input t)
  initialState :: (Embed m e,GetType e,Typeable (EmConstr m e))
               => t
               -> State t e
               -> m (e BoolType)
  stateInvariant :: (Embed m e,GetType e,Typeable (EmConstr m e))
                 => t -> State t e -> Input t e
                 -> m (e BoolType)
  declareNextState :: (Embed m e,GetType e,Typeable (EmConstr m e))
                   => (forall t. Maybe String -> e t -> m (e t))
                   -> t
                   -> State t e -> Input t e
                   -> RealizationProgress t e
                   -> m (State t e,RealizationProgress t e)
  declareAssumptions :: (Embed m e,GetType e,Typeable (EmConstr m e))
                     => (forall t. Maybe String -> e t -> m (e t))
                     -> t
                     -> State t e -> Input t e
                     -> RealizationProgress t e
                     -> m ([e BoolType],RealizationProgress t e)
  declareAssertions :: (Embed m e,GetType e,Typeable (EmConstr m e))
                    => (forall t. Maybe String -> e t -> m (e t))
                    -> t
                    -> State t e -> Input t e
                    -> RealizationProgress t e
                    -> m ([e BoolType],RealizationProgress t e)
  isEndState :: (Embed m e,GetType e)
             => t -> State t e -> m (e BoolType)
  {-createRevState :: Backend b => String -> t -> SMT b (State t (Expr b),RevState t)
  relativizeExpr :: (GetType a,Backend b) => t -> RevState t -> Expr b a -> (State t (Expr b) -> SMT b (Expr b a))-}
  --renderPartialState :: t -> Partial (State t) -> String
  --renderPartialInput :: t -> Partial (Input t) -> String
  -- | Returns a list of suggested predicates and a boolean indicating whether they are guaranteed to be unique
  suggestedPredicates :: t -> [(Bool,CompositeExpr (State t) BoolType)]
  suggestedPredicates _ = []
  defaultPredicateExtractor :: MonadIO m => t -> m (PredicateExtractor t)
  extractPredicates :: (MonadIO m) => t -> PredicateExtractor t
                    -> Unpacked (State t)
                    -> Partial (State t)
                    -> m (PredicateExtractor t,
                          [CompositeExpr (State t) BoolType])
  startingProgress :: t -> RealizationProgress t e

renderState :: (TransitionRelation t) => t -> Unpacked (State t) -> String
renderState (mdl::t) st = show (unmaskValue (Proxy::Proxy (State t)) st)

renderPartialState :: (TransitionRelation t) => t -> Partial (State t) -> String
renderPartialState (mdl::t) st = show st

renderInput :: (TransitionRelation t) => t -> Unpacked (Input t) -> String
renderInput (mdl::t) st = show (unmaskValue (Proxy::Proxy (Input t)) st)

renderPartialInput :: (TransitionRelation t) => t -> Partial (Input t) -> String
renderPartialInput (mdl::t) st = show st

createStateVars :: (TransitionRelation tr,Embed m e,GetType e)
                => (forall t. Repr t -> RevComp (State tr) t -> m (e t))
                -> tr
                -> m (State tr e)
createStateVars f tr
  = createComposite f (stateAnnotation tr)

createInputVars :: (TransitionRelation tr,Embed m e,GetType e)
                => (forall t. Repr t -> RevComp (Input tr) t -> m (e t))
                -> tr
                -> m (Input tr e)
createInputVars f tr
  = createComposite f (inputAnnotation tr)

createRevState :: (TransitionRelation tr,Backend b)
               => tr
               -> SMT b (State tr (Expr b),
                         DMap (B.Var b) (RevComp (State tr)))
createRevState (tr::tr)
  = createRevComp (\tp rev -> embedSMT (B.declareVar tp
                                        (Just $ revName (Proxy::Proxy (State tr)) rev))
                  ) (stateAnnotation tr)

createState :: (Backend b,TransitionRelation tr)
            => tr
            -> SMT b (State tr (Expr b))
createState (tr::tr)
  = createComposite
    (\tp rev -> declareVarNamed tp (revName (Proxy::Proxy (State tr)) rev))
    (stateAnnotation tr)

createInput :: (Backend b,TransitionRelation tr)
            => tr
            -> SMT b (Input tr (Expr b))
createInput (tr::tr)
  = createComposite
    (\tp rev -> declareVarNamed tp (revName (Proxy::Proxy (Input tr)) rev))
    (inputAnnotation tr)

createNextState :: (Backend b,TransitionRelation tr)
                => tr
                -> State tr (Expr b) -> Input tr (Expr b)
                -> RealizationProgress tr (Expr b)
                -> SMT b (State tr (Expr b),RealizationProgress tr (Expr b))
createNextState
  = declareNextState (\name -> case name of
                       Nothing -> defineVar
                       Just name' -> defineVarNamed name'
                     )
