module Realization.Lisp.Simplify.Slicing where

import Realization.Lisp
import Realization.Lisp.Value

import Language.SMTLib2.Internals

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Typeable
import Data.Foldable (foldl)
import Prelude hiding (foldl)

data DepState = DepState { dependencies :: Set (T.Text,LispVarCat)
                         , todo :: [(T.Text,LispVarCat)] }

slice :: LispProgram -> LispProgram
slice prog = prog { programState = Map.intersection (programState prog) keepState
                  , programInput = Map.intersection (programInput prog) keepInput
                  , programGates = Map.intersection (programGates prog) keepGates
                  , programNext  = Map.intersection (programNext prog) keepState
                  , programInit  = Map.intersection (programInit prog) keepState
                  , programInvariant = fmap filterExpr (programInvariant prog)
                  }
  where
    keepInput = Map.fromList [ (name,()) | (name,Input) <- Set.toList deps ]
    keepState = Map.fromList [ (name,()) | (name,State) <- Set.toList deps ]
    keepGates = Map.fromList [ (name,()) | (name,Gate) <- Set.toList deps ]
    dep0 = DepState { dependencies = Set.empty
                    , todo = []
                    }
    dep1 = foldl (\st e -> getDependenciesExpr e st
                 ) dep0 (programProperty prog)
    deps = recDependencies prog dep1
    filterExpr :: SMTExpr t -> SMTExpr t
    filterExpr (InternalObj (cast -> Just acc) ann) = case acc of
      LispVarAccess var idx dyn -> case filterVar var of
        Nothing -> defaultExpr ann
        Just var' -> InternalObj (LispVarAccess var' idx (fmap filterExpr dyn)) ann
      LispSizeAccess var dyn -> case filterVar var of
        Nothing -> defaultExpr ann
        Just var' -> InternalObj (LispSizeAccess var' (fmap filterExpr dyn)) ann
      LispSizeArrAccess var i -> case filterVar var of
        Nothing -> defaultExpr ann
        Just var' -> InternalObj (LispSizeArrAccess var' i) ann
      LispEq v1 v2 -> case filterVar v1 of
        Nothing -> defaultExpr ann
        Just v1' -> case filterVar v2 of
          Nothing -> defaultExpr ann
          Just v2' -> InternalObj (LispEq v1' v2') ann
    filterExpr (App fun args)
      = App fun (snd $ foldExprsId (\_ e _ -> ((),filterExpr e)) () args
                       (extractArgAnnotation args))
    filterExpr e = e
    filterVar v@(NamedVar name cat tp) = case cat of
      Input -> if Map.member name keepInput
               then Just v
               else Nothing
      State -> if Map.member name keepState
               then Just v
               else Nothing
      Gate -> if Map.member name keepGates
              then Just v
              else Nothing
    filterVar (LispStore v idx sidx val) = do
      v' <- filterVar v
      let sidx' = fmap filterExpr sidx
          val' = filterExpr val
      return (LispStore v' idx sidx' val')
    filterVar (LispConstr val) = Just $ LispConstr $ LispValue { size = nsize
                                                               , value = nvalue }
      where
        nsize = case size val of
          Size elem -> Size (fmap (\(SizeElement e) -> SizeElement $ filterExpr e) elem)
        nvalue = fmap (\(Val v) -> Val (filterExpr v)) (value val)
    filterVar (LispITE c ifT ifF) = do
      ifT' <- filterVar ifT
      ifF' <- filterVar ifF
      return (LispITE (filterExpr c) ifT' ifF')

recDependencies :: LispProgram -> DepState -> Set (T.Text,LispVarCat)
recDependencies prog dep = case todo dep of
  [] -> dependencies dep
  ((name,cat):todo') -> case cat of
    Gate -> case Map.lookup name (programGates prog) of
      Just (_,var) -> recDependencies prog $ getDependencies var (dep { todo = todo' })
    State -> case Map.lookup name (programNext prog) of
      Just var -> recDependencies prog $ getDependencies var (dep { todo = todo' })
    Input -> recDependencies prog $ dep { todo = todo' }

getDependencies :: LispVar -> DepState -> DepState
getDependencies (NamedVar name cat _) st
  = if Set.member (name,cat) (dependencies st)
    then st
    else DepState { dependencies = Set.insert (name,cat) $ dependencies st
                  , todo = (name,cat):todo st }
getDependencies (LispStore var _ idx val) st0 = st3
  where
    st1 = getDependencies var st0
    st2 = foldl (\st i -> getDependenciesExpr i st) st1 idx
    st3 = getDependenciesExpr val st2
getDependencies (LispConstr val) st
  = foldl (\st (Val v) -> getDependenciesExpr v st
          ) st (value val)
getDependencies (LispITE c v1 v2) st0 = st3
  where
    st1 = getDependenciesExpr c st0
    st2 = getDependencies v1 st1
    st3 = getDependencies v2 st2

getDependenciesExpr :: SMTExpr a -> DepState -> DepState
getDependenciesExpr (InternalObj (cast -> Just acc) _) st
  = getDependenciesAccess acc st
getDependenciesExpr (App fun args) st
  = fst $ foldExprsId (\st e _ -> (getDependenciesExpr e st,e)) st args
    (extractArgAnnotation args)
getDependenciesExpr _ st = st

getDependenciesAccess :: LispVarAccess -> DepState -> DepState
getDependenciesAccess (LispVarAccess var _ idx) st0 = st2
  where
    st1 = getDependencies var st0
    st2 = foldl (\st e -> getDependenciesExpr e st) st1 idx
getDependenciesAccess (LispSizeAccess var idx) st0 = st2
  where
    st1 = getDependencies var st0
    st2 = foldl (\st e -> getDependenciesExpr e st) st1 idx
getDependenciesAccess (LispSizeArrAccess var _) st
  = getDependencies var st
getDependenciesAccess (LispEq v1 v2) st = st2
  where
    st1 = getDependencies v1 st
    st2 = getDependencies v2 st1
