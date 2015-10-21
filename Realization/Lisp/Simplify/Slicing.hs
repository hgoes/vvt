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

data DepState = DepState { dependencies :: Set (T.Text,LispVarCat)
                         , todo :: [(T.Text,LispVarCat)] }

slice :: LispProgram -> LispProgram
slice prog = prog { programState = Map.intersection (programState prog) keepState
                  , programInput = Map.intersection (programInput prog) keepInput
                  , programGates = Map.intersection (programGates prog) keepGates
                  , programNext  = Map.intersection (programNext prog) keepState
                  , programInit  = Map.intersection (programInit prog) keepState
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
