module Realization.Lisp.Simplify.Slicing where

import Args
import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Array

import Language.SMTLib2
import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import Language.SMTLib2.Internals.Expression

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (foldl)
import Prelude hiding (foldl)
import Data.Functor.Identity
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare
import Control.Monad.State

data AnyName = forall lvl tps. AnyName { anyName :: LispName '(lvl,tps)
                                       , anyCat :: LispVarCat }

data DepState = DepState { dependencies :: Set AnyName
                         , todo :: [AnyName] }


instance Eq AnyName where
  (==) (AnyName n1 s1) (AnyName n2 s2)
    = if s1==s2
      then False
      else defaultEq n1 n2

instance Ord AnyName where
  compare (AnyName n1 s1) (AnyName n2 s2) = case compare s1 s2 of
    EQ -> defaultCompare n1 n2
    r -> r

slice :: LispProgram -> LispProgram
slice prog = prog { programState = filterMap (programState prog) State
                  , programInput = filterMap (programInput prog) Input
                  , programGates = filterMap (programGates prog) Gate
                  , programNext  = filterMap (programNext prog) State
                  , programInit  = filterMap (programInit prog) State
                  , programInvariant = fmap filterExpr (programInvariant prog)
                  }
  where
    filterMap :: DMap LispName a -> LispVarCat -> DMap LispName a
    filterMap mp cat = DMap.fromAscList
                       [ name :=> ann
                       | name@(LispName _ _ _) :=> ann <- DMap.toAscList mp
                       , Set.member (AnyName name cat) deps ]
    dep0 = DepState { dependencies = Set.empty
                    , todo = []
                    }
    dep1 = foldl (\st e -> getDependenciesExpr e st
                 ) dep0 (programProperty prog)
    deps = recDependencies prog dep1
    filterExpr :: LispExpr t -> LispExpr t
    filterExpr (LispExpr (App fun args)) = LispExpr (App fun nargs)
      where
        nargs = runIdentity $ List.mapM (return.filterExpr) args
    filterExpr (LispExpr e) = LispExpr e
    filterExpr e@(LispRef var idx) = case filterVar var of
      Nothing -> defaultExpr (getType e)
      Just nvar -> LispRef nvar idx
    filterExpr (LispEq v1 v2) = case filterVar v1 of
      Nothing -> LispExpr (Const $ BoolValue True)
      Just v1' -> case filterVar v2 of
        Nothing -> LispExpr (Const $ BoolValue True)
        Just v2' -> LispEq v1' v2'
    filterExpr (ExactlyOne xs) = ExactlyOne $ fmap filterExpr xs
    filterExpr (AtMostOne xs) = AtMostOne $ fmap filterExpr xs

    filterVar :: LispVar LispExpr sig -> Maybe (LispVar LispExpr sig)
    filterVar v@(NamedVar name@(LispName _ _ _) cat)
      = if Set.member (AnyName name cat) deps
        then Just v
        else Nothing
    filterVar (LispStore v idx sidx val) = do
      v' <- filterVar v
      let sidx' = filterArrayIndex sidx
          val' = filterExpr val
      return (LispStore v' idx sidx' val')
    filterVar (LispConstr (LispValue sz val))
      = Just $ LispConstr $ LispValue nsize nvalue
      where
        nsize = filterSize sz
        nvalue = runIdentity $ Struct.mapM (\(Sized v) -> return $ Sized (filterExpr v)) val
    filterVar (LispITE c ifT ifF) = do
      ifT' <- filterVar ifT
      ifF' <- filterVar ifF
      return (LispITE (filterExpr c) ifT' ifF')
    filterArrayIndex :: List LispExpr lvl
                     -> List LispExpr lvl
    filterArrayIndex = runIdentity . List.mapM (return.filterExpr)
    filterSize :: Size LispExpr lvl -> Size LispExpr lvl
    filterSize (Size tps szs) = Size tps (runIdentity $ List.mapM (return.filterExpr) szs)

defaultExpr :: Repr tp -> LispExpr tp
defaultExpr tp = case tp of
  BoolRepr -> LispExpr (Const $ BoolValue True)
  IntRepr -> LispExpr (Const $ IntValue 0)
  RealRepr -> LispExpr (Const $ RealValue 0)
  BitVecRepr bw -> LispExpr (Const $ BitVecValue 0 bw)
  ArrayRepr idx el -> LispExpr (App (ConstArray idx el) ((defaultExpr el) ::: Nil))

recDependencies :: LispProgram -> DepState -> Set AnyName
recDependencies prog dep = case todo dep of
  [] -> dependencies dep
  ((AnyName name cat):todo') -> case cat of
    Gate -> case DMap.lookup name (programGates prog) of
      Just gt -> recDependencies prog $ getDependencies (gateDefinition gt) (dep { todo = todo' })
    State -> case DMap.lookup name (programNext prog) of
      Just var -> recDependencies prog $ getDependencies var (dep { todo = todo' })
      Nothing -> error $ "Missing next state for "++show name
    Input -> recDependencies prog $ dep { todo = todo' }

getDependencies :: LispVar LispExpr '(lvl,tp)
                -> DepState -> DepState
getDependencies (NamedVar name@(LispName _ _ _) cat) st
  = if Set.member (AnyName name cat) (dependencies st)
    then st
    else DepState { dependencies = Set.insert (AnyName name cat) $ dependencies st
                  , todo = (AnyName name cat):todo st }
getDependencies (LispStore var _ idx val) st0 = st3
  where
    st1 = getDependencies var st0
    st2 = getDependenciesIndex idx st1
    st3 = getDependenciesExpr val st2
getDependencies (LispConstr val) st
  = execState (foldExprs (\_ v -> do
                             st <- get
                             put $ getDependenciesExpr v st
                             return v
                          ) val) st
getDependencies (LispITE c v1 v2) st0 = st3
  where
    st1 = getDependenciesExpr c st0
    st2 = getDependencies v1 st1
    st3 = getDependencies v2 st2

getDependenciesExpr :: LispExpr a -> DepState -> DepState
getDependenciesExpr (LispExpr (App fun args)) st
  = runIdentity $ List.foldM (\st e -> return $ getDependenciesExpr e st
                             ) st args
getDependenciesExpr (LispRef var _) st
  = getDependencies var st
getDependenciesExpr (LispEq lhs rhs) st
  = getDependencies lhs $
    getDependencies rhs st
getDependenciesExpr (ExactlyOne xs) st
  = foldl (\st x -> getDependenciesExpr x st) st xs
getDependenciesExpr (AtMostOne xs) st
  = foldl (\st x -> getDependenciesExpr x st) st xs
getDependenciesExpr _ st = st

getDependenciesIndex :: List LispExpr lvl -> DepState -> DepState
getDependenciesIndex Nil st = st
getDependenciesIndex (e ::: es) st
  = getDependenciesExpr e $
    getDependenciesIndex es st
