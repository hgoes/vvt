module Realization.Lisp.Simplify.Slicing where

import Args
import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Array

import Language.SMTLib2
import qualified Language.SMTLib2.Internals.Type.List as List
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import qualified Language.SMTLib2.Internals.Expression as E

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
                  , programInvariant = fmap (eliminateKeep (JustVal $ BoolValue True)
                                             (\name' cat' -> Set.member (AnyName name' cat') deps))
                                       (programInvariant prog)
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

defaultExpr :: Repr tp -> LispExpr tp
defaultExpr tp = case tp of
  BoolRepr -> LispExpr (ConstBool False)
  IntRepr -> LispExpr (ConstInt 0)
  RealRepr -> LispExpr (ConstReal 0)
  BitVecRepr bw -> LispExpr (ConstBV 0 bw)
  ArrayRepr idx el -> LispExpr (ConstArray idx (defaultExpr el))

defaultVal :: Repr tp -> Value tp
defaultVal tp = case tp of
  BoolRepr -> BoolValue False
  IntRepr -> IntValue 0
  RealRepr -> RealValue 0
  BitVecRepr bw -> BitVecValue 0 bw

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
getDependenciesExpr (LispExpr (E.App fun args)) st
  = runIdentity $ List.foldM (\st e -> return $ getDependenciesExpr e st
                             ) st args
getDependenciesExpr (LispExpr _) st = st
getDependenciesExpr (LispRef var _) st
  = getDependencies var st
getDependenciesExpr (LispSize var _) st
  = getDependencies var st
getDependenciesExpr (LispEq lhs rhs) st
  = getDependencies lhs $
    getDependencies rhs st
getDependenciesExpr (ExactlyOne xs) st
  = foldl (\st x -> getDependenciesExpr x st) st xs
getDependenciesExpr (AtMostOne xs) st
  = foldl (\st x -> getDependenciesExpr x st) st xs

getDependenciesIndex :: List LispExpr lvl -> DepState -> DepState
getDependenciesIndex Nil st = st
getDependenciesIndex (e ::: es) st
  = getDependenciesExpr e $
    getDependenciesIndex es st

data OptValue tp
  = JustVal (Value tp)
  | NoVal (Repr tp)

-- | Eliminates a variable from an expression and tries to keep the value of the expression.
eliminateKeep :: OptValue t             -- ^ The value the expression should be able to evaluate to
              -> (forall lvl tps.
                  LispName '(lvl,tps) -> LispVarCat -> Bool)
              -> LispExpr t
              -> LispExpr t
eliminateKeep val filter (LispRef (var::LispVar LispExpr '(sz,tps')) idx)
  = LispRef (eliminateKeepVar nval filter var) idx
  where
    (varSz,varTp) = lispVarType var
    nval = mkVal varTp varSz idx val
    mkVal :: Struct.Struct Repr sig
          -> List Repr sz
          -> List Natural idx
          -> OptValue (Arrayed sz (Struct.ElementIndex sig idx))
          -> LispValue '(sz,sig) OptValue
    mkVal sig sz idx val
      = LispValue
        (Size varSz (runIdentity $ List.mapM (return . NoVal) (sizeListType varSz)))
        (runIdentity $ Struct.mapIndexM (\idx' repr -> case geq idx idx' of
                                            Just Refl -> return (Sized val)
                                            Nothing -> return (Sized $ NoVal $ arrayType sz repr)
                                        ) sig)
eliminateKeep (JustVal (BoolValue v)) filter (LispExpr (E.App E.Not (x ::: Nil)))
  = LispExpr $ E.App E.Not (eliminateKeep (JustVal $ BoolValue $ not v) filter x ::: Nil)
eliminateKeep (JustVal (BoolValue v)) filter (ExactlyOne [x])
  = eliminateKeep (JustVal $ BoolValue v) filter x
eliminateKeep _ filter (ExactlyOne xs)
  = ExactlyOne (fmap (eliminateKeep (JustVal $ BoolValue False) filter) xs)
eliminateKeep val filter (LispExpr (E.App fun args))
  = LispExpr (E.App fun nargs)
  where
    nargs = runIdentity $ List.mapM (\e -> return $ eliminateKeep (NoVal $ getType e) filter e) args
eliminateKeep _ _ e = e

eliminateKeepVar :: LispValue sig OptValue
                 -> (forall lvl tps.
                     LispName '(lvl,tps) -> LispVarCat -> Bool)
                 -> LispVar LispExpr sig
                 -> LispVar LispExpr sig
eliminateKeepVar (LispValue _ val) filter (LispConstr (LispValue sz cval))
  = LispConstr (LispValue nsize nval)
  where
    nsize = case sz of
      Size tps szs -> Size tps (runIdentity $ List.mapM (\e -> return $ eliminateKeep (NoVal (getType e)) filter e) szs)
    nval = mkVal val cval
    mkVal :: Struct.Struct (Sized OptValue sz) sig
          -> Struct.Struct (Sized LispExpr sz) sig
          -> Struct.Struct (Sized LispExpr sz) sig
    mkVal val var = runIdentity $ Struct.zipWithM
                      (\(Sized val') (Sized e) -> return $ Sized $ eliminateKeep val' filter e) val var
eliminateKeepVar (LispValue sz val) filter var@(NamedVar name cat)
  = if filter name cat
    then var
    else LispConstr (LispValue nsz nval)
  where
    nsz = case sz of
      Size tps szs -> Size tps (runIdentity $ List.mapM (\v -> case v of
                                                            JustVal v' -> return $ LispExpr $ E.Const v'
                                                            NoVal tp -> return $ defaultExpr tp
                                                        ) szs)
    nval = runIdentity $ Struct.mapM (\(Sized val) -> case val of
                                         JustVal val' -> return $ Sized $ LispExpr $ E.Const val'
                                         NoVal tp -> return $ Sized $ defaultExpr tp
                                     ) val
eliminateKeepVar val filter (LispITE c ifT ifF)
  = LispITE (eliminateKeep (NoVal bool) filter c)
    (eliminateKeepVar val filter ifT)
    (eliminateKeepVar val filter ifF)
