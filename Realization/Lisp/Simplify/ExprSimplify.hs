{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.ExprSimplify where

import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Array
import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import Data.Either
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare
import Data.Functor.Identity
import Data.List (nub)

simplifyProgram :: LispProgram -> LispProgram
simplifyProgram prog
  = prog { programNext = DMap.mapWithKey (\(LispName _ _ _) -> simplifyVar) (programNext prog)
         , programGates = DMap.mapWithKey
                          (\(LispName _ _ _) gt -> gt { gateDefinition = simplifyVar
                                                                         (gateDefinition gt) }
                          ) (programGates prog)
         , programProperty = fmap simplifyExpr (programProperty prog)
         , programInvariant = fmap simplifyExpr (programInvariant prog)
         , programAssumption = fmap simplifyExpr (programAssumption prog)
         , programPredicates = fmap simplifyExpr (programPredicates prog)
         }

simplifyVar :: LispVar LispExpr '(lvl,tp) -> LispVar LispExpr '(lvl,tp)
simplifyVar (NamedVar name cat) = NamedVar name cat
simplifyVar (LispStore var idx didx val)
  = LispStore (simplifyVar var) idx (simplifyArrayIndex didx) (simplifyExpr val)
simplifyVar (LispConstr val) = LispConstr (simplifyValue val)
simplifyVar (LispITE cond ifT ifF) = case asBoolConst ncond of
  Just True -> nifT
  Just False -> nifF
  _ -> LispITE ncond nifT nifF
  where
    ncond = simplifyExpr cond
    nifT = simplifyVar ifT
    nifF = simplifyVar ifF

simplifyArrayIndex :: List LispExpr lvl
                   -> List LispExpr lvl
simplifyArrayIndex = runIdentity . List.mapM (return.simplifyExpr)

simplifyValue :: LispValue '(lvl,tp) LispExpr -> LispValue '(lvl,tp) LispExpr
simplifyValue (LispValue sz val)
  = LispValue (simplifySize sz) (runIdentity $ Struct.mapM (return.simplifyVal) val)

simplifySize :: Size LispExpr lvl -> Size LispExpr lvl
simplifySize (Size tps szs)
  = Size tps (runIdentity $ List.mapM (return.simplifyExpr) szs)

simplifyVal :: Sized LispExpr lvl tp -> Sized LispExpr lvl tp
simplifyVal (Sized expr) = Sized (simplifyExpr expr)

simplifyExpr :: LispExpr t -> LispExpr t
simplifyExpr (LispExpr (App fun args)) = optimizeFun fun nargs
  where
    nargs = runIdentity $ List.mapM (return.simplifyExpr) args
simplifyExpr (LispRef (LispConstr (LispValue _ val)) idx)
  = case Struct.elementIndex val idx of
  Sized el -> simplifyExpr el
simplifyExpr (LispExpr e) = LispExpr e
simplifyExpr (LispRef var idx)
  = LispRef (simplifyVar var) idx
simplifyExpr (LispSize var idx)
  = LispSize (simplifyVar var) idx
simplifyExpr (LispEq v1 v2) = LispEq (simplifyVar v1) (simplifyVar v2)
simplifyExpr (ExactlyOne []) = LispExpr (Const (BoolValue False))
simplifyExpr (ExactlyOne [x]) = simplifyExpr x
simplifyExpr (ExactlyOne xs) = ExactlyOne (fmap simplifyExpr xs)
simplifyExpr (AtMostOne []) = LispExpr (Const (BoolValue True))
simplifyExpr (AtMostOne [x]) = LispExpr (Const (BoolValue True))
simplifyExpr (AtMostOne xs) = AtMostOne (fmap simplifyExpr xs)

optimizeFun :: Function NoRef NoRef NoRef '(arg,res) -> List LispExpr arg -> LispExpr res
optimizeFun (ITE tp) args@(cond ::: lhs ::: rhs ::: Nil)
  | defaultEq lhs rhs = lhs
  | otherwise = case cond of
  LispExpr (Const (BoolValue c)) -> if c then lhs else rhs
  _ -> case tp of
    BoolRepr -> case (lhs,rhs) of
      (LispExpr (Const (BoolValue True)),LispExpr (Const (BoolValue False)))
        -> cond
      (LispExpr (Const (BoolValue False)),LispExpr (Const (BoolValue True)))
        -> LispExpr (App Not (cond ::: Nil))
      (LispExpr (Const (BoolValue True)),_)
        -> simplifyExpr $ LispExpr (App (Logic Or (Succ (Succ Zero)))
                                    (cond ::: rhs ::: Nil))
      (_,LispExpr (Const (BoolValue True)))
        -> simplifyExpr $ LispExpr (App (Logic Implies (Succ (Succ Zero)))
                                    (cond ::: lhs ::: Nil))
      (_,LispExpr (Const (BoolValue False)))
        -> simplifyExpr $ LispExpr (App (Logic And (Succ (Succ Zero)))
                                    (cond ::: lhs ::: Nil))
      (LispExpr (Const (BoolValue False)),_)
        -> simplifyExpr $ LispExpr (App (Logic And (Succ (Succ Zero)))
                                    ((LispExpr (App Not (cond ::: Nil))) :::
                                     rhs ::: Nil))
      _ -> LispExpr (App (ITE tp) args)
    _ -> LispExpr (App (ITE tp) args)
optimizeFun (Logic XOr (Succ (Succ Zero))) (c ::: (asBoolConst -> Just True) ::: Nil)
  = LispExpr (App Not (c ::: Nil))
optimizeFun (Logic And n) args = case fmap nub $ optAnd (allEqToList n args) of
  Just [] -> LispExpr (Const (BoolValue True))
  Just [c] -> c
  Just args' -> allEqFromList args' $
                \nn nargs -> LispExpr (App (Logic And nn) nargs)
  Nothing -> LispExpr (Const (BoolValue False))
  where
    optAnd [] = Just []
    optAnd ((asBoolConst -> Just False):_) = Nothing
    optAnd ((asBoolConst -> Just True):xs) = optAnd xs
    optAnd (LispExpr (App (Logic And n) x):xs)
      = optAnd (allEqToList n x ++ xs)
    optAnd (x:xs) = do
      xs' <- optAnd xs
      return (x:xs')
optimizeFun (Logic Or n) args = case fmap nub $ optOr (allEqToList n args) of
  Just [] -> LispExpr (Const (BoolValue False))
  Just [c] -> c
  Just args' -> allEqFromList args' $
                \nn nargs -> LispExpr (App (Logic Or nn) nargs)
  Nothing -> LispExpr (Const (BoolValue True))
  where
    optOr [] = Just []
    optOr ((asBoolConst -> Just False):xs) = optOr xs
    optOr ((asBoolConst -> Just True):xs) = Nothing
    optOr (LispExpr (App (Logic Or n) x):xs)
      = optOr (allEqToList n x++xs)
    optOr (x:xs) = do
      xs' <- optOr xs
      return (x:xs')
optimizeFun (Logic Implies (Succ (Succ Zero))) (_ ::: (asBoolConst -> Just True) ::: Nil)
  = LispExpr (Const (BoolValue True))
optimizeFun Not ((asBoolConst -> Just c) ::: Nil) = LispExpr (Const (BoolValue (not c)))
optimizeFun (Arith NumInt Plus n) xs = case dyns of
  [] -> LispExpr (Const (IntValue c))
  [d]
    | c==0 -> d
  _ -> allEqFromList (if c==0
                      then dyns
                      else dyns++[LispExpr (Const (IntValue c))]) $
       \nn nargs -> LispExpr $ App (Arith NumInt Plus nn) nargs
  where
    c = sum consts
    (consts,dyns) = partitionEithers
                    (fmap (\x -> case x of
                             LispExpr (Const (IntValue n)) -> Left n
                             _ -> Right x
                          ) (allEqToList n xs))
optimizeFun (Eq tp (Succ (Succ Zero)))
  ((LispExpr (Const x)) :::
   (LispExpr (Const y)) :::
    Nil) = LispExpr (Const (BoolValue (defaultEq x y)))
optimizeFun f arg = LispExpr (App f arg)

asBoolConst :: LispExpr tp -> Maybe Bool
asBoolConst (LispExpr (Const (BoolValue v))) = Just v
asBoolConst _ = Nothing
