{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.ExprSimplify where

import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Array
import Language.SMTLib2
import qualified Language.SMTLib2.Internals.Expression as E
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
simplifyExpr (LispExpr (E.App fun args)) = optimizeFun fun nargs
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
simplifyExpr (ExactlyOne []) = LispExpr (E.Const (BoolValue False))
simplifyExpr (ExactlyOne [x]) = simplifyExpr x
simplifyExpr (ExactlyOne xs) = ExactlyOne (fmap simplifyExpr xs)
simplifyExpr (AtMostOne []) = LispExpr (E.Const (BoolValue True))
simplifyExpr (AtMostOne [x]) = LispExpr (E.Const (BoolValue True))
simplifyExpr (AtMostOne xs) = AtMostOne (fmap simplifyExpr xs)

optimizeFun :: E.Function NoRef NoRef NoRef '(arg,res) -> List LispExpr arg -> LispExpr res
optimizeFun (E.ITE tp) args@(cond ::: lhs ::: rhs ::: Nil)
  | defaultEq lhs rhs = lhs
  | otherwise = case cond of
  LispExpr (E.Const (BoolValue c)) -> if c then lhs else rhs
  _ -> case tp of
    BoolRepr -> case (lhs,rhs) of
      (LispExpr (E.Const (BoolValue True)),LispExpr (E.Const (BoolValue False)))
        -> cond
      (LispExpr (E.Const (BoolValue False)),LispExpr (E.Const (BoolValue True)))
        -> LispExpr (E.App E.Not (cond ::: Nil))
      (LispExpr (E.Const (BoolValue True)),_)
        -> simplifyExpr $ LispExpr (E.App (E.Logic E.Or (Succ (Succ Zero)))
                                    (cond ::: rhs ::: Nil))
      (_,LispExpr (E.Const (BoolValue True)))
        -> simplifyExpr $ LispExpr (E.App (E.Logic E.Implies (Succ (Succ Zero)))
                                    (cond ::: lhs ::: Nil))
      (_,LispExpr (E.Const (BoolValue False)))
        -> simplifyExpr $ LispExpr (E.App (E.Logic E.And (Succ (Succ Zero)))
                                    (cond ::: lhs ::: Nil))
      (LispExpr (E.Const (BoolValue False)),_)
        -> simplifyExpr $ LispExpr (E.App (E.Logic E.And (Succ (Succ Zero)))
                                    ((LispExpr (E.App E.Not (cond ::: Nil))) :::
                                     rhs ::: Nil))
      _ -> LispExpr (E.App (E.ITE tp) args)
    _ -> LispExpr (E.App (E.ITE tp) args)
optimizeFun (E.Logic E.XOr (Succ (Succ Zero))) (c ::: (asBoolConst -> Just True) ::: Nil)
  = LispExpr (E.App E.Not (c ::: Nil))
optimizeFun (E.Logic E.And n) args = case fmap nub $ optAnd (E.allEqToList n args) of
  Just [] -> LispExpr (E.Const (BoolValue True))
  Just [c] -> c
  Just args' -> E.allEqFromList args' $
                \nn nargs -> LispExpr (E.App (E.Logic E.And nn) nargs)
  Nothing -> LispExpr (E.Const (BoolValue False))
  where
    optAnd [] = Just []
    optAnd ((asBoolConst -> Just False):_) = Nothing
    optAnd ((asBoolConst -> Just True):xs) = optAnd xs
    optAnd (LispExpr (E.App (E.Logic E.And n) x):xs)
      = optAnd (E.allEqToList n x ++ xs)
    optAnd (x:xs) = do
      xs' <- optAnd xs
      return (x:xs')
optimizeFun (E.Logic E.Or n) args = case fmap nub $ optOr (E.allEqToList n args) of
  Just [] -> LispExpr (E.Const (BoolValue False))
  Just [c] -> c
  Just args' -> E.allEqFromList args' $
                \nn nargs -> LispExpr (E.App (E.Logic E.Or nn) nargs)
  Nothing -> LispExpr (E.Const (BoolValue True))
  where
    optOr [] = Just []
    optOr ((asBoolConst -> Just False):xs) = optOr xs
    optOr ((asBoolConst -> Just True):xs) = Nothing
    optOr (LispExpr (E.App (E.Logic E.Or n) x):xs)
      = optOr (E.allEqToList n x++xs)
    optOr (x:xs) = do
      xs' <- optOr xs
      return (x:xs')
optimizeFun (E.Logic E.Implies (Succ (Succ Zero))) (_ ::: (asBoolConst -> Just True) ::: Nil)
  = LispExpr (E.Const (BoolValue True))
optimizeFun E.Not ((asBoolConst -> Just c) ::: Nil) = LispExpr (E.Const (BoolValue (not c)))
optimizeFun (E.Arith NumInt E.Plus n) xs = case dyns of
  [] -> LispExpr (E.Const (IntValue c))
  [d]
    | c==0 -> d
  _ -> E.allEqFromList (if c==0
                        then dyns
                        else dyns++[LispExpr (E.Const (IntValue c))]) $
       \nn nargs -> LispExpr $ E.App (E.Arith NumInt E.Plus nn) nargs
  where
    c = sum consts
    (consts,dyns) = partitionEithers
                    (fmap (\x -> case x of
                             LispExpr (E.Const (IntValue n)) -> Left n
                             _ -> Right x
                          ) (E.allEqToList n xs))
optimizeFun (E.Eq tp (Succ (Succ Zero)))
  ((LispExpr (E.Const x)) :::
   (LispExpr (E.Const y)) :::
    Nil) = LispExpr (E.Const (BoolValue (defaultEq x y)))
optimizeFun (E.Ord NumInt op)
  ((LispExpr (E.Const (IntValue x))) :::
   (LispExpr (E.Const (IntValue y))) ::: Nil)
  = LispExpr (E.Const (BoolValue (case op of
                                     E.Ge -> x>=y
                                     E.Gt -> x>y
                                     E.Le -> x<=y
                                     E.Lt -> x<y)))
optimizeFun f arg = LispExpr (E.App f arg)

asBoolConst :: LispExpr tp -> Maybe Bool
asBoolConst (LispExpr (E.Const (BoolValue v))) = Just v
asBoolConst _ = Nothing
