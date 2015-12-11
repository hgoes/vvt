{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.ExprSimplify where

import Realization.Lisp
import Realization.Lisp.Value
import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Data.Typeable
import Data.List
import Data.Either
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare
import Data.Functor.Identity

import Debug.Trace

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

simplifyArrayIndex :: LispArrayIndex LispExpr lvl rlvl tp
                   -> LispArrayIndex LispExpr lvl rlvl tp
simplifyArrayIndex (ArrGet lvl tp) = ArrGet lvl tp
simplifyArrayIndex (ArrIdx i is) = ArrIdx (simplifyExpr i) (simplifyArrayIndex is)

simplifyValue :: LispValue '(lvl,tp) LispExpr -> LispValue '(lvl,tp) LispExpr
simplifyValue (LispValue sz val)
  = LispValue (simplifySize sz) (mapLispStruct simplifyVal val)

simplifySize :: Size LispExpr lvl -> Size LispExpr lvl
simplifySize NoSize = NoSize
simplifySize (Size i is) = Size (simplifyExpr i) (simplifySize is)

simplifyVal :: LispVal LispExpr lvl tp -> LispVal LispExpr lvl tp
simplifyVal (Val expr) = Val (simplifyExpr expr)

simplifyExpr :: LispExpr t -> LispExpr t
simplifyExpr (LispExpr (App fun args)) = optimizeFun fun nargs
  where
    nargs = runIdentity $ mapArgs (return.simplifyExpr) args
simplifyExpr (LispRef var idx didx) = LispRef (simplifyVar var) idx (simplifyArrayIndex didx)
simplifyExpr (LispEq v1 v2) = LispEq (simplifyVar v1) (simplifyVar v2)
simplifyExpr (ExactlyOne []) = LispExpr (Const (BoolValue False))
simplifyExpr (ExactlyOne [x]) = simplifyExpr x
simplifyExpr (ExactlyOne xs) = ExactlyOne (fmap simplifyExpr xs)
simplifyExpr (AtMostOne []) = LispExpr (Const (BoolValue True))
simplifyExpr (AtMostOne [x]) = LispExpr (Const (BoolValue True))
simplifyExpr (AtMostOne xs) = AtMostOne (fmap simplifyExpr xs)

optimizeFun :: Function NoRef NoRef NoRef '(arg,res) -> Args LispExpr arg -> LispExpr res
optimizeFun (ITE tp) args@(Arg cond (Arg lhs (Arg rhs NoArg)))
  | defaultEq lhs rhs = lhs
  | otherwise = case cond of
  LispExpr (Const (BoolValue c)) -> if c then lhs else rhs
  _ -> case tp of
    BoolRepr -> case (lhs,rhs) of
      (LispExpr (Const (BoolValue True)),LispExpr (Const (BoolValue False)))
        -> cond
      (LispExpr (Const (BoolValue False)),LispExpr (Const (BoolValue True)))
        -> LispExpr (App Not (Arg cond NoArg))
      (LispExpr (Const (BoolValue True)),_)
        -> simplifyExpr $ LispExpr (App (Logic Or (Succ (Succ Zero)))
                                    (Arg cond (Arg rhs NoArg)))
      (_,LispExpr (Const (BoolValue True)))
        -> simplifyExpr $ LispExpr (App (Logic Implies (Succ (Succ Zero)))
                                    (Arg cond (Arg lhs NoArg)))
      (_,LispExpr (Const (BoolValue False)))
        -> simplifyExpr $ LispExpr (App (Logic And (Succ (Succ Zero)))
                                    (Arg cond (Arg lhs NoArg)))
      (LispExpr (Const (BoolValue False)),_)
        -> simplifyExpr $ LispExpr (App (Logic And (Succ (Succ Zero)))
                                    (Arg (LispExpr (App Not (Arg cond NoArg)))
                                     (Arg rhs NoArg)))
      _ -> LispExpr (App (ITE tp) args)
optimizeFun (Logic XOr (Succ (Succ Zero))) (Arg c (Arg (asBoolConst -> Just True) NoArg))
  = LispExpr (App Not (Arg c NoArg))
optimizeFun (Logic And n) args = case optAnd (allEqToList n args) of
  Just [] -> LispExpr (Const (BoolValue True))
  Just [c] -> c
  Just args' -> allEqFromList args' $
                \nn nargs -> LispExpr (App (Logic And nn) nargs)
  Nothing -> LispExpr (Const (BoolValue False))
  where
    optAnd [] = Just []
    optAnd ((asBoolConst -> Just False):_) = Nothing
    optAnd ((asBoolConst -> Just True):xs) = optAnd xs
    optAnd (LispExpr (App (Logic And n) x):xs) = fmap (allEqToList n x++) $ optAnd xs
    optAnd (x:xs) = fmap (x:) $ optAnd xs
optimizeFun (Logic Or n) args = case [ arg | arg <- allEqToList n args
                                          , asBoolConst arg /= Just False ] of
  [] -> LispExpr (Const (BoolValue False))
  [c] -> c
  args' -> allEqFromList args' $
           \nn nargs -> LispExpr (App (Logic Or nn) nargs)
optimizeFun (Logic Implies (Succ (Succ Zero))) (Arg _ (Arg (asBoolConst -> Just True) NoArg))
  = LispExpr (Const (BoolValue True))
optimizeFun Not (Arg (asBoolConst -> Just c) NoArg) = LispExpr (Const (BoolValue (not c)))
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
  (Arg (LispExpr (Const x))
   (Arg (LispExpr (Const y))
    NoArg)) = LispExpr (Const (BoolValue (defaultEq x y)))
optimizeFun f arg = LispExpr (App f arg)

asBoolConst :: LispExpr tp -> Maybe Bool
asBoolConst (LispExpr (Const (BoolValue v))) = Just v
asBoolConst _ = Nothing
