{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.ExprSimplify where

import Realization.Lisp
import Realization.Lisp.Value
import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Data.Typeable
import Data.List
import Data.Either

import Debug.Trace

simplifyProgram :: LispProgram -> LispProgram
simplifyProgram prog
  = prog { programNext = fmap simplifyVar (programNext prog)
         , programGates = fmap (\(tp,var,ann) -> (tp,simplifyVar var,ann)) (programGates prog)
         , programProperty = fmap simplifyExpr (programProperty prog)
         , programInvariant = fmap simplifyExpr (programInvariant prog)
         , programAssumption = fmap simplifyExpr (programAssumption prog)
         , programPredicates = fmap simplifyExpr (programPredicates prog)
         }

simplifyVar :: LispVar -> LispVar
simplifyVar (NamedVar name cat tp) = NamedVar name cat tp
simplifyVar (LispStore var idx didx val)
  = LispStore (simplifyVar var) idx (fmap simplifyExpr didx) (simplifyExpr val)
simplifyVar (LispConstr val) = LispConstr (simplifyValue val)
simplifyVar (LispITE cond ifT ifF) = case ncond of
  Const True _ -> nifT
  Const False _ -> nifF
  _ -> LispITE ncond nifT nifF
  where
    ncond = simplifyExpr cond
    nifT = simplifyVar ifT
    nifF = simplifyVar ifF

simplifyValue :: LispValue -> LispValue
simplifyValue (LispValue sz val)
  = LispValue (Size $ fmap simplifySize (sizeElements sz)) (fmap simplifyVal val)

simplifySize :: SizeElement -> SizeElement
simplifySize (SizeElement expr) = SizeElement (simplifyExpr expr)

simplifyVal :: LispVal -> LispVal
simplifyVal (Val expr) = Val (simplifyExpr expr)

simplifyExpr :: SMTExpr t -> SMTExpr t
simplifyExpr (App fun args) = optimizeFun fun nargs
  where
    (_,nargs) = foldExprsId (\_ e _ -> ((),simplifyExpr e)) () args (extractArgAnnotation args)
simplifyExpr (InternalObj (cast -> Just acc) ann) = simplifyAccess ann acc
simplifyExpr (UntypedExpr e) = UntypedExpr (simplifyExpr e)
simplifyExpr (UntypedExprValue e) = UntypedExprValue (simplifyExpr e)
simplifyExpr e = e

simplifyAccess :: SMTType t => SMTAnnotation t -> LispVarAccess -> SMTExpr t
simplifyAccess ann (LispVarAccess var sidx didx)
  = simplify (simplifyVar var) sidx (fmap simplifyExpr didx)
  where
    simplify v@(LispStore var sidx' didx' e) sidx didx
      | sidx==sidx' = if null didx
                      then castUntypedExpr e
                      else InternalObj (LispVarAccess v sidx didx) ann
      | otherwise = simplify var sidx didx
    simplify (LispConstr (LispValue (Size []) (Singleton (Val v)))) [] []
      = case cast v of
          Just e -> e
    simplify v sidx didx = InternalObj (LispVarAccess v sidx didx) ann
simplifyAccess ann (LispSizeAccess var idx)
  = InternalObj (LispSizeAccess (simplifyVar var) (fmap simplifyExpr idx)) ann
simplifyAccess ann (LispSizeArrAccess var idx)
  = InternalObj (LispSizeArrAccess (simplifyVar var) idx) ann
simplifyAccess ann (LispEq lhs rhs)
  = InternalObj (LispEq (simplifyVar lhs) (simplifyVar rhs)) ann

optimizeFun :: (Args arg,SMTType res) => SMTFunction arg res -> arg -> SMTExpr res
optimizeFun SMTITE (cond,lhs,rhs)
  | lhs==rhs = lhs
  | otherwise = case asBoolConst cond of
  Just True -> lhs
  Just False -> rhs
  Nothing -> case cast (lhs,rhs) of
    Just (blhs,brhs) -> case (asBoolConst blhs,asBoolConst brhs) of
      (Just True,Just False) -> case cast cond of
        Just r -> r
      (Just True,Nothing) -> case cast rhs of
        Just r -> case cast $ App (SMTLogic Or) [cond,r] of
          Just r -> simplifyExpr r
      (Nothing,Just True) -> case cast lhs of
        Just r -> case cast $ App (SMTLogic Implies) [cond,r] of
          Just r -> simplifyExpr r
      (Nothing,Just False) -> case cast lhs of
        Just r -> case cast $ App (SMTLogic And) [cond,r] of
          Just r -> simplifyExpr r
      (Just False,Just True) -> case cast $ App SMTNot cond of
        Just r -> r
      (Just False,Nothing) -> case cast rhs of
        Just r -> case cast $ App (SMTLogic And) [App SMTNot cond,r] of
          Just r -> simplifyExpr r
      _ -> App SMTITE (cond,lhs,rhs)
    _ -> App SMTITE (cond,lhs,rhs)
optimizeFun (SMTLogic XOr) [c,Const True _] = not' c
optimizeFun (SMTLogic And) args = case optAnd args of
  Just [] -> constant True
  Just [c] -> c
  Just args' -> App (SMTLogic And) args'
  Nothing -> constant False
  where
    optAnd [] = Just []
    optAnd (Const False _:_) = Nothing
    optAnd (Const True _:xs) = optAnd xs
    optAnd ((App (SMTLogic And) x):xs) = fmap (x++) $ optAnd xs
    optAnd (x:xs) = fmap (x:) $ optAnd xs
optimizeFun (SMTLogic Or) args = case [ arg | arg <- args
                                            , asBoolConst arg /= Just False ] of
  [] -> constant False
  [c] -> c
  args' -> App (SMTLogic Or) args'
optimizeFun (SMTLogic Implies) [_,Const True _] = Const True ()
optimizeFun SMTNot (Const False _) = Const True ()
optimizeFun SMTNot (Const True _) = Const False ()
optimizeFun (SMTArith Plus) xs = case dyns of
  [] -> Const c ann
  [d]
    | c==0 -> d
  _ -> App (SMTArith Plus) $ if c==0
                             then dyns
                             else dyns++[Const c ann]
  where
    c = sum consts
    (consts,dyns) = partitionEithers
                    (fmap (\x -> case x of
                             Const n _ -> Left n
                             _ -> Right x
                          ) xs)
    ann = case dyns of
      x:_ -> extractAnnotation x
optimizeFun SMTEq [Const x _,Const y _] = Const (x==y) ()
optimizeFun f arg = App f arg

asBoolConst :: SMTExpr Bool -> Maybe Bool
asBoolConst (Const v ()) = Just v
asBoolConst (InternalObj (cast -> Just acc) ann) = asBoolAcc acc
  where
    asBoolAcc :: LispVarAccess -> Maybe Bool
    asBoolAcc (LispVarAccess var [] []) = asBoolVar var
    asBoolAcc _ = Nothing

    asBoolVar :: LispVar -> Maybe Bool
    asBoolVar (LispConstr val) = asBoolVal val
    asBoolVar _ = Nothing

    asBoolVal :: LispValue -> Maybe Bool
    asBoolVal (LispValue (Size []) (Singleton (Val v))) = do
      expr <- cast v
      asBoolConst expr
    asBoolVal _ = Nothing
asBoolConst _ = Nothing
