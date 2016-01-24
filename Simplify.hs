module Simplify where

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Interface
import qualified Language.SMTLib2.Internals.Expression as E
import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List

simplify :: forall i e tp m.
            (GetType e,
             Embed m e,Extract i e,
             EmVar m e ~ ExVar i e,
             EmQVar m e ~ ExQVar i e,
             EmFun m e ~ ExFun i e,
             EmConstr m e ~ ExConstr i e,
             EmField m e ~ ExField i e,
             EmFunArg m e ~ ExFunArg i e,
             EmLVar m e ~ ExLVar i e)
            => i -> e tp -> m (e tp)
simplify i e = case extract i e of
  Just (x :==: (extract i -> Just (ConstBool v))) -> do
    nx <- simplify i x
    if v
      then return nx
      else embed $ Not nx
  Just (AndLst xs) -> do
    xs' <- mapM (simplify i) xs
    embed $ AndLst $ concatAnd xs'
    where
      concatAnd :: [e BoolType] -> [e BoolType]
      concatAnd [] = []
      concatAnd (e:es) = case extract i e of
        Just (AndLst ys) -> ys++concatAnd es
        _ -> e:concatAnd es
  Just (E.App fun args) -> do
    nargs <- List.mapM (simplify i) args
    embed $ E.App fun nargs
  _ -> return e
