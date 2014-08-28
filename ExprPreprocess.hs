{-# LANGUAGE ViewPatterns,ScopedTypeVariables,GADTs #-}
module ExprPreprocess where

import Language.SMTLib2
import Language.SMTLib2.Views
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Optimize
import Data.Fix

import Data.List (nub)
import Data.Typeable (cast)
import qualified Data.Map as Map

removeGuards :: SMTType a => SMTExpr a -> [([SMTExpr Bool],SMTExpr a)]
removeGuards (asITE -> Just (cond,lhs,rhs))
  | cond' == constant True = removeGuards lhs
  | cond' == constant False = removeGuards rhs
  | otherwise = [ (cond:condL,lhs') | (condL,lhs') <- removeGuards lhs ] ++
                [ ((not' cond):condR,rhs') | (condR,rhs') <- removeGuards rhs ]
  where
    cond' = case optimizeExpr cond of
      Just c -> c
      Nothing -> cond
removeGuards (asAnyApp removeFunGuards -> Just res) = res
removeGuards x = [([],x)]

removeFunGuards :: (Args arg,SMTType res) => SMTFunction arg res -> arg -> Maybe [([SMTExpr Bool],SMTExpr res)]
removeFunGuards fun arg
  = Just [ (cond,app fun arg')
         | (cond,arg') <- removeArgGuards arg ]

removeArgGuards :: Args a => a -> [([SMTExpr Bool],a)]
removeArgGuards x
  = [ (conds,arg)
    | (conds,xs) <- remove unts
    , let Just (arg,[]) = toArgs (extractArgAnnotation x) xs ]
  where
    unts = fromArgs x

    remove [] = []
    remove [UntypedExpr x] = [ (cond,[UntypedExpr x'])
                             | (cond,x') <- removeGuards x ]
    remove ((UntypedExpr x):xs)
      = [ (cond++cond',(UntypedExpr x'):xs')
        | (cond,x') <- removeGuards x
        , (cond',xs') <- remove xs ]

removeInputs :: (Args inp,Args b) => ArgAnnotation inp -> ArgAnnotation b -> (inp -> b) -> [b]
removeInputs ann_inp ann_st fun = rexpr
  where
    ((n,mp),inp) = foldExprsId (\(n,mp) (_::SMTExpr a) ann -> ((n+1,Map.insert n (ProxyArg (undefined::a) ann) mp),InternalObj n ann)
                               ) (0::Integer,Map.empty) undefined ann_inp
    xs = fun inp
    rexpr = Map.foldlWithKey (\exprs n prx
                               -> if prx == ProxyArg (undefined::Bool) ()
                                  then [optimizeArgs ann_st $ replaceExpr (InternalObj n ()) (Const val ()) expr
                                       | val <- [False,True]
                                       , expr <- exprs ]
                                  else (if prx == ProxyArg (undefined::Integer) ()
                                        then [optimizeArgs ann_st $ replaceExpr (InternalObj n ()) (Const val ()) expr
                                             | val <- [0,1::Integer]
                                             , expr <- exprs ]
                                        else exprs)
                             ) [xs] mp

optimizeArgs :: Args a => ArgAnnotation a -> a -> a
optimizeArgs ann args = snd $ foldExprsId (\_ e _ -> ((),optimizeExpr' e)) () args ann

--optimizeExpr' :: SMTExpr t -> SMTExpr t
--optimizeExpr' e = case optimizeExpr e of
--  Nothing -> e
--  Just e' -> e'

replaceExpr :: (SMTType t,Args a) => SMTExpr t -> SMTExpr t -> a -> a
replaceExpr old new expr
  = snd $ foldArgs (\_ expr' -> case cast expr' of
                       Nothing -> ((),expr')
                       Just expr'' -> if expr''==old
                                      then (case cast new of
                                               Just new' -> ((),new'))
                                      else ((),expr')
                   ) () expr
