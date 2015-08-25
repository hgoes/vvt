{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.Inliner where

import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Simplify.Dataflow

import Language.SMTLib2.Internals

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable,mapAccumL)
import qualified Data.Text as T
import Control.Monad.Identity
import Data.Typeable (cast)

data Inlining = Inlining { inliningCache :: Map T.Text (Maybe LispVar)
                         , inliningDeps :: DependencyMap }

doInlining :: LispProgram -> LispProgram
doInlining prog = prog { programState = nstate
                       , programInput = ninput
                       , programGates = ngates'
                       , programNext = nnext'
                       , programProperty = nprop
                       , programInit = ninit
                       , programInvariant = ninvar
                       , programAssumption = nassump
                       , programPredicates = npreds }
  where
    inl = Inlining Map.empty (generateDependencyMapUp prog)
    (ngates,inl1) = inlineList (\prog (tp,var) inl
                                -> let (nvar,ninl) = inlineVar prog var inl
                                   in ((tp,nvar),ninl))
                    prog (programGates prog) inl
    (nnext,inl2) = inlineList inlineVar prog (programNext prog) inl1
    (nprop,inl3) = inlineList inlineExpr prog (programProperty prog) inl2
    (ninvar,inl4) = inlineList inlineExpr prog (programInvariant prog) inl3
    (nassump,inl5) = inlineList inlineExpr prog (programAssumption prog) inl4
    (npreds,inl6) = inlineList inlineExpr prog (programPredicates prog) inl5
    -- All variables that have been inlined
    inlined = Map.mapMaybe (\x -> case x of
                              Just inl -> Just ()
                              _ -> Nothing
                           ) (inliningCache inl6)
    nstate = Map.difference (programState prog) inlined
    ninput = Map.difference (programInput prog) inlined
    ngates' = Map.difference ngates inlined
    nnext' = Map.difference nnext inlined
    ninit = Map.difference (programInit prog) inlined

isSimple :: LispVar -> Bool
isSimple (NamedVar _ _ _) = True
isSimple (LispConstr val) = case size val of
  Size [] -> isSimpleStruct (value val)
  _ -> False
  where
    isSimpleStruct (Singleton (Val x)) = isSimpleExpr x
    isSimpleStruct (Struct _) = False

    isSimpleExpr (Const _ _) = True
    isSimpleExpr (InternalObj _ _) = True
    isSimpleExpr _ = False

inlineVar :: LispProgram -> LispVar -> Inlining -> (LispVar,Inlining)
inlineVar prog v@(NamedVar name cat tp) inl = case cat of
  Gate -> let def = snd $ (programGates prog) Map.! name
              (res,ninl) = getInlining prog name def inl
          in (case res of
                Nothing -> v
                Just r -> r,ninl)
  _ -> (v,inl)
inlineVar prog (LispStore var idx idx_dyn expr) inl
  = (LispStore var' idx idx_dyn' expr',inl3)
  where
    (var',inl1) = inlineVar prog var inl
    (idx_dyn',inl2) = inlineList inlineExpr prog idx_dyn inl1
    (expr',inl3) = inlineExpr prog expr inl2
inlineVar prog (LispConstr val) inl = (LispConstr (LispValue { size = Size nsize
                                                             , value = nvalue }),inl2)
  where
    (inl1,nsize) = mapAccumL (\inl (SizeElement expr)
                              -> let (nexpr,ninl) = inlineExpr prog expr inl
                                 in (ninl,SizeElement nexpr)
                             ) inl (sizeElements $ size val)
    (nvalue,inl2) = inlineStruct prog (value val) inl1
    inlineStruct prog (Singleton (Val x)) inl = let (nx,inl') = inlineExpr prog x inl
                                           in (Singleton (Val nx),inl')
    inlineStruct prog (Struct xs) inl
      = let (nxs,ninl) = inlineList inlineStruct prog xs inl
        in (Struct nxs,ninl)
inlineVar prog (LispITE cond v1 v2) inl = (LispITE ncond nv1 nv2,inl3)
  where
    (ncond,inl1) = inlineExpr prog cond inl
    (nv1,inl2) = inlineVar prog v1 inl1
    (nv2,inl3) = inlineVar prog v2 inl2

inlineExpr :: LispProgram -> SMTExpr t -> Inlining -> (SMTExpr t,Inlining)
inlineExpr prog (App fun args) inl = (App fun nargs,ninl)
  where
    (ninl,nargs) = runIdentity $
                   foldExprs (\inl expr _ -> do
                                  let (nexpr,inl') = inlineExpr prog expr inl
                                  return (inl',nexpr)
                             ) inl args (extractArgAnnotation args)
inlineExpr prog (InternalObj (cast -> Just acc) ann) inl = (InternalObj nacc ann,ninl)
  where
    (nacc,ninl) = inlineAccess prog acc inl
inlineExpr prog expr inl = (expr,inl)

inlineList :: Traversable t => (LispProgram -> a -> Inlining -> (a,Inlining))
           -> LispProgram -> t a -> Inlining -> (t a,Inlining)
inlineList f prog xs inl = (nxs,ninl)
  where
    (ninl,nxs) = mapAccumL (\inl x -> let (nx,ninl) = f prog x inl
                                      in (ninl,nx)
                           ) inl xs

inlineAccess :: LispProgram -> LispVarAccess -> Inlining -> (LispVarAccess,Inlining)
inlineAccess prog (LispVarAccess var idx dyn_idx) inl = (LispVarAccess nvar idx ndyn_idx,inl2)
  where
    (nvar,inl1) = inlineVar prog var inl
    (ndyn_idx,inl2) = inlineList inlineExpr prog dyn_idx inl1
inlineAccess prog (LispSizeAccess var idx) inl = (LispSizeAccess nvar nidx,inl2)
  where
    (nvar,inl1) = inlineVar prog var inl
    (nidx,inl2) = inlineList inlineExpr prog idx inl1
inlineAccess prog (LispSizeArrAccess var idx) inl = (LispSizeArrAccess nvar idx,inl1)
  where
    (nvar,inl1) = inlineVar prog var inl
inlineAccess prog (LispEq v1 v2) inl = (LispEq nv1 nv2,inl2)
  where
    (nv1,inl1) = inlineVar prog v1 inl
    (nv2,inl2) = inlineVar prog v2 inl1 

getInlining :: LispProgram -> T.Text -> LispVar -> Inlining -> (Maybe LispVar,Inlining)
getInlining prog name def inl = case Map.lookup name (inliningCache inl) of
  Just res -> (res,inl)
  Nothing -> if isSimple def || Set.size deps < 2
             then (Just nvar,inl1 { inliningCache = Map.insert name (Just nvar) (inliningCache inl1) })
             else (Nothing,inl { inliningCache = Map.insert name Nothing (inliningCache inl) })
    where
      deps = case Map.lookup name (inliningDeps inl) of
        Nothing -> Set.empty
        Just d -> d
      (nvar,inl1) = inlineVar prog def inl
