{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.Inliner where

import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Array
import Realization.Lisp.Simplify.Dataflow

import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Struct (Struct(..))

import Data.Traversable (mapAccumL)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Identity
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap

data Inlining = Inlining { inliningCache :: DMap LispName InlineStatus
                         , inliningDeps :: DependencyMap }

data InlineStatus tp where
  Inlined :: LispVar LispExpr tp -> InlineStatus tp
  Used :: InlineStatus tp

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
    inl = Inlining DMap.empty (generateDependencyMapUp prog)
    (ngates,inl1) = inlineMap (\prog gt inl
                               -> let (ndef,ninl) = inlineVar prog (gateDefinition gt) inl
                                   in (gt { gateDefinition = ndef },ninl))
                    prog (programGates prog) inl
    (nnext,inl2) = inlineMap inlineVar prog (programNext prog) inl1
    (nprop,inl3) = inlineList inlineExpr prog (programProperty prog) inl2
    (ninvar,inl4) = inlineList inlineExpr prog (programInvariant prog) inl3
    (nassump,inl5) = inlineList inlineExpr prog (programAssumption prog) inl4
    (npreds,inl6) = inlineList inlineExpr prog (programPredicates prog) inl5
    nstate = filterMap (programState prog) inl6
    ninput = filterMap (programInput prog) inl6
    ngates' = filterMap ngates inl6
    nnext' = filterMap nnext inl6
    ninit = filterMap (programInit prog) inl6

filterMap :: DMap LispName a -> Inlining -> DMap LispName a
filterMap mp inl = DMap.fromAscList
                   [ name :=> ann
                   | name :=> ann <- DMap.toAscList mp
                   , case DMap.lookup name (inliningCache inl) of
                     Just Used -> True
                     Nothing -> True
                     _ -> False ]

inlineMap :: (forall sig. LispProgram -> a sig -> Inlining -> (a sig,Inlining))
          -> LispProgram -> DMap LispName a -> Inlining
          -> (DMap LispName a,Inlining)
inlineMap f prog mp inl = (DMap.fromAscList nlst,ninl)
  where
    lst = DMap.toAscList mp
    (ninl,nlst) = mapAccumL (\inl (name :=> e)
                             -> let (ne,ninl) = f prog e inl
                                in (ninl,name :=> ne)
                            ) inl lst

isSimple :: LispVar LispExpr tp -> Bool
isSimple (NamedVar _ _) = True
isSimple (LispConstr (LispValue sz val)) = case sz of
  Size Nil Nil -> isSimpleStruct val
  _ -> False
  where
    isSimpleStruct :: Struct (Sized LispExpr lvl) tp -> Bool
    isSimpleStruct (Singleton (Sized x)) = isSimpleExpr x
    isSimpleStruct (Struct _) = False

    isSimpleExpr (LispExpr (Const _)) = True
    isSimpleExpr (LispRef _ _) = True
    isSimpleExpr _ = False

inlineVar :: LispProgram -> LispVar LispExpr sig -> Inlining -> (LispVar LispExpr sig,Inlining)
inlineVar prog v@(NamedVar name cat) inl = case cat of
  Gate -> let def = gateDefinition $ (programGates prog) DMap.! name
              (res,ninl) = getInlining prog name Gate def inl
          in (case res of
                Used -> v
                Inlined r -> r,ninl)
  _ -> (v,inl)
inlineVar prog (LispStore var idx idx_dyn expr) inl
  = (LispStore var' idx idx_dyn' expr',inl3)
  where
    (var',inl1) = inlineVar prog var inl
    (idx_dyn',inl2) = inlineArrayIndex prog idx_dyn inl1
    (expr',inl3) = inlineExpr prog expr inl2
inlineVar prog (LispConstr (LispValue sz val)) inl = (LispConstr (LispValue nsize nvalue),inl2)
  where
    (nsize,inl1) = inlineSize prog sz inl
    (nvalue,inl2) = inlineStruct prog val inl1
    inlineStruct :: LispProgram -> Struct (Sized LispExpr lvl) tp
                 -> Inlining -> (Struct (Sized LispExpr lvl) tp,Inlining)
    inlineStruct prog (Singleton (Sized x)) inl
      = let (nx,inl') = inlineExpr prog x inl
        in (Singleton (Sized nx),inl')
    inlineStruct prog (Struct xs) inl
      = let (nxs,ninl) = inlineStructs prog xs inl
        in (Struct nxs,ninl)
    inlineStructs :: LispProgram -> List (Struct (Sized LispExpr lvl)) sig
                  -> Inlining -> (List (Struct (Sized LispExpr lvl)) sig,Inlining)
    inlineStructs prog Nil inl = (Nil,inl)
    inlineStructs prog (x ::: xs) inl
      = let (nx,inl1) = inlineStruct prog x inl
            (nxs,inl2) = inlineStructs prog xs inl1
        in (nx ::: nxs,inl2)
inlineVar prog (LispITE cond v1 v2) inl = (LispITE ncond nv1 nv2,inl3)
  where
    (ncond,inl1) = inlineExpr prog cond inl
    (nv1,inl2) = inlineVar prog v1 inl1
    (nv2,inl3) = inlineVar prog v2 inl2

inlineSize :: LispProgram -> Size LispExpr lvl
           -> Inlining -> (Size LispExpr lvl,Inlining)
inlineSize prog (Size tps szs) inl
  = (Size tps nszs,ninl)
  where
    (ninl,nszs) = runIdentity $ List.mapAccumM
                  (\inl e -> do
                      let (ne,ninl) = inlineExpr prog e inl
                      return (ninl,ne)
                  ) inl szs

inlineExpr :: LispProgram -> LispExpr t -> Inlining -> (LispExpr t,Inlining)
inlineExpr prog (LispExpr (App fun args)) inl = (LispExpr $ App fun nargs,ninl)
  where
    (ninl,nargs) = runIdentity $
                   List.mapAccumM (\inl expr -> do
                                      let (nexpr,inl') = inlineExpr prog expr inl
                                      return (inl',nexpr)
                                  ) inl args
inlineExpr prog (LispExpr e) inl = (LispExpr e,inl)
inlineExpr prog (LispRef var idx) inl = (LispRef nvar idx,inl1)
  where
    (nvar,inl1) = inlineVar prog var inl
inlineExpr prog (LispEq v1 v2) inl = (LispEq nv1 nv2,inl2)
  where
    (nv1,inl1) = inlineVar prog v1 inl
    (nv2,inl2) = inlineVar prog v2 inl1
inlineExpr prog (ExactlyOne xs) inl = (ExactlyOne nxs,ninl)
  where
    (ninl,nxs) = mapAccumL (\inl x -> let (nx,ninl) = inlineExpr prog x inl
                                      in (ninl,nx)
                           ) inl xs
inlineExpr prog (AtMostOne xs) inl = (AtMostOne nxs,ninl)
  where
    (ninl,nxs) = mapAccumL (\inl x -> let (nx,ninl) = inlineExpr prog x inl
                                      in (ninl,nx)
                           ) inl xs

inlineArrayIndex :: LispProgram -> List LispExpr arrlvl
                 -> Inlining -> (List LispExpr arrlvl,
                                 Inlining)
inlineArrayIndex prog idx inl = (nidx,ninl)
  where
    (ninl,nidx) = runIdentity $ List.mapAccumM
                  (\inl e -> do
                      let (ne,ninl) = inlineExpr prog e inl
                      return (ninl,ne)
                  ) inl idx

inlineList :: Traversable t => (LispProgram -> a -> Inlining -> (a,Inlining))
           -> LispProgram -> t a -> Inlining -> (t a,Inlining)
inlineList f prog xs inl = (nxs,ninl)
  where
    (ninl,nxs) = mapAccumL (\inl x -> let (nx,ninl) = f prog x inl
                                      in (ninl,nx)
                           ) inl xs

getInlining :: LispProgram -> LispName sig -> LispVarCat -> LispVar LispExpr sig -> Inlining
            -> (InlineStatus sig,Inlining)
getInlining prog name@(LispName _ _ name') cat def inl = case DMap.lookup name (inliningCache inl) of
  Just res -> (res,inl)
  Nothing -> if isSimple def || Set.size deps < 2
             then (Inlined nvar,inl1 { inliningCache = DMap.insert name (Inlined nvar) (inliningCache inl1) })
             else (Used,inl { inliningCache = DMap.insert name Used (inliningCache inl) })
    where
      deps = case Map.lookup (AnyName name (cat==State)) (inliningDeps inl) of
        Nothing -> Set.empty
        Just d -> d
      (nvar,inl1) = inlineVar prog def inl
      
