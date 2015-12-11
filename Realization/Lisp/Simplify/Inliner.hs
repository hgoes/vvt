{-# LANGUAGE GADTs,ViewPatterns #-}
module Realization.Lisp.Simplify.Inliner where

import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Simplify.Dataflow

import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable,mapAccumL)
import qualified Data.Text as T
import Control.Monad.Identity
import Data.Typeable (cast)
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
    ngates' = filterMap (programGates prog) inl6
    nnext' = filterMap (programNext prog) inl6
    ninit = filterMap (programInit prog) inl6

filterMap :: DMap LispName a -> Inlining -> DMap LispName a
filterMap mp inl = DMap.fromAscList
                   [ name :=> ann
                   | name :=> ann <- DMap.toAscList mp
                   , case DMap.lookup name (inliningCache inl) of
                     Just Used -> True
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
isSimple (LispConstr val) = case size val of
  NoSize -> isSimpleStruct (value val)
  _ -> False
  where
    isSimpleStruct :: LispStruct (LispVal LispExpr lvl) tp -> Bool
    isSimpleStruct (LSingleton (Val x)) = isSimpleExpr x
    isSimpleStruct (LStruct _) = False

    isSimpleExpr (LispExpr (Const _)) = True
    isSimpleExpr (LispRef _ _ _) = True
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
inlineVar prog (LispConstr val) inl = (LispConstr (LispValue { size = nsize
                                                             , value = nvalue }),inl2)
  where
    (nsize,inl1) = inlineSize prog (size val) inl
    (nvalue,inl2) = inlineStruct prog (value val) inl1
    inlineStruct :: LispProgram -> LispStruct (LispVal LispExpr lvl) tp
                 -> Inlining -> (LispStruct (LispVal LispExpr lvl) tp,Inlining)
    inlineStruct prog (LSingleton (Val x)) inl
      = let (nx,inl') = inlineExpr prog x inl
        in (LSingleton (Val nx),inl')
    inlineStruct prog (LStruct xs) inl
      = let (nxs,ninl) = inlineStructs prog xs inl
        in (LStruct nxs,ninl)
    inlineStructs :: LispProgram -> StructArgs (LispVal LispExpr lvl) sig
                  -> Inlining -> (StructArgs (LispVal LispExpr lvl) sig,Inlining)
    inlineStructs prog NoSArg inl = (NoSArg,inl)
    inlineStructs prog (SArg x xs) inl
      = let (nx,inl1) = inlineStruct prog x inl
            (nxs,inl2) = inlineStructs prog xs inl1
        in (SArg nx nxs,inl2)
inlineVar prog (LispITE cond v1 v2) inl = (LispITE ncond nv1 nv2,inl3)
  where
    (ncond,inl1) = inlineExpr prog cond inl
    (nv1,inl2) = inlineVar prog v1 inl1
    (nv2,inl3) = inlineVar prog v2 inl2

inlineSize :: LispProgram -> Size LispExpr lvl
           -> Inlining -> (Size LispExpr lvl,Inlining)
inlineSize prog NoSize inl = (NoSize,inl)
inlineSize prog (Size e es) inl = (Size ne nes,inl2)
  where
    (ne,inl1) = inlineExpr prog e inl
    (nes,inl2) = inlineSize prog es inl1

inlineExpr :: LispProgram -> LispExpr t -> Inlining -> (LispExpr t,Inlining)
inlineExpr prog (LispExpr (App fun args)) inl = (LispExpr $ App fun nargs,ninl)
  where
    (ninl,nargs) = runIdentity $
                   mapAccumArgs (\inl expr -> do
                                    let (nexpr,inl') = inlineExpr prog expr inl
                                    return (inl',nexpr)
                                ) inl args
inlineExpr prog (LispExpr e) inl = (LispExpr e,inl)
inlineExpr prog (LispRef var idx dyn_idx) inl = (LispRef nvar idx ndyn,inl2)
  where
    (nvar,inl1) = inlineVar prog var inl
    (ndyn,inl2) = inlineArrayIndex prog dyn_idx inl1
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

inlineArrayIndex :: LispProgram -> LispArrayIndex LispExpr lvl rlvl tp
                 -> Inlining -> (LispArrayIndex LispExpr lvl rlvl tp,
                                 Inlining)
inlineArrayIndex _ (ArrGet lvl tp) inl = (ArrGet lvl tp,inl)
inlineArrayIndex prog (ArrIdx i is) inl = (ArrIdx ni nis,inl2)
  where
    (ni,inl1) = inlineExpr prog i inl
    (nis,inl2) = inlineArrayIndex prog is inl1

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
      
