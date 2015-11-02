{-# LANGUAGE ViewPatterns #-}
module Realization.Lisp.Simplify.Dataflow where

import Realization.Lisp
import Realization.Lisp.Value

import Language.SMTLib2.Internals

import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Identity
import Data.Typeable (cast)

class Fact a where
  empty :: a
  propagateUp :: (T.Text -> a) -> LispVar -> a
  union :: a -> a -> a
  leq :: a -> a -> Bool

type DependencyMap = Map T.Text (Set T.Text)

generateDependencyMapUp :: LispProgram -> DependencyMap
generateDependencyMapUp prog = mp2
  where
    mp1 = Map.foldlWithKey (\mp trg var -> depLVar trg var mp
                           ) Map.empty (programNext prog)
    mp2 = Map.foldlWithKey (\mp trg (_,var) -> depLVar trg var mp
                           ) mp1 (programGates prog)
    depLVar :: T.Text -> LispVar -> DependencyMap -> DependencyMap
    depLVar trg (NamedVar name cat _) mp
      | cat==Input = mp
      | otherwise  = Map.insertWith Set.union name (Set.singleton trg) mp
    depLVar trg (LispStore v _ _ _) mp = depLVar trg v mp
    depLVar trg (LispConstr val) mp = depLVal trg val mp
    depLVar trg (LispITE cond v1 v2) mp
      = depExpr trg cond $
        depLVar trg v1 $
        depLVar trg v2 mp
    depLVal trg val mp = fst $ runIdentity $
                         foldExprsWithIndex (\mp _ expr -> return (depExpr trg expr mp,expr)
                                            ) mp val
    depExpr :: T.Text -> SMTExpr t -> DependencyMap -> DependencyMap
    depExpr trg (Const _ _) mp = mp
    depExpr trg (App _ args) mp = fst $ runIdentity $
                                  foldExprs (\mp expr _ -> return (depExpr trg expr mp,expr)
                                            ) mp args (extractArgAnnotation args)
    depExpr trg (InternalObj (cast -> Just acc) _) mp = depAccess trg acc mp
    depAccess trg (LispVarAccess v _ _) mp = depLVar trg v mp
    depAccess trg (LispEq v1 v2) mp = depLVar trg v1 $
                                      depLVar trg v2 mp

bottomUp :: Fact a => DependencyMap -> LispProgram -> Map T.Text a
bottomUp deps prog = bottomUp' initTodo initFacts
  where
    initTodo = Set.union
               (Map.keysSet (programState prog))
               (Map.keysSet (programGates prog))
    initFacts = fmap (\v -> propagateUp (const empty) (LispConstr v)
                     ) (programInit prog)
    bottomUp' todo facts = let (ntodo,nfacts) = bottomUp'' (Set.toList todo) Set.empty facts
                           in if Set.null ntodo
                              then nfacts
                              else bottomUp' ntodo nfacts
    bottomUp'' [] ntodo facts = (ntodo,facts)
    bottomUp'' (sym:todo) ntodo facts
      = bottomUp'' todo ntodo' nfacts
      where
        ntodo' = if leq fact old_fact'
                 then ntodo
                 else case Map.lookup sym deps of
                 Nothing -> ntodo
                 Just d -> Set.union d ntodo
        old_fact' = case old_fact of
          Nothing -> empty
          Just f -> f
        (old_fact,nfacts) = Map.insertLookupWithKey (const union) sym fact facts
        fact = propagateUp getFact var
        getFact v = Map.findWithDefault empty v facts
        var = case Map.lookup sym (programNext prog) of
          Just v -> v
          Nothing -> case Map.lookup sym (programGates prog) of
            Just (_,v) -> v
