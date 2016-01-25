{-# LANGUAGE ViewPatterns #-}
module Realization.Lisp.Simplify.Dataflow where

import Args
import Realization.Lisp
import Realization.Lisp.Value

import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type.Struct (Tree(..))
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Identity
import Control.Monad.State
import Data.GADT.Compare

class Fact (a :: ([Type],Tree Type) -> *) where
  empty :: a sig
  propagateUp :: (forall lvl tps. LispName '(lvl,tps) -> a '(lvl,tps)) -> LispVar e sig -> a sig
  union :: a sig -> a sig -> a sig
  leq :: a sig -> a sig -> Bool

type DependencyMap = Map AnyName (Set AnyName)
type Facts a = DMap LispName a

generateDependencyMapUp :: LispProgram -> DependencyMap
generateDependencyMapUp prog = mp2
  where
    mp1 = DMap.foldlWithKey (\mp name@(LispName _ _ _) var -> depLVar (AnyName name True) var mp
                            ) Map.empty (programNext prog)
    mp2 = DMap.foldlWithKey (\mp name@(LispName _ _ _) gt -> depLVar (AnyName name False) (gateDefinition gt) mp
                            ) mp1 (programGates prog)
    depLVar :: AnyName -> LispVar LispExpr '(lvl,tps)
            -> DependencyMap -> DependencyMap
    depLVar trg (NamedVar name cat) mp
      | cat==Input = mp
      | otherwise  = Map.insertWith Set.union (AnyName name (case cat of
                                                              State -> True
                                                              Gate -> False))
                     (Set.singleton trg) mp
    depLVar trg (LispStore v _ _ el) mp = depLVar trg v (depExpr trg el mp)
    depLVar trg (LispConstr val) mp = depLVal trg val mp
    depLVar trg (LispITE cond v1 v2) mp
      = depExpr trg cond $
        depLVar trg v1 $
        depLVar trg v2 mp
    depLVal :: AnyName -> LispValue '(lvl,tps) LispExpr
            -> DependencyMap -> DependencyMap
    depLVal trg val mp = execState
                         (foldExprs (\_ e -> do
                                        mp <- get
                                        let nmp = depExpr trg e mp
                                        put nmp
                                        return e) val) mp
    depExpr :: AnyName -> LispExpr t -> DependencyMap -> DependencyMap
    depExpr trg (LispExpr (Const _)) mp = mp
    depExpr trg (LispExpr (App _ args)) mp
      = runIdentity $ List.foldM (\mp e -> return $ depExpr trg e mp
                                 ) mp args
    depExpr trg (LispRef var _) mp = depLVar trg var mp
    depExpr trg (LispEq v1 v2) mp = depLVar trg v1 $
                                    depLVar trg v2 mp
    depExpr trg (ExactlyOne xs) mp = foldl (\mp e -> depExpr trg e mp) mp xs
    depExpr trg (AtMostOne xs) mp = foldl (\mp e -> depExpr trg e mp) mp xs

data AnyName = forall lvl tps. AnyName { anyName :: LispName '(lvl,tps)
                                       , isState :: Bool }

instance Eq AnyName where
  (==) (AnyName n1 s1) (AnyName n2 s2)
    = if s1==s2
      then False
      else defaultEq n1 n2

instance Ord AnyName where
  compare (AnyName n1 s1) (AnyName n2 s2) = case compare s1 s2 of
    EQ -> defaultCompare n1 n2
    r -> r
               
bottomUp :: forall a. Fact a => DependencyMap -> LispProgram -> Facts a
bottomUp deps prog = bottomUp' initTodo initFacts
  where
    initTodo = Set.fromList $
               [ AnyName name True
               | name@(LispName _ _ _) :=> _ <- DMap.toList (programState prog) ] ++
               [ AnyName name False
               | name@(LispName _ _ _) :=> _ <- DMap.toList (programGates prog) ]
    initFacts :: Facts a
    initFacts = DMap.fromAscList
                [ name :=> propagateUp (const empty) (LispConstr v)
                | name :=> (LispInit v) <- DMap.toAscList (programInit prog) ]
    bottomUp' todo facts = let (ntodo,nfacts) = bottomUp'' (Set.toList todo) Set.empty facts
                           in if Set.null ntodo
                              then nfacts
                              else bottomUp' ntodo nfacts
    bottomUp'' :: [AnyName] -> Set AnyName -> Facts a -> (Set AnyName,Facts a)
    bottomUp'' [] ntodo facts = (ntodo,facts)
    bottomUp'' (name@(AnyName sym isState):todo) ntodo facts
      = bottomUp'' todo ntodo' nfacts
      where
        ntodo' = if leq fact old_fact'
                 then ntodo
                 else case Map.lookup name deps of
                 Nothing -> ntodo
                 Just d -> Set.union d ntodo
        old_fact' = case old_fact of
          Nothing -> empty
          Just f -> f
        (old_fact,nfacts) = DMap.insertLookupWithKey (const union) sym fact facts
        fact = propagateUp getFact var
        getFact :: LispName sig -> a sig
        getFact v = DMap.findWithDefault empty v facts
        var = if isState
              then case DMap.lookup sym (programNext prog) of
              Just v -> v
              else case DMap.lookup sym (programGates prog) of
              Just gt -> gateDefinition gt
