module Realization.Lisp.Predicates where

import Realization.Lisp
import Realization.Lisp.Value

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.Struct (Struct(..))
import qualified Language.SMTLib2.Internals.Type.Struct as Struct
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Typeable (cast)
import Data.Foldable
import Prelude hiding (foldl)
import Data.Proxy
import Data.GADT.Compare
import Data.Functor.Identity

ineqPredicates :: (Embed m e,GetType e) => [e IntType] -> m [e BoolType]
ineqPredicates [] = return []
ineqPredicates (i:is) = do
  lts <- mapM (\j -> [expr| (< i j) |]) is
  les <- mapM (\j -> [expr| (<= i j) |]) is
  rest <- ineqPredicates is
  return (lts++les++rest)

statesOfType :: Repr t -> LispProgram -> [LispExpr t]
statesOfType repr prog = DMap.foldlWithKey (\lin name _
                                            -> getStates repr name ++ lin
                                           ) [] (programState prog)
  where
    getStates :: Repr t -> LispName sig -> [LispExpr t]
    getStates repr name@(LispName lvl tps _) = case lvl of
      Zero -> runIdentity $ Struct.flattenIndex
              (\idx repr' -> case geq repr repr' of
                Just Refl -> return [LispRef (NamedVar name State) idx ArrGet lvl]
                Nothing -> return [])
              (return . concat) tps
      _ -> []

{-
linearExpressions :: LispProgram -> Set (SMTExpr Integer)
linearExpressions prog = lin5
  where
    lin1 = foldl (\lin (_,var) -> linearVar var lin
                 ) Set.empty (programGates prog)
    lin2 = foldl (\lin nxt -> linearVar nxt lin
                 ) lin1 (programNext prog)
    lin3 = foldl (\lin prop -> linearExpr prop lin
                 ) lin2 (programProperty prog)
    lin4 = foldl (\lin init -> linearValue init lin
                 ) lin3 (programInit prog)
    lin5 = foldl (\lin inv -> linearExpr inv lin
                 ) lin4 (programInvariant prog)
    
    linearVar :: LispVar -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    linearVar (LispConstr val) cur = linearValue val cur
    linearVar (LispITE cond l1 l2) cur0
      = let cur1 = linearExpr cond cur0
            cur2 = linearVar l1 cur1
            cur3 = linearVar l2 cur2
        in cur3
    linearVar _ cur = cur
    
    linearValue :: LispValue -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    linearValue val cur0
      = let cur1 = linearSize (size val) cur0
            cur2 = foldl (\lin (Val val)
                          -> linearExpr val lin
                         ) cur1 (value val)
        in cur2

    linearSize :: Size -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    linearSize (Size els) cur
      = foldl (\lin el -> linearSizeElement el lin
              ) cur els

    linearSizeElement :: SizeElement -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    linearSizeElement (SizeElement el) cur = case cast el of
      Nothing -> cur
      Just idx -> decomposeLin idx cur
      
    linearExpr :: SMTType a => SMTExpr a -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    linearExpr expr cur = case cast expr of
      Just lin -> decomposeLin lin cur
      Nothing -> case expr of
        App _ args -> fst $ foldExprsId (\lins expr' _ -> (linearExpr expr' lins,expr')
                                        ) cur args (extractArgAnnotation args)
        --InternalObj obj _ -> case cast obj of
        --  Just acc -> 
        _ -> cur

    decomposeLin :: SMTExpr Integer -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    decomposeLin (Const _ _) cur = cur
    decomposeLin expr cur
      | Set.member expr cur = cur
      | otherwise = decomposeLin' expr (Set.insert expr cur)

    decomposeLin' :: SMTExpr Integer -> Set (SMTExpr Integer) -> Set (SMTExpr Integer)
    decomposeLin' (App _ args) cur
      = fst $ foldExprsId (\lins expr' _ -> (linearExpr expr' lins,expr')
                          ) cur args (extractArgAnnotation args)
    decomposeLin' _ cur = cur
-}
