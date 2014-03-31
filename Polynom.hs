{-# LANGUAGE ViewPatterns,StandaloneDeriving #-}
module Polynom where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Views

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (genericReplicate)

import Data.Foldable
import Prelude hiding (all,foldl1)

data PolyExpr a = PolyExpr { polyFactors :: Map (Map Integer Integer) a
                           , polyAnnotation :: SMTAnnotation a }

deriving instance (SMTValue a) => Show (PolyExpr a)

polyAdd :: Num a => PolyExpr a -> PolyExpr a -> PolyExpr a
polyAdd x y
  = PolyExpr { polyFactors = Map.unionWith (+) (polyFactors x) (polyFactors y)
             , polyAnnotation = polyAnnotation x }

polyMul :: Num a => PolyExpr a -> PolyExpr a -> PolyExpr a
polyMul x y
  = PolyExpr { polyFactors = Map.fromListWith (+)
                             [ (Map.unionWith (+) vars1 vars2,fac1*fac2)
                             | (vars1,fac1) <- Map.toList (polyFactors x)
                             , (vars2,fac2) <- Map.toList (polyFactors y) ]
             , polyAnnotation = polyAnnotation x }

polyNeg :: Num a => PolyExpr a -> PolyExpr a
polyNeg expr = expr { polyFactors = fmap negate (polyFactors expr) }

polyToExpr :: SMTArith a => PolyExpr a -> SMTExpr a
polyToExpr expr
  = app plus ([ if Map.null vars
                then constantAnn fac (polyAnnotation expr)
                else app mult $ (constantAnn fac (polyAnnotation expr)):
                     [ Var var' (polyAnnotation expr)
                     | (var,exp) <- Map.toList vars
                     , var' <- genericReplicate exp var ]
              | (vars,fac) <- Map.toList (polyFactors expr) ])

polyFromExpr :: SMTArith a => SMTExpr a -> Maybe (PolyExpr a)
polyFromExpr (asConst -> Just (c,ann))
  = Just (PolyExpr { polyFactors = Map.singleton Map.empty c
                   , polyAnnotation = ann })
polyFromExpr (asVar -> Just (idx,ann))
  = Just (PolyExpr { polyFactors = Map.singleton (Map.singleton idx 1) 1
                   , polyAnnotation = ann })
polyFromExpr (asSum -> Just xs) = do
  xs' <- mapM polyFromExpr xs
  return $ foldl1 polyAdd xs'
polyFromExpr (asProduct -> Just xs) = do
  xs' <- mapM polyFromExpr xs
  return $ foldl1 polyMul xs'
polyFromExpr (asNeg -> Just x) = do
  x' <- polyFromExpr x
  return $ polyNeg x'
polyFromExpr _ = Nothing
