{-# LANGUAGE ViewPatterns,StandaloneDeriving #-}
module Affine where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Views

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Foldable
import Prelude hiding (all,foldl1)

data AffineExpr a = AffineExpr { affineFactors :: Map Integer a
                               , affineConstant :: a
                               , affineAnnotation :: SMTAnnotation a
                               }

deriving instance (SMTValue a) => Show (AffineExpr a)
deriving instance (SMTValue a) => Eq (AffineExpr a)
deriving instance (SMTValue a) => Ord (AffineExpr a)

affineAdd :: Num a => AffineExpr a -> AffineExpr a -> AffineExpr a
affineAdd x y
  = AffineExpr { affineFactors = Map.unionWith (+) (affineFactors x) (affineFactors y)
               , affineConstant = (affineConstant x)+(affineConstant y)
               , affineAnnotation = affineAnnotation x
               }

affineMul :: (Eq a,Num a) => AffineExpr a -> AffineExpr a -> Maybe (AffineExpr a)
affineMul x y
  | all (==0) (affineFactors x) = Just (AffineExpr { affineFactors = fmap (*(affineConstant x)) (affineFactors y)
                                                   , affineConstant = (affineConstant x)*(affineConstant y)
                                                   , affineAnnotation = affineAnnotation x })
  | all (==0) (affineFactors y) = Just (AffineExpr { affineFactors = fmap (*(affineConstant y)) (affineFactors x)
                                                   , affineConstant = (affineConstant x)*(affineConstant y)
                                                   , affineAnnotation = affineAnnotation x })
  | otherwise = Nothing

affineNeg :: Num a => AffineExpr a -> AffineExpr a
affineNeg expr = expr { affineFactors = fmap negate (affineFactors expr)
                      , affineConstant = negate (affineConstant expr) }

affineToExpr :: SMTArith a => AffineExpr a -> SMTExpr a
affineToExpr expr
  = case summands of
    [] -> constantAnn 0 (affineAnnotation expr)
    [x] -> x
    _ -> app plus summands
  where
    summands = [ case c of
                    1 -> Var v (affineAnnotation expr)
                    -1 -> app neg (Var v (affineAnnotation expr))
                    _ -> app mult [Var v (affineAnnotation expr)
                                  ,constantAnn c (affineAnnotation expr)]
               | (v,c) <- Map.toList $ affineFactors expr,
                 c /= 0 ]++
               (if affineConstant expr == 0
                then []
                else [constantAnn (affineConstant expr) (affineAnnotation expr)])
    
affineFromExpr :: SMTArith a => SMTExpr a -> Maybe (AffineExpr a)
affineFromExpr (asConst -> Just (c,ann))
  = Just (AffineExpr { affineFactors = Map.empty
                     , affineConstant = c
                     , affineAnnotation = ann })
affineFromExpr (asVar -> Just (idx,ann))
  = Just (AffineExpr { affineFactors = Map.singleton idx 1
                     , affineConstant = 0
                     , affineAnnotation = ann })
affineFromExpr (asSum -> Just xs) = do
  xs' <- mapM affineFromExpr xs
  return $ foldl1 affineAdd xs'
affineFromExpr (asMinus -> Just (x,y)) = do
  x' <- affineFromExpr x
  y' <- affineFromExpr y
  return $ affineAdd x' (affineNeg y')
affineFromExpr (asProduct -> Just xs) = do
  x':xs' <- mapM affineFromExpr xs
  foldlM affineMul x' xs'
affineFromExpr (asNeg -> Just x) = do
  x' <- affineFromExpr x
  return $ affineNeg x'
affineFromExpr _ = Nothing
