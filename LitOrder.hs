module LitOrder where

import Domain

import Prelude hiding (foldl)
import Data.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

type LitOrder = Map Int Float

decayOrder :: LitOrder -> LitOrder
decayOrder = fmap (* 0.99)

updateOrder :: AbstractState a -> LitOrder -> LitOrder
updateOrder st order
  = foldl (\mp (nd,_) -> Map.insertWith (+) nd 1 mp) (decayOrder order) st

compareOrder :: LitOrder -> Int -> Int -> Ordering
compareOrder order n1 n2
  = compare (Map.findWithDefault 0 n2 order)
    (Map.findWithDefault 0 n1 order)

addOrderElement :: Int -> LitOrder -> LitOrder
addOrderElement el order = Map.insert el (val+1) order
  where
    val = if Map.null order
          then 1
          else maximum order
