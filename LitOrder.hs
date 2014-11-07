module LitOrder where

import Domain

import Prelude hiding (foldl)
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map

type LitOrder = Map Int Float

decayOrder :: LitOrder -> LitOrder
decayOrder = fmap (* 0.99)

updateOrder :: AbstractState a -> LitOrder -> LitOrder
updateOrder st order
  = foldl (\mp (nd,_) -> Map.insertWith (+) nd 1 mp) order st

compareOrder :: LitOrder -> Int -> Int -> Ordering
compareOrder order n1 n2
  = compare (Map.findWithDefault 0 n2 order)
    (Map.findWithDefault 0 n1 order)
