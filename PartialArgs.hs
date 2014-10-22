{-# LANGUAGE TypeFamilies,ScopedTypeVariables #-}
module PartialArgs where

import Language.SMTLib2
import Language.SMTLib2.Internals

import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable
import Data.Typeable

class LiftArgs a => PartialArgs a where
  type PartialValue a
  maskValue :: a -> PartialValue a -> [Bool] -> (PartialValue a,[Bool])
  unmaskValue :: a -> Unpacked a -> PartialValue a
  assignPartial :: a -> PartialValue a -> [SMTExpr Bool]

instance SMTValue t => PartialArgs (SMTExpr t) where
  type PartialValue (SMTExpr t) = Maybe t
  maskValue _ val (x:xs) = (if x
                            then val
                            else Nothing,xs)
  unmaskValue _ val = Just val
  assignPartial _ Nothing = []
  assignPartial expr (Just v) = [expr .==. (constantAnn v (extractAnnotation expr))]

instance (PartialArgs a1,PartialArgs a2) => PartialArgs (a1,a2) where
  type PartialValue (a1,a2) = (PartialValue a1,PartialValue a2)
  maskValue (_::(a1,a2)) (v1,v2) xs = let (r1,rest1) = maskValue (undefined::a1) v1 xs
                                          (r2,rest2) = maskValue (undefined::a2) v2 rest1
                                      in ((r1,r2),rest2)
  unmaskValue (_::(a1,a2)) (v1,v2) = (unmaskValue (undefined::a1) v1,
                                      unmaskValue (undefined::a2) v2)
  assignPartial (e1,e2) (v1,v2) = (assignPartial e1 v1)++
                                  (assignPartial e2 v2)

instance (PartialArgs a1,PartialArgs a2,PartialArgs a3)
         => PartialArgs (a1,a2,a3) where
  type PartialValue (a1,a2,a3) = (PartialValue a1,PartialValue a2,PartialValue a3)
  maskValue (_::(a1,a2,a3)) (v1,v2,v3) xs
    = let (r1,rest1) = maskValue (undefined::a1) v1 xs
          (r2,rest2) = maskValue (undefined::a2) v2 rest1
          (r3,rest3) = maskValue (undefined::a3) v3 rest2
      in ((r1,r2,r3),rest3)
  unmaskValue (_::(a1,a2,a3)) (v1,v2,v3)
    = (unmaskValue (undefined::a1) v1,
       unmaskValue (undefined::a2) v2,
       unmaskValue (undefined::a3) v3)
  assignPartial (e1,e2,e3) (v1,v2,v3)
    = (assignPartial e1 v1)++
      (assignPartial e2 v2)++
      (assignPartial e3 v3)

instance (PartialArgs a1,PartialArgs a2,PartialArgs a3,PartialArgs a4)
         => PartialArgs (a1,a2,a3,a4) where
  type PartialValue (a1,a2,a3,a4) = (PartialValue a1,PartialValue a2,PartialValue a3,PartialValue a4)
  maskValue (_::(a1,a2,a3,a4)) (v1,v2,v3,v4) xs
    = let (r1,rest1) = maskValue (undefined::a1) v1 xs
          (r2,rest2) = maskValue (undefined::a2) v2 rest1
          (r3,rest3) = maskValue (undefined::a3) v3 rest2
          (r4,rest4) = maskValue (undefined::a4) v4 rest3
      in ((r1,r2,r3,v4),rest4)
  unmaskValue (_::(a1,a2,a3,a4)) (v1,v2,v3,v4)
    = (unmaskValue (undefined::a1) v1,
       unmaskValue (undefined::a2) v2,
       unmaskValue (undefined::a3) v3,
       unmaskValue (undefined::a4) v4)
  assignPartial (e1,e2,e3,e4) (v1,v2,v3,v4)
    = (assignPartial e1 v1)++
      (assignPartial e2 v2)++
      (assignPartial e3 v3)++
      (assignPartial e4 v4)

instance (Typeable a,Ord a,Show a,PartialArgs b) => PartialArgs (Map a b) where
  type PartialValue (Map a b) = Map a (PartialValue b)
  maskValue (_::Map a b) mpPart mask
    = let (rmask,rmp) = mapAccumL
                        (\cmask pval -> let (pval',nmask) = maskValue (undefined::b) pval cmask
                                        in (nmask,pval')
                        ) mask mpPart
      in (rmp,rmask)
  unmaskValue (_::Map a b) mp = fmap (unmaskValue (undefined::b)) mp
  assignPartial mp mpPart = concat $ Map.elems $ Map.intersectionWith assignPartial mp mpPart
