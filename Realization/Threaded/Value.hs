{-# LANGUAGE DeriveDataTypeable,TypeFamilies #-}
module Realization.Threaded.Value where

import Gates

import Language.SMTLib2
import Language.SMTLib2.Internals
import Data.Map (Map)
import qualified Data.Map as Map
import LLVM.FFI
import Foreign.Ptr (Ptr)
import Data.Typeable
import Data.List (mapAccumL)

data SymVal = ValBool { valBool :: SMTExpr Bool }
            | ValInt { valInt :: SMTExpr Integer }
            | ValPtr { valPtr :: Map MemoryLoc (SMTExpr Bool) }
            | ValThreadId { valThreadId :: Map (Ptr CallInst) (SMTExpr Bool) }
            | ValStruct { valStruct :: [SymVal] }
            deriving (Eq,Ord,Show,Typeable)

data SymType = TpBool
             | TpInt
             | TpPtr { tpPtr :: Map MemoryLoc () }
             | TpThreadId { tpThreadId :: Map (Ptr CallInst) () }
             | TpStruct { tpStruct :: [SymType] }
             deriving (Eq,Ord,Show,Typeable)

type MemoryLoc = Either (Ptr AllocaInst) (Ptr GlobalVariable)

sameType :: SymType -> SymType -> Bool
sameType TpBool TpBool = True
sameType TpInt TpInt = True
sameType (TpPtr _) (TpPtr _) = True
sameType (TpThreadId _) (TpThreadId _) = True
sameType (TpStruct s1) (TpStruct s2) = sameTypes s1 s2
  where
    sameTypes [] [] = True
    sameTypes (x:xs) (y:ys) = sameType x y && sameTypes xs ys
    sameTypes _ _ = False
sameType _ _ = False

symITE :: SMTExpr Bool -> SymVal -> SymVal -> SymVal
symITE cond (ValBool x) (ValBool y) = ValBool (ite cond x y)
symITE cond (ValInt x) (ValInt y) = ValInt (ite cond x y)
symITE cond (ValPtr x) (ValPtr y)
  = ValPtr (Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
            (fmap (.&&. cond)) (fmap (.&&. (not' cond))) x y)
symITE cond (ValThreadId x) (ValThreadId y)
  = ValThreadId (Map.mergeWithKey (\_ p q -> Just $ ite cond p q)
                 (fmap (.&&. cond)) (fmap (.&&. (not' cond))) x y)
symITE cond (ValStruct s1) (ValStruct s2)
  = ValStruct $ zipWith (symITE cond) s1 s2

symITEs :: [(SMTExpr Bool,SymVal)] -> SymVal
symITEs [(_,val)] = val
symITEs ((c,val):rest) = symITE c val rval
  where
    rval = symITEs rest

addSymGate :: Args inp => GateMap inp -> SymType -> (inp -> SymVal) -> Maybe String
              -> (SymVal,GateMap inp)
addSymGate gts TpBool f name
  = let (expr,ngts) = addGate gts (Gate { gateTransfer = valBool.f
                                        , gateAnnotation = ()
                                        , gateName = name })
    in (ValBool expr,ngts)
addSymGate gts TpInt f name
  = let (expr,ngts) = addGate gts (Gate { gateTransfer = valInt.f
                                        , gateAnnotation = ()
                                        , gateName = name })
    in (ValInt expr,ngts)
addSymGate gts (TpPtr trgs) f name
  = let (ngts,trgExprs) = Map.mapAccumWithKey
                          (\gts loc _ -> let gt = Gate { gateTransfer = (Map.! loc).valPtr.f
                                                       , gateAnnotation = ()
                                                       , gateName = name }
                                             (cond,ngts) = addGate gts gt
                                         in (ngts,cond)
                          ) gts trgs
    in (ValPtr trgExprs,ngts)
addSymGate gts (TpThreadId trgs) f name
  = let (ngts,trgExprs) = Map.mapAccumWithKey
                          (\gts th _ -> let gt = Gate { gateTransfer = (Map.! th).valThreadId.f
                                                      , gateAnnotation = ()
                                                      , gateName = name }
                                            (cond,ngts) = addGate gts gt
                                        in (ngts,cond)
                          ) gts trgs
    in (ValThreadId trgExprs,ngts)
addSymGate gts (TpStruct tps) f name
  = (ValStruct ns,ngts)
  where
    ((ngts,_),ns) = mapAccumL (\(gts,n) tp
                               -> let (val,ngts) = addSymGate gts tp (\inp -> (valStruct (f inp))!!n) name
                                  in ((ngts,n+1),val)
                              ) (gts,0) tps

instance Args SymVal where
  type ArgAnnotation SymVal = SymType
  foldExprs f s ~(ValBool e) TpBool = do
    (s',e') <- f s e ()
    return (s',ValBool e')
  foldExprs f s ~(ValInt e) TpInt = do
    (s',e') <- f s e ()
    return (s',ValInt e')
  foldExprs f s ~(ValPtr conds) (TpPtr ptrs) = do
    (s',conds') <- foldExprs f s conds ptrs
    return (s',ValPtr conds')
  foldExprs f s ~(ValThreadId conds) (TpThreadId ths) = do
    (s',conds') <- foldExprs f s conds ths
    return (s',ValThreadId conds')
  foldExprs f s ~(ValStruct vals) (TpStruct tps) = do
    (s',vals') <- foldExprs f s vals tps
    return (s',ValStruct vals')
  foldsExprs f s lst TpBool = do
    let lst' = fmap (\(x,y) -> (valBool x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ()
    return (ns,fmap ValBool rlst,ValBool res)
  foldsExprs f s lst TpInt = do
    let lst' = fmap (\(x,y) -> (valInt x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ()
    return (ns,fmap ValInt rlst,ValInt res)
  foldsExprs f s lst (TpPtr conds) = do
    let lst' = fmap (\(x,y) -> (valPtr x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' conds
    return (ns,fmap ValPtr rlst,ValPtr res)
  foldsExprs f s lst (TpThreadId ths) = do
    let lst' = fmap (\(x,y) -> (valThreadId x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' ths
    return (ns,fmap ValThreadId rlst,ValThreadId res)
  foldsExprs f s lst (TpStruct tps) = do
    let lst' = fmap (\(x,y) -> (valStruct x,y)) lst
    (ns,rlst,res) <- foldsExprs f s lst' tps
    return (ns,fmap ValStruct rlst,ValStruct res)
  extractArgAnnotation (ValBool _) = TpBool
  extractArgAnnotation (ValInt _) = TpInt
  extractArgAnnotation (ValPtr conds) = TpPtr (fmap (const ()) conds)
  extractArgAnnotation (ValThreadId conds) = TpThreadId (fmap (const ()) conds)
  extractArgAnnotation (ValStruct vals) = TpStruct $ fmap extractArgAnnotation vals
  toArgs TpBool es = case es of
    [] -> Nothing
    e:es -> do
      e' <- entype cast e
      return (ValBool e',es)
  toArgs TpInt es = case es of
    [] -> Nothing
    e:es -> do
      e' <- entype cast e
      return (ValInt e',es)
  toArgs (TpPtr trgs) es = do
    (conds,rest) <- toArgs trgs es
    return (ValPtr conds,rest)
  toArgs (TpThreadId ths) es = do
    (conds,rest) <- toArgs ths es
    return (ValThreadId conds,rest)
  toArgs (TpStruct tps) es = do
    (vals,rest) <- toArgs tps es
    return (ValStruct vals,rest)
  getTypes _ TpBool = [ProxyArg (undefined::Bool) ()]
  getTypes _ TpInt = [ProxyArg (undefined::Integer) ()]
  getTypes _ (TpPtr trgs) = getTypes (undefined::Map (Either (Ptr AllocaInst) (Ptr GlobalVariable)) (SMTExpr Bool)) trgs
  getTypes _ (TpThreadId ths) = getTypes (undefined::Map (Ptr CallInst) (SMTExpr Bool)) ths
  getTypes u (TpStruct tps) = concat $ fmap (getTypes u) tps
  fromArgs (ValBool e) = [UntypedExpr e]
  fromArgs (ValInt e) = [UntypedExpr e]
  fromArgs (ValPtr conds) = fromArgs conds
  fromArgs (ValThreadId conds) = fromArgs conds
  fromArgs (ValStruct vals) = fromArgs vals
