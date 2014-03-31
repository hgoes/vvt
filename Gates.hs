{-# LANGUAGE ExistentialQuantification,GeneralizedNewtypeDeriving,
             DeriveDataTypeable,ScopedTypeVariables #-}
module Gates where

import Language.SMTLib2
import Language.SMTLib2.Internals

import Data.Typeable
import Data.Array
import Data.Map (Map)
import qualified Data.Map as Map

newtype GateExpr = GateExpr Int deriving (Typeable,Eq,Ord,Show,Ix)

type GateArray inp outp = Map GateExpr (Gate inp outp)

data AnyGateArray inp = forall outp. SMTType outp => AnyGateArray (GateArray inp outp)

type GateMap inp = Map TypeRep (Int,AnyGateArray inp)

data Gate inp outp = Gate { gateTransfer :: inp -> SMTExpr outp
                          , gateAnnotation :: SMTAnnotation outp
                          , gateName :: Maybe String
                          }
                   deriving Typeable

addGate :: (Args inp,SMTType outp) => GateMap inp -> Gate inp outp -> (SMTExpr outp,GateMap inp)
addGate mp gate = let (expr,nmp) = addGate' mp gate
                  in (InternalObj expr (gateAnnotation gate),nmp)

addGate' :: (Args inp,SMTType outp) => GateMap inp -> Gate inp outp -> (GateExpr,GateMap inp)
addGate' mp (gate::Gate inp outp)
  = let tprep = typeOf (undefined::outp)
    in case Map.lookup tprep mp of
      Just (nidx,AnyGateArray arr) -> case cast arr of
        Just arr' -> (GateExpr nidx,Map.insert tprep (nidx+1,AnyGateArray (Map.insert (GateExpr nidx) gate arr')) mp)
      Nothing -> (GateExpr 0,Map.insert tprep (1,AnyGateArray (Map.singleton (GateExpr 0) gate)) mp)

modifyGate :: (Args inp,SMTType outp) => GateExpr -> GateMap inp -> (Gate inp outp -> Gate inp outp) -> GateMap inp
modifyGate idx mp (f::Gate inp outp -> Gate inp outp)
  = let tp = typeOf (undefined::outp)
    in Map.adjust (\(nxt,AnyGateArray arr) -> case cast arr of
                      Just arr' -> (nxt,AnyGateArray $ Map.adjust f idx arr')) tp mp

getGate :: (Args inp,SMTType outp) => GateExpr -> GateMap inp -> Gate inp outp
getGate idx mp = withUndef $
                 \u -> let tprep = typeOf u
                       in case Map.lookup tprep mp of
                         Just (_,AnyGateArray gates) -> case Map.lookup idx gates of
                           Just res -> case cast res of
                             Just res' -> res'
                           Nothing -> error $ "Gate "++show idx++" not found in "++show tprep++" "++show (Map.keys gates)
                         Nothing -> error $ "No gates for "++show tprep++" found."
  where
    withUndef :: (outp -> Gate inp outp) -> Gate inp outp
    withUndef f = f undefined

emptyGateMap :: GateMap inp
emptyGateMap = Map.empty

translateGateExpr :: (Args inp,SMTType a) => SMTExpr a -> GateMap inp -> inp -> SMTExpr a
translateGateExpr e mp inp = snd $ foldExpr (\_ e' -> ((),translateGateExpr' e' mp inp)
                                            ) () e

translateGateExpr' :: Args inp => SMTExpr a -> GateMap inp -> inp -> SMTExpr a
translateGateExpr' e@(InternalObj obj ann) mp inp = case cast obj of
  Just gexpr -> translateGateExpr (gateTransfer (getGate gexpr mp) inp) mp inp
  Nothing -> e
translateGateExpr' e _ _ = e

type RealizedGates = Map TypeRep (Map GateExpr UntypedExpr)

declareGate :: (Args inp,SMTType a,Monad m) => SMTExpr a -> RealizedGates -> GateMap inp -> inp -> SMT' m (SMTExpr a,RealizedGates)
declareGate e real mp inp = do
  (nreal,[res]) <- foldExprM (\creal e -> do
                                 (res,nreal) <- declareGate' e creal mp inp
                                 return (nreal,[res])
                             ) real e
  return (res,nreal)

declareGate' :: (Args inp,Monad m) => SMTExpr a -> RealizedGates -> GateMap inp -> inp -> SMT' m (SMTExpr a,RealizedGates)
declareGate' e@(InternalObj obj ann::SMTExpr a) real mp inp = case cast obj of
  Just gexpr -> case Map.lookup (typeOf (undefined::a)) real of
    Just exprs -> case Map.lookup gexpr exprs of
      Just decl -> return (castUntypedExpr decl,real)
      Nothing -> createGate gexpr
    Nothing -> createGate gexpr
  Nothing -> return (e,real)
  where
    createGate gexpr = do
      let gate = getGate gexpr mp
      (r,nreal) <- declareGate (gateTransfer gate inp) real mp inp
      res <- case gateName gate of
        Nothing -> defConst r
        Just name -> defConstNamed name r
      return (res,Map.insertWith Map.union (typeOf (undefined::a)) (Map.singleton gexpr (UntypedExpr res)) nreal)
declareGate' e real _ _ = return (e,real)

test :: (SMTExpr Integer,SMTExpr Integer,SMTExpr Bool) -> SMTExpr Integer
test = translateGateExpr e3 mp3
  where
    g1 = Gate (\(x,y,_) -> x+y) () Nothing
    g2 = Gate (\(x,y,_) -> x-y) () Nothing
    (e1,mp1) = addGate Map.empty g1
    (e2,mp2) = addGate mp1 g2
    g3 = Gate (\(_,_,c) -> ite c e1 e2) () Nothing
    (e3,mp3) = addGate mp2 g3
