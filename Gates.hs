{-# LANGUAGE ExistentialQuantification,GeneralizedNewtypeDeriving,
             DeriveDataTypeable,ScopedTypeVariables,GADTs #-}
module Gates where

import Language.SMTLib2
import Language.SMTLib2.Internals

import Data.Typeable
import Data.Array
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldlM)
import qualified Data.Graph.Inductive as Gr

newtype GateExpr = GateExpr Int deriving (Typeable,Eq,Ord,Show,Ix)

type GateArray inp outp = Map GateExpr (Gate inp outp)

data AnyGateArray inp = forall outp. SMTType outp => AnyGateArray (GateArray inp outp)

type GateMap inp = Map TypeRep (Int,AnyGateArray inp)

data Gate inp outp = Gate { gateTransfer :: inp -> SMTExpr outp
                          , gateAnnotation :: SMTAnnotation outp
                          , gateName :: Maybe String
                          }
                   deriving Typeable

type RealizedGates = Map TypeRep (Map GateExpr (SMTExpr Untyped))

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

translateGateExpr :: (Args inp,SMTType a) => SMTExpr a -> GateMap inp -> RealizedGates -> inp -> SMTExpr a
translateGateExpr e mp real inp
  = snd $ foldExpr (\_ e' -> ((),translateGateExpr' e' mp real inp)
                   ) () e

translateGateExpr' :: Args inp => SMTExpr a -> GateMap inp -> RealizedGates -> inp -> SMTExpr a
translateGateExpr' e@(InternalObj obj ann::SMTExpr a) mp realized inp = case cast obj of
  Just gexpr -> case (do
                         exprs <- Map.lookup (typeOf (undefined::a)) realized
                         Map.lookup gexpr exprs) of
    Just decl -> castUntypedExpr decl
    Nothing -> translateGateExpr (gateTransfer (getGate gexpr mp) inp) mp realized inp
  Nothing -> e
translateGateExpr' e _ _ _ = e

declareGate :: (Args inp,SMTType a,Monad m) => SMTExpr a -> RealizedGates -> GateMap inp -> inp -> SMT' m (SMTExpr a,RealizedGates)
declareGate e real mp inp = do
  --trace ("declare gate "++show e) (return ())
  (nreal,[res]) <- foldExprM (\creal e -> do
                                 (res,nreal) <- declareGate' e creal mp inp
                                 return (nreal,[res])
                             ) real e
  --trace "...done" (return ())
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
      --trace ("creating gate "++show (gateName gate)) (return ())
      (r,nreal) <- declareGate (gateTransfer gate inp) real mp inp
      res <- case gateName gate of
        Nothing -> defConst r
        Just name -> defConstNamed name r
      return (res,Map.insertWith Map.union (typeOf (undefined::a)) (Map.singleton gexpr (UntypedExpr res)) nreal)
declareGate' e real _ _ = return (e,real)

declareAllGates :: (Args inp,Monad m) => RealizedGates -> GateMap inp -> inp
                   -> SMT' m RealizedGates
declareAllGates realized gates inp
  = foldlM (\realized (_,AnyGateArray arr)
             -> foldlM (\realized gate
                        -> do
                          (_,nrealized) <- declareGate (gateTransfer gate inp) realized gates inp
                          return nrealized
                       ) realized arr
           ) realized gates

test :: (SMTExpr Integer,SMTExpr Integer,SMTExpr Bool) -> SMTExpr Integer
test = translateGateExpr e3 mp3 Map.empty
  where
    g1 = Gate (\(x,y,_) -> x+y) () Nothing
    g2 = Gate (\(x,y,_) -> x-y) () Nothing
    (e1,mp1) = addGate Map.empty g1
    (e2,mp2) = addGate mp1 g2
    g3 = Gate (\(_,_,c) -> ite c e1 e2) () Nothing
    (e3,mp3) = addGate mp2 g3

data GateId = GateName String
            | GateNr TypeRep GateExpr

instance Show GateId where
  show (GateName n) = n
  show (GateNr tp i) = show (tp,i)

debugGates :: inp -> GateMap inp -> Gr.Gr (TypeRep,GateExpr,String,SMTExpr Untyped) ()
debugGates inp gates
  = Gr.mkGraph [ (nd,(tp,i,n,e))
               | (nd,(tp,i,Just n,e)) <- allGates ]
    edges
  where
    allGates = zip [0..]
               [ (tp,i,gateName gate,UntypedExpr (gateTransfer gate inp))
               | (tp,(no,AnyGateArray arr)) <- Map.toList gates
               , (i,gate) <- Map.toList arr ]
    gateMp = Map.fromList
             [ ((tp,i),nd) | (nd,(tp,i,_,_)) <- allGates ]
    edges = [ (nd,ndDep,())
            | (nd,(tp,i,_,UntypedExpr expr)) <- allGates
            , ndDep <- gateDeps expr ]
    gateDeps :: SMTType a => SMTExpr a -> [Gr.Node]
    gateDeps expr = fst $ foldExpr exprDeps [] expr
    exprDeps :: [Gr.Node] -> SMTExpr a -> ([Gr.Node],SMTExpr a)
    exprDeps deps e@(InternalObj obj ann :: SMTExpr a) = case cast obj of
      Just i -> ((gateMp Map.! (typeOf (undefined::a),i)):deps,e)
      Nothing -> (deps,e)
    exprDeps deps e = (deps,e)

{-
debugGates :: inp -> GateMap inp -> Gr.Gr GateId ()
debugGates inp gates
  = Gr.mkGraph [ (nd,case name of
                     Nothing -> GateNr tp i
                     Just n -> GateName n)
               | (nd,(tp,i,name,_)) <- allGates ]
    edges
  where
    allGates = zip [0..]
               [ (tp,i,gateName gate,UntypedExpr (gateTransfer gate inp))
               | (tp,(no,AnyGateArray arr)) <- Map.toList gates
               , (i,gate) <- Map.toList arr ]
    gateMp = Map.fromList
             [ ((tp,i),nd) | (nd,(tp,i,_,_)) <- allGates ]
    edges = [ (nd,ndDep,())
            | (nd,(tp,i,_,UntypedExpr expr)) <- allGates
            , ndDep <- gateDeps expr ]
    gateDeps :: SMTType a => SMTExpr a -> [Gr.Node]
    gateDeps expr = fst $ foldExpr exprDeps [] expr
    exprDeps :: [Gr.Node] -> SMTExpr a -> ([Gr.Node],SMTExpr a)
    exprDeps deps e@(InternalObj obj ann :: SMTExpr a) = case cast obj of
      Just i -> ((gateMp Map.! (typeOf (undefined::a),i)):deps,e)
      Nothing -> (deps,e)
    exprDeps deps e = (deps,e)-}
