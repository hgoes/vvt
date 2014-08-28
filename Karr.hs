{-# LANGUAGE ScopedTypeVariables,GADTs #-}
module Karr where

import Affine
import Polynom
import ExprPreprocess
import Model

import Language.SMTLib2
import Language.SMTLib2.Internals

import Data.Vector as Vec
import Linear.Vector
import Linear.Matrix ((!*))
import Prelude as P hiding (all)

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Data.Maybe (catMaybes)
import Data.List as L

import Data.Graph.Inductive as Gr

import Debug.Trace

data DiagonalBasis = DiagBasis { basisVector :: !(Vector Integer)
                               , basisVectors :: !(IntMap (Vector Integer))
                               } deriving Show

data KarrState = KarrState { karrNodes :: IntMap DiagonalBasis
                           , karrTransition :: Int -> Int -> [(Vector (Vector Integer),Vector Integer)]
                           , karrSuccessor :: Int -> [Int]
                           , karrQueue :: [(Int,Vector Integer)]
                           }

instance Show KarrState where
  show st = show (karrNodes st,karrQueue st)

renderKarrTrans :: KarrState -> Gr () [(Vector (Vector Integer),Vector Integer)]
renderKarrTrans st = traceGraph [start] Set.empty Gr.empty
  where
    (start,_) = L.head (karrQueue st)
    traceGraph [] _ gr = gr
    traceGraph (n:ns) visited gr
      = if Set.member n visited
        then traceGraph ns visited gr
        else (let gr1 = insNode (n,()) gr
                  gr2 = traceGraph ((karrSuccessor st n) L.++ ns) (Set.insert n visited) gr1
              in L.foldl (\cgr v
                          -> insEdge (n,v,karrTransition st n v) cgr
                         ) gr2 (karrSuccessor st n))
{-
runKarr :: (Args inp,Args st) => CFGModel inp st -> IntMap [st -> SMTExpr Bool]
runKarr mdl = fmap (\diag -> fmap predicateVecToFun $ extractPredicateVec diag) $ karrNodes $ runKarr' (initKarrFromCFG mdl)
  where
    runKarr' st = if karrComplete st
                  then st
                  else runKarr' (stepKarr st)

runKarrDebug :: (Args inp,Args st) => CFGModel inp st -> IntMap [SMTExpr Bool]
runKarrDebug mdl = fmap (fmap (\fun -> fun st)) $ runKarr mdl
  where
    (k,st) = foldExprsId (\i _ ann -> (i+1,Var i ann)) 0 undefined (cfgStAnnotation mdl)

initKarrFromCFG :: (Args inp,Args st) => CFGModel inp st -> KarrState
initKarrFromCFG (mdl::CFGModel inp st)
  = initKarr numSts (cfgInit mdl)
    (\_ trg -> tmap IMap.! trg)
    (suc (cfgGraph mdl))
  where
    tmap = IMap.fromList [ (nd,getTransformMat
                               (cfgInpAnnotation mdl)
                               (cfgStAnnotation mdl)
                               (nodeTransformation node))
                         | (nd,node) <- labNodes (cfgGraph mdl) ]
    (numSts,_) = foldExprsId (\n e _ -> case cast e of
                                 Nothing -> (n,e)
                                 Just (_::SMTExpr Integer) -> (n+1,e)) 0 (undefined::st) (cfgStAnnotation mdl)
-}

finishKarr :: KarrState -> KarrState
finishKarr st = if karrComplete st
                then st
                else finishKarr (stepKarr st)

initKarr :: Int -- ^ The total number of states
         -> Int -- ^ The initial state
         -> (Int -> Int -> [(Vector (Vector Integer),Vector Integer)])
         -> (Int -> [Int])
         -> KarrState
initKarr numSt initSt trans succ
  = KarrState { karrNodes = IMap.singleton initSt
                            (DiagBasis { basisVector = Vec.replicate numSt 0
                                       , basisVectors = IMap.fromList
                                                        [ (i,Vec.generate numSt
                                                             (\i' -> if i==i'
                                                                     then 1
                                                                     else 0))
                                                        | i <- [0..(numSt-1)] ]
                                       })
              , karrTransition = trans
              , karrSuccessor = succ
              , karrQueue = [ (initSt,Vec.generate numSt (\i' -> if i==i'
                                                                 then 1
                                                                 else 0))
                            | i <- [0..(numSt-1)] ] }

stepKarr :: KarrState -> KarrState
stepKarr st = case karrQueue st of
  ((u,x):nqueue)
    -> let (nodes,queue) = L.foldl' (\(nds,q) v
                                     -> let trans = karrTransition st u v
                                            diag = IMap.lookup v nds
                                            (ndiag,nq) = L.foldl'
                                                         (\(diag',cq) (trans_A,trans_b)
                                                          -> let t = (trans_A !* x) ^+^ trans_b
                                                             in case diag' of
                                                               Nothing -> (Just $ initBasis t,(v,t):cq)
                                                               Just diag'' -> case updateBasis t diag'' of
                                                                 Nothing -> (Just diag'',cq)
                                                                 Just diag''' -> (Just diag''',(v,t):cq)
                                                         ) (diag,q) trans
                                        in (case ndiag of
                                               Nothing -> nds
                                               Just ndiag' -> IMap.insert v ndiag' nds,nq)
                                    ) (karrNodes st,nqueue) (karrSuccessor st u)
       in st { karrNodes = nodes
             , karrQueue = queue }

karrComplete :: KarrState -> Bool
karrComplete st = P.null (karrQueue st)

testTrans :: SMTExpr Bool -> (SMTExpr Integer,SMTExpr Integer) -> (SMTExpr Integer,SMTExpr Integer)
testTrans inp (x,y) = (ite inp (x+5) (x+y),2*(y+x))

{-
getTransformMat :: (Args inp,Args st) => ArgAnnotation inp -> ArgAnnotation st -> (inp -> st -> st) -> [(Vector (Vector Integer),Vector Integer)]
getTransformMat ann_inp ann_st f
  = [ (Vec.fromList $
       [ case aff of
            Nothing -> Vec.generate (fromIntegral k) (\i' -> if i'==(fromIntegral i) then 1 else 0)
            Just aff' -> Vec.generate (fromIntegral k) (\i' -> case Map.lookup (fromIntegral i') (affineFactors aff') of
                                                           Nothing -> 0
                                                           Just x -> x)
       | (i,aff) <- aff_exprs' ],
       Vec.fromList $
       [ case aff of
            Nothing -> 0
            Just aff' -> affineConstant aff'
       | (_,aff) <- aff_exprs' ])
    | aff_exprs' <- aff_exprs ]
  where
    {-(n,inp) = foldExprsId (\i e ann -> case cast e of
                              Nothing -> (i,InternalObj () ann)
                              Just (_::SMTExpr Integer) -> (i+1,Var i ann)) 0 undefined ann_inp-}
    (k,st) = foldExprsId (\i e ann -> case cast e of
                             Nothing -> (i,InternalObj () ann)
                             Just (_::SMTExpr Integer) -> (i+1,Var i ann)) 0 undefined ann_st
    sts = [ catMaybes [ cast expr | UntypedExpr expr <- fromArgs arg ]
          | x <- removeInputs ann_inp ann_st f st
          , (conds,arg) <- removeArgGuards x ]
    aff_exprs = [ [ (i,affineFromExpr (expr::SMTExpr Integer))
                  | (i,expr) <- P.zip [0..(k-1)] st' ]
                | st' <- sts ]-}

initBasis :: Vector Integer -> DiagonalBasis
initBasis vec = DiagBasis { basisVector = vec
                          , basisVectors = IMap.empty }

updateBasis :: Vector Integer -> DiagonalBasis -> Maybe DiagonalBasis
updateBasis t basis
  = case Vec.findIndex (/=0) t' of
    Nothing -> Nothing
    Just ni -> Just (basis { basisVectors = IMap.insert ni t' $
                                            fmap (\xi -> if xi!ni == 0
                                                         then xi
                                                         else (let p = lcm (t' ! ni) (xi!ni)
                                                                   xi' = xi ^* (p `div` (xi!ni))
                                                                   t'' = t' ^* (p `div` (t' ! ni))
                                                               in xi' ^-^ t'')
                                                 ) (basisVectors basis)
                           })
  where
    t' = reduceVec (t ^-^ (basisVector basis)) (IMap.toList $ basisVectors basis)
    
    reduceVec x [] = x
    reduceVec x ((i,xi):xs)
      | x!i == 0 = reduceVec x xs
      | otherwise = let p = lcm (x!i) (xi!i)
                        xi' = xi ^* (p `div` (xi!i))
                        x' = x ^* (p `div` (x!i))
                        rx = x' ^-^ xi'
                    in reduceVec rx xs

extractPredicateVec :: DiagonalBasis -> [Vector Integer]
extractPredicateVec diag
  = [ Vec.generate ((Vec.length nbase)+1)
      (\i' -> if i'==0
              then -v
              else (if i'==(i+1)
                    then -f
                    else (case IMap.lookup (i'-1) ndiag of
                             Nothing -> 0
                             Just v' -> v' ! i)))
    | (i,v) <- P.zip [0..] (Vec.toList nbase)
    , IMap.notMember i ndiag ]
  where
    (f,nbase) = IMap.foldlWithKey (\(cf,cbase) i vec
                                   -> if (cbase!i)==0
                                      then (cf,cbase)
                                      else let m = lcm (cbase!i) (vec!i)
                                               base0 = cbase ^* (m `div` (cbase!i))
                                               base1 = vec ^* (m `div` (vec!i))
                                               nf = lcm (m `div` (cbase!i)) cf
                                           in (nf,base0 ^-^ base1)
                                  ) (1,basisVector diag) (basisVectors diag)
    ndiag = IMap.mapWithKey (\i v -> fmap (\x -> (x*f) `div` (v!i)) v) (basisVectors diag)

predicateVecToFun :: (Args st) => Vector Integer -> st -> SMTExpr Bool
predicateVecToFun v st = (constant c) .==. (app plus $ catMaybes $ match (fromArgs st) facs)
  where
    c:facs = Vec.toList v
    match _ [] = []
    match ((UntypedExpr e):es) facs = case cast e of
      Nothing -> match es facs
      Just e' -> (case P.head facs of
                     0 -> Nothing
                     1 -> Just e'
                     -1 -> Just (app neg e')
                     f -> Just $ (constant f)*e'):(match es (P.tail facs))

testExpr :: SMTExpr Integer
testExpr = 2*((Var 0 ()) + (constant 4)) + (Var 1 ()) + (Var 0 ())*(Var 0 ())
