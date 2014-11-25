{-# LANGUAGE ScopedTypeVariables,GADTs #-}
module Karr where

import Data.Vector (Vector,(//),(!))
import qualified Data.Vector as Vec
import Linear.Vector
import Linear.Matrix ((!*))
import Prelude as P hiding (all)

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IMap
import qualified Data.Set as Set
import Data.List as L

import Data.Graph.Inductive as Gr

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

finishKarr :: KarrState -> KarrState
finishKarr st = if karrComplete st
                then st
                else finishKarr (stepKarr st)

initKarr :: Int -- ^ The number of variables
         -> Int -- ^ The initial state
         -> (Int -> Int -> [(Vector (Vector Integer),Vector Integer)])
         -> (Int -> [Int])
         -> KarrState
initKarr numVar initSt trans succ
  = KarrState { karrNodes = IMap.singleton initSt
                            (DiagBasis { basisVector = Vec.replicate numVar 0
                                       , basisVectors = IMap.fromList
                                                        [ (i,Vec.generate numVar
                                                             (\i' -> if i==i'
                                                                     then 1
                                                                     else 0))
                                                        | i <- [0..(numVar-1)] ]
                                       })
              , karrTransition = trans
              , karrSuccessor = succ
              , karrQueue = (initSt,Vec.generate numVar (const 0))
                            :[ (initSt,Vec.generate numVar (\i' -> if i==i'
                                                                   then 1
                                                                   else 0))
                             | i <- [0..(numVar-1)] ] }

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

extractPredicateVec :: DiagonalBasis -> [(Vector Integer,Integer)]
extractPredicateVec diag
  = [ (Vec.slice (numBasis+1) numVars line,line!numBasis)
    | line <- Vec.toList solved
    , Vec.all (==0) $ Vec.slice 0 numBasis line]
  where
    nbasis = IMap.fromList $ zip [0..] $ IMap.elems (basisVectors diag)
    numBasis = IMap.size nbasis
    numVars = Vec.length (basisVector diag)
    system = Vec.generate numVars
             (\i -> Vec.generate (numBasis+1+numVars)
                    (\j -> if j < numBasis
                           then (nbasis IMap.! j)!i
                           else if j==numBasis
                                then (basisVector diag)!i
                                else if i==j-numBasis-1
                                     then 1
                                     else 0))
    solved = gaussElim system

testKarr1 :: [(Int,(Vector Integer,Integer))]
testKarr1 = [ (n,vec)
            | (n,basis) <- IMap.toList (karrNodes st')
            , vec <- extractPredicateVec basis ]
  where
    st = initKarr 2 0
         (\f t -> case (f,t) of
                        (0,1) -> [(Vec.fromList [Vec.fromList [0,0]
                                                ,Vec.fromList [0,0]],
                                   Vec.fromList [0,0])]
                        (1,2) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [0,0])]
                        (1,3) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [0,0])]
                        (2,1) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [4,1])]
                        (3,4) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [0,0])]
                        (4,3) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [-4,-1])]
                        (3,5) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [0,0])]
                        (5,5) -> [(Vec.fromList [Vec.fromList [1,0]
                                                ,Vec.fromList [0,1]],
                                   Vec.fromList [0,0])])
         (\f -> case f of
           0 -> [1]
           1 -> [2,3]
           2 -> [1]
           3 -> [4,5]
           4 -> [3]
           5 -> [5])
    st' = finishKarr st

gaussElim :: Integral a => Vector (Vector a) -> Vector (Vector a)
gaussElim mat = foldl (\mat i -> elim i mat
                      ) mat [0..Vec.length mat-1]
  where
    elim n mat = case switchZero n mat of
      Nothing -> mat
      Just nmat -> foldl (\mat i -> if i==n
                                    then mat
                                    else mkZero n i mat
                         ) nmat [0..Vec.length mat-1]
    switchZero n mat = if mat!n!n==0
                       then case Vec.findIndex (\ln -> ln!n/=0) mat of
                             Just nonNullIdx -> Just $ mat//[(n,mat!nonNullIdx)
                                                            ,(nonNullIdx,mat!n)]
                             Nothing -> Nothing
                       else Just mat
    mkZero n m mat = let elN = mat!n!n
                         elM = mat!m!n
                         f = lcm elN elM
                     in if elM==0
                        then mat
                        else mat//[(m,mat!m^*(f `div` elM) ^-^ mat!n^*(f `div` elN))]
