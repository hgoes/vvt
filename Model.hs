{-# LANGUAGE FlexibleContexts #-}
module Model where

import Data.Unit
import Language.SMTLib2
import Language.SMTLib2.Internals (foldsExprsId)
import Data.Graph.Inductive as Gr
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (comparing)
import Data.Foldable
import Prelude hiding (foldl)

data Model inp st = Model { inpAnnotation :: ArgAnnotation inp
                          , stAnnotation :: ArgAnnotation st
                          , initState :: st -> SMTExpr Bool
                          , nextState :: st -> inp -> st -> SMTExpr Bool
                          , assertion :: st -> SMTExpr Bool }

data CFGNode inp st = CFGNode { nodeAssertion :: inp -> st -> SMTExpr Bool
                              , nodePhi :: Map Node (inp -> st -> st)
                              , nodeTransformation :: inp -> st -> st
                              }

data CFGEdge inp st = CondJump (inp -> st -> SMTExpr Bool)

data CFGModel inp st = CFGModel { cfgStAnnotation :: ArgAnnotation st
                                , cfgInpAnnotation :: ArgAnnotation inp
                                , cfgGraph :: Gr (CFGNode inp st) (CFGEdge inp st)
                                , cfgInit :: Node
                                }

addAssertion :: (st -> SMTExpr Bool) -> Model inp st -> Model inp st
addAssertion f mdl = mdl { assertion = \x -> (assertion mdl x) .&&. (f x) }

newState :: Args st => Model inp st -> SMT st
newState mdl = argVarsAnn (stAnnotation mdl)

newInput :: Args inp => Model inp st -> SMT inp
newInput mdl = argVarsAnn (inpAnnotation mdl)

bmc :: (Args inp,LiftArgs st) => Model inp st -> SMT [Unpacked st]
bmc mdl = do
  init <- newState mdl
  assert $ initState mdl init
  bmc' [] init
  where
    bmc' hist cur = do
      res <- stack $ do
        assert $ not' $ assertion mdl cur
        sat <- checkSat
        if sat
          then fmap Just $ mapM getValues (cur:hist)
          else return Nothing
      case res of
        Nothing -> do
          nxt <- newState mdl
          inp <- newInput mdl
          assert $ nextState mdl cur inp nxt
          bmc' (cur:hist) nxt
        Just res' -> return res'

mergeArgs :: Args a => [(a,SMTExpr Bool)] -> a
mergeArgs xs = res
  where
    (_,_,res) = foldsExprsId (\_ exprs anns -> ((),[ expr | (expr,_) <- exprs ],buildITE exprs))
                () xs (extractArgAnnotation $ fst $ head xs)
    buildITE [(e,_)] = e
    buildITE ((e,c):es) = ite c e (buildITE es)

treeBmc :: (LiftArgs inp,LiftArgs st) => CFGModel inp st
           -> (s -> [Node] -> (s,Node)) -> s
           -> SMT [(Node,Unpacked inp,Unpacked st)]
treeBmc mdl sel st = do
  inp <- argVarsAnn (cfgInpAnnotation mdl)
  init <- argVarsAnn (cfgStAnnotation mdl)
  let gr = Gr.mkGraph [(0,(cfgInit mdl,constant True,inp,init))] []
      queue = Map.singleton (cfgInit mdl) [(0,constant True)]
  treeBmc' st gr queue
  where
    --treeBmc' :: s -> Gr.Gr (Node,SMTExpr Bool,a) (SMTExpr Bool) -> Map Node [(Node,SMTExpr Bool)] -> SMT [(Node,Unpacked a)]
    treeBmc' st gr queue = do
      inp <- argVarsAnn (cfgInpAnnotation mdl)
      let (nst,nd) = sel st (Map.keys queue)
          (Just inc,nqueue) = Map.updateLookupWithKey (\_ _ -> Nothing) nd queue
          (Just ctx,_) = Gr.match nd (cfgGraph mdl)
          inc' = [ (nd_from,nd_cfg,arg_from,act_from,cond)
                 | (nd_from,cond) <- inc
                 , let Just (nd_cfg,act_from,inp_from,arg_from) = Gr.lab gr nd_from ]
          inc_args = mergeArgs [ (case Map.lookup nd_cfg (nodePhi $ Gr.lab' ctx) of
                                     Just app -> app inp arg_from
                                     Nothing -> arg_from,act_from .&&. cond)
                               | (_,nd_cfg,arg_from,act_from,cond) <- inc' ]
      act <- defConstNamed ("act"++show nd)
             (app or' [ act_from .&&. cond
                      | (_,_,_,act_from,cond) <- inc'])
      let curArgs = nodeTransformation (Gr.lab' ctx) inp inc_args
          [new_nd] = Gr.newNodes 1 gr
          ngr = foldl (\cgr (nd_from,_,_,_,cond)
                       -> Gr.insEdge (nd_from,new_nd,cond) cgr)
                (Gr.insNode (new_nd,(nd,act,inp,curArgs)) gr) inc'
      bug <- stack $ do
        assert $ act .&&. (not' $ nodeAssertion (Gr.lab' ctx) inp curArgs)
        sat <- checkSat
        if sat
          then fmap Just $ getTrace 0 ngr
          else return Nothing
      case bug of
        Just bug' -> return bug'
        Nothing -> treeBmc' nst ngr
                   (foldl (\cqueue (nd_succ,edge)
                           -> case edge of
                             CondJump c -> Map.insertWith (++) nd_succ
                                           [(new_nd,c inp curArgs)] cqueue
                          ) nqueue (Gr.lsuc' ctx))
    getTrace :: (LiftArgs inp,LiftArgs st)
                => Node -> Gr.Gr (Node,SMTExpr Bool,inp,st) (SMTExpr Bool)
                -> SMT [(Node,Unpacked inp,Unpacked st)]
    getTrace nd gr = do
      let (Just ctx,_) = Gr.match nd gr
          (nd_cfg,_,inp,cont) = Gr.lab' ctx
      vals <- getValues cont
      inp' <- getValues inp
      case Gr.lsuc' ctx of
        [] -> return [(nd_cfg,inp',vals)]
        xs -> do
          rest <- getTrace' xs gr
          return ((nd_cfg,inp',vals):rest)

    getTrace' :: (LiftArgs inp,LiftArgs st)
                 => [(Node,SMTExpr Bool)] -> Gr.Gr (Node,SMTExpr Bool,inp,st) (SMTExpr Bool)
                 -> SMT [(Node,Unpacked inp,Unpacked st)]
    getTrace' [] _ = error "No successor state is active"
    getTrace' ((nxt,cond):rest) gr = do
      vcond <- getValue cond
      if vcond
        then getTrace nxt gr
        else getTrace' rest gr

simpleSelector :: Map Node Integer -> [Node] -> (Map Node Integer,Node)
simpleSelector mp nds
  = let (minCount,selNd) = minimumBy (comparing fst) [ (Map.findWithDefault 0 nd mp,nd) | nd <- nds ]
    in (Map.insert selNd (minCount+1) mp,selNd)

stateSpace :: (Args inp,LiftArgs st,Ord (Unpacked st))
              => Model inp st -> SMT (Gr.Gr (Unpacked st) ())
stateSpace mdl = do
  st <- newState mdl
  st' <- newState mdl
  inits <- stack $ do
    assert $ initState mdl st
    getAll (stAnnotation mdl) st
  (gr',_) <- foldlM (\(gr,mp) val -> do
                        (ngr,nmp,_) <- explore gr mp st st' val
                        return (ngr,nmp)
                    ) (Gr.empty,Map.empty) inits
  return gr'
  where
    explore gr mp st st' val = case Map.lookup val mp of
      Just nd -> return (gr,mp,nd)
      Nothing -> do
        let [nd] = Gr.newNodes 1 gr
            ngr = Gr.insNode (nd,val) gr
            nmp = Map.insert val nd mp
        succs <- stack $ do
          inp <- newInput mdl
          assert $ argEq st (liftArgs val (stAnnotation mdl))
          assert $ nextState mdl st inp st'
          getAll (stAnnotation mdl) st'
        (ngr,nmp') <- foldlM (\(cgr,cmp) succ -> do
                                 (ngr,nmp,nd') <- explore cgr nmp st st' succ
                                 let ngr' = Gr.insEdge (nd,nd',()) ngr
                                 return (ngr',nmp)
                             ) (ngr,nmp) succs
        return (ngr,nmp',nd)
    getAll :: LiftArgs a => ArgAnnotation a -> a -> SMT [Unpacked a]
    getAll ann st = do
      res <- checkSat
      if res
        then (do
                 v <- getValues st
                 assert $ not' $ argEq st (liftArgs v ann)
                 vs <- getAll ann st
                 return (v:vs))
        else return []
