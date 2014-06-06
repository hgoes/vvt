{-# LANGUAGE ExistentialQuantification,FlexibleContexts,RankNTypes,
             ScopedTypeVariables,PackageImports,GADTs #-}
module CTIGAR where

--import Model
import Realization
import Domain
import Translate
import State
import SMTPool

import Language.SMTLib2
import Language.SMTLib2.Connection
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

import Data.IORef
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (when)
import "mtl" Control.Monad.Trans (liftIO)
import Data.List (sort)
import Data.PQueue.Min
import Data.Graph.Inductive (Node)
import Data.Foldable
import Prelude hiding (sequence_,concat,mapM_)
import Data.Typeable

data Frame st = Frame { frameFrontier :: Set (AbstractState st)
                      , frameActivation :: SMTExpr Bool
                      }

data IC3Env inp st
  = IC3Env { ic3Model :: Model inp st
           , ic3Domain :: Domain st
           , ic3InitialProperty :: Node
           , ic3Consecution :: Consecution inp st
           , ic3Lifting :: SMTPool (st,inp,st)
           , ic3Initiation :: SMTPool st
           , ic3Interpolation :: SMTPool (st,inp,st)
           , ic3Frames :: [Frame st]
           }

data Consecution inp st = forall b. SMTBackend b IO =>
                          Consecution { consSolver :: SMTConnection b
                                      , consVars :: st
                                      , consInp :: inp
                                      , consVarsPrimed :: st
                                      }

data Obligation inp st = Obligation { oblState :: IORef (State inp st)
                                    , oblLevel :: Int
                                    , oblDepth :: Int
                                    } deriving Eq

instance Ord (Obligation inp st) where
  compare o1 o2 = case compare (oblLevel o1) (oblLevel o2) of
    EQ -> compare (oblDepth o1) (oblDepth o2)
    r -> r

type Queue inp st = MinQueue (Obligation inp st)

splitLast :: [a] -> ([a],a)
splitLast [x] = ([],x)
splitLast (x:xs) = let (rest,last) = splitLast xs
                   in (x:rest,last)

consecutionPerform :: Consecution inp st -> SMT a -> IO a
consecutionPerform (Consecution { consSolver = conn }) act
  = performSMT conn act

consecutionNew :: (SMTBackend b IO,Args inp,Args st)
                  => IO b -> Model inp st -> IO (Consecution inp st)
consecutionNew backend mdl = do
  consBackend <- backend
  consConn <- open consBackend
  (consSt,consInp,consSt') <- performSMT consConn $ do
    v <- argVarsAnn (stAnnotation mdl)
    inp <- argVarsAnn (inpAnnotation mdl)
    v' <- argVarsAnn (stAnnotation mdl)
    assert $ nextState mdl v inp v'
    assert $ assertion mdl v
    return (v,inp,v')
  return $ Consecution consConn consSt consInp consSt'

ic3Env :: (SMTBackend b IO,Args st,Args inp)
          => IO b -> Model inp st -> IO (IC3Env inp st)
ic3Env backend mdl = do
  cons <- consecutionNew backend mdl
  lifting <- createSMTPool backend $ do
    v <- argVarsAnn (stAnnotation mdl)
    inp <- argVarsAnn (inpAnnotation mdl)
    v' <- argVarsAnn (stAnnotation mdl)
    return (v,inp,v')
  initiation <- createSMTPool backend $ do
    v <- argVarsAnn (stAnnotation mdl)
    return v
  interpolation <- createSMTPool backend $ do
    v <- argVarsAnn (stAnnotation mdl)
    inp <- argVarsAnn (inpAnnotation mdl)
    v' <- argVarsAnn (stAnnotation mdl)
    return (v,inp,v')
  domainPool <- createSMTPool backend $ argVarsAnn (stAnnotation mdl)
  let dom = initialDomain domainPool
  (initNode,dom') <- domainAdd (initState mdl) dom
  return $ IC3Env { ic3Model = mdl
                  , ic3Consecution = cons
                  , ic3Lifting = lifting
                  , ic3Initiation = initiation
                  , ic3Interpolation = interpolation
                  , ic3Domain = dom'
                  , ic3InitialProperty = initNode
                  , ic3Frames = [] }
  
newFrame :: IC3Env inp st -> Bool -> IO (Frame st)
newFrame env init = consecutionPerform (ic3Consecution env) $ do
  act <- var
  if init
    then assert $ act .=>. (initState (ic3Model env) (consVars $ ic3Consecution env))
    else return ()
  return (Frame { frameFrontier = Set.empty
                , frameActivation = act })

{-
strengthenFrontier :: IC3Config inp st -> Consecution inp st -> Lifting inp st -> Frame -> IO Bool
strengthenFrontier cfg cons lift frame = do
  consecutionPerform cons $ stack $ do
    assert $ not' $ assertion (ic3Model cfg) $ frameVarsPrimed frame
    errorReachable <- checkSat
    if errorReachable
      then (do
               st <- extractState (ic3Model cfg) cons Nothing True lift
               
               else return True
-}
extractState :: (PartialArgs st,LiftArgs inp)
                => IC3Env inp st
                -> Maybe (IORef (State inp st))
                -> Bool
                -> IO (IORef (State inp st))
extractState env succ doLift = do
  let cons = ic3Consecution env
  vars <- liftIO $ consecutionPerform cons $ getValues (consVars cons)
  inp <- liftIO $ consecutionPerform cons $ getValues (consInp cons)
  state <- if doLift
           then (do
                    nxt <- case succ of
                      Nothing -> return (\st -> not' (assertion (ic3Model env) st))
                      Just succ' -> do
                        succ'' <- readIORef succ'
                        return (\st -> argEq st (liftArgs (stateFull succ'')
                                                 (extractArgAnnotation st)))
                    part <- withSMTPool (ic3Lifting env) $
                            \vars' -> liftState vars' (vars,inp,nxt)
                    return $ State { stateSuccessor = succ
                                   , stateLiftedAst = Nothing
                                   , stateFullAst = Nothing
                                   , stateFull = vars
                                   , stateInputs = inp
                                   , stateLifted = part
                                   , stateSpuriousLevel = 0
                                   , stateSpuriousSucc = False
                                   , stateNSpurious = 0
                                   , stateDomainHash = 0 })
           else return $ State { stateSuccessor = succ
                               , stateLiftedAst = Nothing
                               , stateFullAst = Nothing
                               , stateFull = vars
                               , stateInputs = inp
                               , stateLifted = unmaskValue (consVars cons) vars
                               , stateSpuriousLevel = 0
                               , stateSpuriousSucc = False
                               , stateNSpurious = 0
                               , stateDomainHash = 0 }
  newIORef state

liftState :: (PartialArgs st,LiftArgs inp) => (st,inp,st)
             -> (Unpacked st,Unpacked inp,st -> SMTExpr Bool)
             -> SMT (PartialValue st)
liftState vars@(cur::st,inp,nxt) vals@(vcur,vinp,vnxt) = do
  let ann_cur = extractArgAnnotation cur
      ann_inp = extractArgAnnotation inp
  (len_st,_,_) <- foldsExprs (\n [(arg1,_),(arg2,_)] _ -> do
                                 (eq,_) <- named ("st"++show n) (arg1 .==. arg2)
                                 assert eq
                                 return (n+1,[arg1,arg2],undefined)
                             ) 0 [(cur,()),(liftArgs vcur ann_cur,())] ann_cur
  assert $ argEq inp (liftArgs vinp ann_inp)
  assert $ not' $ vnxt nxt
  res <- checkSat
  when res $ error "The model appears to be non-deterministic."
  core <- getUnsatCore
  let part = toTruthValues len_st 0 (sort $ fmap (\('s':'t':num) -> read num) core)
      vcur' = unmaskValue (undefined::st) vcur
      (vcur'',[]) = maskValue (undefined::st) vcur' part
  return vcur''
  where
    toTruthValues len n []
      | n==len = []
      | otherwise = False:toTruthValues len (n+1) []
    toTruthValues len n (x:xs)
      = if n==x
        then True:toTruthValues len (n+1) xs
        else False:toTruthValues len (n+1) (x:xs)

-- | Check if the abstract state intersects with the initial condition
initiationTest :: IC3Env inp st -> AbstractState st -> IO Bool
initiationTest env state
  = fmap not $ withSMTPool (ic3Initiation env) $
    \vars -> stack $ do
      assert $ toDomainTerm state (ic3Domain env) vars
      checkSat

-- From LiftRef
updateAbstraction :: (LiftArgs st,LiftArgs inp)
                     => IC3Env inp st -> IORef (State inp st) -> IO ()
updateAbstraction env ref = do
  st <- readIORef ref
  case stateLiftedAst st of
    Just _ -> return ()
    Nothing
      -> if stateDomainHash st < domainHash (ic3Domain env)
         then return ()
         else do
           st' <- calculateLifting env st
           writeIORef ref st'

calculateLifting :: (LiftArgs inp,LiftArgs st)
                    => IC3Env inp st -> State inp st
                    -> IO (State inp st)
calculateLifting env state = do
  fullAbs <- domainAbstract
             (\vars -> argEq vars
                       (liftArgs (stateFull state) (extractArgAnnotation vars)))
             (ic3Domain env)
  liftedAbs <- case stateSuccessor state of
    Nothing -> lift env fullAbs (stateInputs state) Nothing
    Just succ -> do
      succ_state <- readIORef succ
      lift env fullAbs (stateInputs state) (Just $ bestAbstraction succ_state)
  return (state { stateFullAst = Just fullAbs
                , stateLiftedAst = liftedAbs })

lift :: (LiftArgs inp)
        => IC3Env inp st -> AbstractState st -> Unpacked inp
        -> Maybe (AbstractState st)
        -> IO (Maybe (AbstractState st))
lift env toLift inps succ = withSMTPool (ic3Lifting env) $ \(vars,inp,vars') -> stack $ do
  sequence_ $ Map.mapWithKey (\nd (expr,act) -> do
                                 (named_expr,_) <- named ("st"++show nd)
                                                   (if act
                                                    then expr
                                                    else not' expr)
                                 assert named_expr
                             ) (toDomainTerms toLift (ic3Domain env) vars)
  assert $ argEq inp (liftArgs inps (extractArgAnnotation inp))
  case succ of
    Nothing -> assert $ assertion (ic3Model env) vars'
    Just succ_abstr -> assert $ toDomainTerm succ_abstr (ic3Domain env) vars'
  res <- checkSat
  if res
    then return Nothing
    else (do
             core <- getUnsatCore
             let core_mp = Map.fromList
                           [ (read num,())
                           | 's':'t':num <- core ]
                 lift_abs = Map.intersection toLift core_mp
             init_res <- liftIO $ initiationTest env lift_abs
             let nlift_abs = if init_res
                             then lift_abs
                             else Map.insert (ic3InitialProperty env) False lift_abs
             return $ Just nlift_abs)
  
relativize :: Args a => SMTExpr Bool -> a -> a -> SMTExpr Bool
relativize expr args args'
  = snd $ foldExpr (\_ expr' -> case expr' of
                       Var n ann -> case Map.lookup n trMp of
                         Just n' -> ((),Var n' ann)
                         Nothing -> ((),Var n ann)
                       _ -> ((),expr')
                   ) () expr
  where
    (trMp,_,_) = foldsExprsId (\cmp [(Var ecur _,_),(Var enew _,_)] _
                               -> (Map.insert ecur enew cmp,undefined,undefined)
                              ) Map.empty [(args,()),(args',())] (extractArgAnnotation args)

splitRefinementTerm :: Bool -> SMTExpr Bool -> [SMTExpr Bool]
splitRefinementTerm onlyIneqs (App (SMTLogic And) xs)
  = concat $ fmap (splitRefinementTerm onlyIneqs) xs
splitRefinementTerm onlyIneqs e@(App SMTEq xs) = case cast xs of
  Nothing -> [e] -- This should not happen, as we only deal with integers
  Just (xs'::[SMTExpr Integer])
    -> if onlyIneqs
       then concat [ [x .<=. y,
                      y .<=. x]
                   | (x,y) <- pairs xs' ]
       else e:[ x .<=. y | (x,y) <- pairs xs' ]
splitRefinementTerm _ expr = [expr]

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [ (x,y) | y <- xs ] ++
               pairs xs

interpolateState :: (LiftArgs st,LiftArgs inp)
                    => IC3Env inp st -> State inp st
                    -> IO [st -> SMTExpr Bool]
interpolateState env st
  = withSMTPool (ic3Interpolation env) $
    \(vars,inp,vars') -> stack $ do
      ante <- interpolationGroup
      cons <- interpolationGroup
      assertInterp (argEq vars (liftArgs (stateFull st) (extractArgAnnotation vars))) ante
      assertInterp (argEq inp (liftArgs (stateInputs st) (extractArgAnnotation inp))) cons
      assertInterp (nextState (ic3Model env) vars inp vars') cons
      case stateSuccessor st of
        Nothing -> assertInterp (not' (assertion (ic3Model env) vars')) cons
        Just succ -> do
          succ_st <- liftIO $ readIORef succ
          assertInterp (not' $ toDomainTerm (bestAbstraction succ_st) (ic3Domain env) vars') cons
      res <- checkSat
      when res $ error "Interpolation query not unsat."
      interp <- getInterpolant [ante]
      return $ fmap (\x -> relativize x vars) (splitRefinementTerm True interp)

elimSpuriousTrans :: (LiftArgs st,LiftArgs inp)
                     => IC3Env inp st -> State inp st -> IO (IC3Env inp st)
elimSpuriousTrans env st = do
  -- Some clever trace mining stuff is omitted...
  props <- interpolateState env st
  dom' <- foldlM (\dom prop -> do
                     (_,dom') <- domainAdd prop dom
                     return dom'
                 ) (ic3Domain env) props
  return $ env { ic3Domain = dom' }

backtrackRefine :: (LiftArgs st,LiftArgs inp)
                   => IC3Env inp st
                   -> IORef (State inp st)
                   -> IO (IC3Env inp st)
backtrackRefine env ref = do
  st <- readIORef ref
  if not (stateSpuriousSucc st) ||
     stateNSpurious st /= 1
    then (case stateSuccessor st of
             Just st' -> backtrackRefine env st')
    else elimSpuriousTrans env st

rebuildConsecution :: (SMTBackend b IO,Args inp,Args st)
                      => IO b -> IC3Env inp st -> IO (IC3Env inp st)
rebuildConsecution backend env = do
  -- TODO: Heuristic check to see if rebuild is neccessary
  let mdl = ic3Model env
  case ic3Consecution env of
    Consecution { consSolver = solv } -> close solv
  ncons <- consecutionNew backend (ic3Model env)
  let (frames',last_frame) = splitLast (ic3Frames env)
  init_act <- consecutionPerform ncons $ do
    init <- var
    assert $ init .=>. (initState (ic3Model env) (consVars ncons))
    return init
  let nlast_frame = last_frame { frameActivation = init_act }
  nframes <- mapM (\frame -> do
                      nact <- consecutionPerform ncons $ do
                        act <- var
                        mapM_ (\abs -> do
                                  assert $ act .=>. (not' $ toDomainTerm abs (ic3Domain env)
                                                     (consVars ncons))
                            ) (frameFrontier frame)
                        return act
                      return $ frame { frameActivation = nact }
                  ) frames'
  return $ env { ic3Frames = nframes++[nlast_frame]
               , ic3Consecution = ncons }

abstractConsecution :: IC3Env inp st -> Int -> AbstractState st -> IO (Maybe (AbstractState st))
abstractConsecution env fi abs_st
  = consecutionPerform (ic3Consecution env) $ stack $ do
    assert $ not' $ toDomainTerm abs_st (ic3Domain env) (consVars $ ic3Consecution env)
    --assert $
    return Nothing
  

{-
handleObligations :: IC3Env inp st -> Queue inp st -> IO Bool
handleObligations env queue = case getMin queue of
  Nothing -> return True
  Just (obl,queue') -> do
    updateAbstraction env (oblState obl)
    st <- readIORef (oblState obl)
    -}
