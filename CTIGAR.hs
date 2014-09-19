{-# LANGUAGE ExistentialQuantification,FlexibleContexts,RankNTypes,
             ScopedTypeVariables,PackageImports,GADTs,DeriveDataTypeable,
             ViewPatterns #-}
module CTIGAR where

import Realization
import Domain
import Translate
import State
import SMTPool
import LitOrder
import RSM
import Gates

import Language.SMTLib2
import Language.SMTLib2.Connection
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Pipe
import Language.SMTLib2.Debug

import Data.IORef
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (when,unless)
import "mtl" Control.Monad.Trans (liftIO)
import "mtl" Control.Monad.Reader (ReaderT,runReaderT,ask,asks)
import "mtl" Control.Monad.State (StateT,evalStateT,gets)
import qualified "mtl" Control.Monad.Trans as T (lift)
import Data.List (sort,sortBy)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as Queue
import Data.Graph.Inductive (Node)
import Data.Foldable
import Data.Traversable
import Prelude hiding (sequence_,concat,mapM_,or,and,mapM,foldl)
import Data.Typeable
import Foreign.Ptr (Ptr,nullPtr)
import LLVM.FFI (BasicBlock,Instruction,getNameString)
import "mtl" Control.Monad.State (runStateT,execStateT,get,put,modify)
import Data.Bits (shiftL)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Maybe (catMaybes)
import Data.List (intersperse)

import Debug.Trace

data Frame st = Frame { frameFrontier :: Set (AbstractState st)
                      , frameActivation :: SMTExpr Bool
                      }

data IC3Config
  = IC3Cfg { ic3Model :: RealizedBlocks
           , ic3DefaultBackend :: IO (AnyBackend IO)
           , ic3InterpolationBackend :: IO (AnyBackend IO)
           , ic3DebugLevel :: Int
           , ic3MaxSpurious :: Int
           , ic3MicAttempts :: Int
           , ic3MaxDepth :: Int
           , ic3MaxJoins :: Int
           , ic3MaxCTGs :: Int
           , ic3RebuildIntercept :: Int
           , ic3RebuildVarSlope :: Int
           }

data IC3Env
  = IC3Env { ic3Domain :: Domain (LatchActs,ValueMap) -- The domain talks about the outputs
           , ic3InitialProperty :: Node
           , ic3Consecution :: Consecution ValueMap (LatchActs,ValueMap)
           , ic3Lifting :: SMTPool LiftingState
           , ic3Initiation :: SMTPool (LatchActs,ValueMap)
           , ic3Interpolation :: SMTPool InterpolationState
           , ic3LitOrder :: LitOrder
           , ic3Frames :: Vector (Frame (LatchActs,ValueMap))
           , ic3CexState :: Maybe (IORef (State ValueMap (LatchActs,ValueMap)))
           , ic3Earliest :: Int
           , ic3RSM :: RSMState
           }

data Consecution inp st = forall b. SMTBackend b IO =>
                          Consecution { consSolver :: SMTConnection b
                                      , consVars :: st
                                      , consInp :: inp
                                      , consNxtInp :: inp
                                      , consVarsPrimed :: st
                                      , consAssertPrimed :: [SMTExpr Bool]
                                      }

data InterpolationState = InterpolationState { interpBlks :: LatchActs
                                             , interpInstrs :: ValueMap
                                             , interpNxtBlks :: LatchActs
                                             , interpNxtInstrs :: ValueMap
                                             , interpInputs :: ValueMap
                                             , interpAsserts :: [SMTExpr Bool]
                                             , interpAnte :: InterpolationGroup
                                             , interpPost :: InterpolationGroup
                                             , interpReverse :: Map Integer (Either (Ptr BasicBlock,Ptr BasicBlock) (Ptr Instruction))
                                             }

data LiftingState = LiftingState { liftBlks :: LatchActs
                                 , liftInstrs :: ValueMap
                                 , liftInputs :: ValueMap
                                 , liftNxtBlks :: LatchActs
                                 , liftNxtInstrs :: ValueMap
                                 , liftNxtInputs :: ValueMap
                                 , liftNxtAsserts :: [SMTExpr Bool]
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

type IC3 a = ReaderT IC3Config (StateT IC3Env IO) a

k :: IC3 Int
k = do
  frames <- gets ic3Frames
  return $ Vec.length frames - 2

ic3Debug :: Int -> String -> IC3 ()
ic3Debug lvl txt = ic3DebugAct lvl (liftIO $ putStrLn txt)

ic3DebugAct :: Int -> IC3 () -> IC3 ()
ic3DebugAct lvl act = do
  dbgLevel <- asks ic3DebugLevel
  if dbgLevel >= lvl
    then act
    else return ()

splitLast :: [a] -> ([a],a)
splitLast [x] = ([],x)
splitLast (x:xs) = let (rest,last) = splitLast xs
                   in (x:rest,last)

consecutionPerform :: Consecution inp st -> SMT a -> IC3 a
consecutionPerform (Consecution { consSolver = conn }) act
  = liftIO $ performSMT conn act

consecutionNew :: (SMTBackend b IO)
                  => IO b -> RealizedBlocks -> IO (Consecution ValueMap (LatchActs,ValueMap))
consecutionNew backend mdl = do
  consBackend <- backend -- >>= namedDebugBackend "cons"
  consConn <- open consBackend
  (consSt,consInp,consNxtInp,consSt',primedErrs) <- performSMT consConn $ do
    setOption (ProduceModels True)
    setOption (ProduceUnsatCores True)
    blks <- createBlockVars "" mdl
    assert (blockConstraint blks)
    --blks <- createIntBlockVar "block" mdl
    inp <- createInputVars "" mdl
    instrs <- createInstrVars "" mdl
    let st1 = (blks,inp,instrs)
    (nxtBlks,real1) <- declareOutputActs mdl Map.empty st1
    --assert (blockConstraint blks)
    (nxtInstrs,real2) <- declareOutputInstrs mdl real1 st1
    (asserts1,real3) <- declareAssertions mdl real2 st1
    nxtInp <- createInputVars "nxt." mdl
    let st2 = (nxtBlks,nxtInp,nxtInstrs)
    (asserts2,_) <- declareAssertions mdl Map.empty st2
    mapM assert asserts1
    return ((blks,instrs),inp,nxtInp,(nxtBlks,nxtInstrs),asserts2)
  return $ Consecution consConn consSt consInp consNxtInp consSt' primedErrs

ic3DefaultConfig :: RealizedBlocks -> IC3Config
ic3DefaultConfig mdl
  = IC3Cfg { ic3Model = mdl
           , ic3DefaultBackend = fmap AnyBackend $ createSMTPipe "z3" ["-in","-smt2"]
           , ic3InterpolationBackend = fmap AnyBackend $ createSMTPipe "mathsat" []
           , ic3DebugLevel = 0
           , ic3MaxSpurious = 0
           , ic3MicAttempts = 1 `shiftL` 20
           , ic3MaxDepth = 1
           , ic3MaxJoins = 1 `shiftL` 20
           , ic3MaxCTGs = 3
           , ic3RebuildIntercept = 1000
           , ic3RebuildVarSlope = 200
           }

runIC3 :: IC3Config -> IC3 a -> IO a
runIC3 cfg act = do
  let backend = ic3DefaultBackend cfg
      interpBackend = ic3InterpolationBackend cfg
      mdl = ic3Model cfg
  cons <- consecutionNew backend mdl
  let liftingBackend = backend -- >>= namedDebugBackend "lift"
      initiationBackend = backend -- >>= namedDebugBackend "init"
      domainBackend = backend -- >>= namedDebugBackend "domain"
      interpBackend' = interpBackend -- >>= namedDebugBackend "interp"
  lifting <- createSMTPool liftingBackend $ do
    setOption (ProduceUnsatCores True)
    blks <- createBlockVars "" mdl
    instrs <- createInstrVars "" mdl
    inp <- createInputVars "inp." mdl
    (blks',real1) <- declareOutputActs mdl Map.empty (blks,inp,instrs)
    (instrs',real2) <- declareOutputInstrs mdl real1 (blks,inp,instrs)
    inp' <- createInputVars "inp.nxt." mdl
    (asserts,real1') <- declareAssertions mdl Map.empty (blks',inp',instrs')
    return $ LiftingState blks instrs inp blks' instrs' inp' asserts
  initiation <- createSMTPool initiationBackend $ do
    blks <- createBlockVars "" mdl
    instrs <- createInstrVars "" mdl
    assert $ initialState mdl blks
    return (blks,instrs)
  interpolation <- createSMTPool interpBackend' $ do
    setLogic "QF_LIA"
    setOption (ProduceInterpolants True)
    blks <- createBlockVars "" mdl
    instrs <- createInstrVars "" mdl
    inp <- createInputVars "" mdl
    (nxtBlks,real1) <- declareOutputActs mdl Map.empty (blks,inp,instrs)
    (nxtInstrs,real2) <- declareOutputInstrs mdl real1 (blks,inp,instrs)
    (asserts,real3) <- declareAssertions mdl real2 (blks,inp,instrs)
    nxtBlks' <- createBlockVars "nxt" mdl
    nxtInstrs' <- createInstrVars "nxt" mdl
    let rmp1 = Map.foldlWithKey
               (\rmp trg srcs
                -> Map.foldlWithKey
                   (\rmp src (Var idx _)
                     -> Map.insert idx (Left (trg,src)) rmp
                   ) rmp srcs
               ) Map.empty nxtBlks'
        rmp2 = Map.foldlWithKey
               (\rmp instr (Var idx _)
                 -> Map.insert idx (Right instr) rmp
               ) rmp1 nxtInstrs'
    ante <- interpolationGroup
    post <- interpolationGroup
    assertInterp (blockConstraint blks) ante
    mapM_ (\assert -> assertInterp assert ante) asserts
    assertInterp (argEq nxtBlks' nxtBlks) ante
    assertInterp (argEq nxtInstrs' nxtInstrs) ante
    return $ InterpolationState { interpBlks = blks
                                , interpInstrs = instrs
                                , interpNxtBlks = nxtBlks'
                                , interpNxtInstrs = nxtInstrs'
                                , interpInputs = inp
                                , interpAsserts = asserts
                                , interpAnte = ante
                                , interpPost = post
                                , interpReverse = rmp2
                                }
  domainPool <- createSMTPool domainBackend $ do
    setOption (ProduceModels True)
    blks <- createBlockVars "" mdl
    instrs <- createInstrVars "" mdl
    return (blks,instrs)
  let dom = initialDomain domainPool
  (initNode,dom') <- domainAdd (\(blks,_)
                                -> initialState mdl blks
                               ) dom
  evalStateT (runReaderT act cfg) (IC3Env { ic3Domain = dom'
                                          , ic3InitialProperty = initNode
                                          , ic3Consecution = cons
                                          , ic3Lifting = lifting
                                          , ic3Initiation = initiation
                                          , ic3Interpolation = interpolation
                                          , ic3Frames = Vec.empty
                                          , ic3CexState = Nothing
                                          , ic3LitOrder = Map.empty
                                          , ic3Earliest = 0
                                          , ic3RSM = emptyRSM
                                          })
  
newFrame :: Bool -> IC3 (Frame (LatchActs,ValueMap))
newFrame init = do
  mdl <- asks ic3Model
  cons <- gets ic3Consecution
  consecutionPerform cons $ do
    act <- varNamed "frameAct"
    if init
      then assert $ act .=>. (initialState mdl (fst $ consVars cons))
      else return ()
    return (Frame { frameFrontier = Set.empty
                  , frameActivation = act })

extractSpuriousState :: IC3Env -> Maybe (IORef (State ValueMap (LatchActs,ValueMap)))
                        -> SMT (State ValueMap (LatchActs,ValueMap))
extractSpuriousState env succ = do
  let cons = ic3Consecution env
  inps <- getValues (consInp cons)
  nxtInps <- getValues (consNxtInp cons)
  full <- getValues (consVars cons)
  return $ State { stateSuccessor = succ
                 , stateLiftedAst = Nothing
                 , stateFullAst = Nothing
                 , stateFull = full
                 , stateInputs = inps
                 , stateNxtInputs = nxtInps
                 , stateLifted = unmaskValue (undefined::(LatchActs,ValueMap)) full
                 , stateSpuriousLevel = 0
                 , stateNSpurious = 0
                 , stateSpuriousSucc = False
                 , stateDomainHash = 0 }

extractState :: Maybe (IORef (State ValueMap (LatchActs,ValueMap)))
                -> Bool
                -> IC3 (IORef (State ValueMap (LatchActs,ValueMap)))
extractState succ doLift = do
  env <- get
  mdl <- asks ic3Model
  let cons = ic3Consecution env
  vars <- consecutionPerform cons $ getValues (consVars cons)
  inp <- consecutionPerform cons $ getValues (consInp cons)
  inp' <- consecutionPerform cons $ getValues (consNxtInp cons)
  state <- if doLift
           then (do
                    nxt <- case succ of
                      Nothing -> return (\st -> app and' $ liftNxtAsserts st)
                      Just succ' -> do
                        succ'' <- liftIO $ readIORef succ'
                        return (\st -> not' $ app and' $
                                       assignPartial (liftNxtBlks st,liftNxtInstrs st)
                                       (stateLifted succ''))
                    part <- liftIO $ withSMTPool (ic3Lifting env) $
                            \vars' -> liftState ((liftBlks vars',liftInstrs vars')
                                                 ,liftInputs vars'
                                                 ,liftNxtInputs vars'
                                                 ,(liftNxtBlks vars',liftNxtInstrs vars'))
                                      (vars,inp,inp',nxt vars')
                    str_part <- renderState part
                    ic3Debug 3 ("Lifted state: "++str_part)
                    return $ State { stateSuccessor = succ
                                   , stateLiftedAst = Nothing
                                   , stateFullAst = Nothing
                                   , stateFull = vars
                                   , stateInputs = inp
                                   , stateNxtInputs = inp'
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
                               , stateNxtInputs = inp'
                               , stateLifted = unmaskValue (consVars cons) vars
                               , stateSpuriousLevel = 0
                               , stateSpuriousSucc = False
                               , stateNSpurious = 0
                               , stateDomainHash = 0 }
  liftIO $ newIORef state

liftState :: (PartialArgs st,LiftArgs inp) => (st,inp,inp,st)
             -> (Unpacked st,Unpacked inp,Unpacked inp,SMTExpr Bool)
             -> SMT (PartialValue st)
liftState (cur::st,inp,inp',nxt) vals@(vcur,vinp,vinp',vnxt) = stack $ do
  let ann_cur = extractArgAnnotation cur
      ann_inp = extractArgAnnotation inp
  ((cmp,len_st),_,_) <- foldsExprs (\(mp,n) [(arg1,_),(arg2,_)] _ -> do
                                       cid <- assertId (arg1 .==. arg2)
                                       return ((Map.insert cid n mp,n+1),[arg1,arg2],error "U3")
                                   ) (Map.empty,0) [(cur,()),(liftArgs vcur ann_cur,())] ann_cur
  assert $ argEq inp (liftArgs vinp ann_inp)
  assert $ argEq inp' (liftArgs vinp' ann_inp)
  assert vnxt
  res <- checkSat
  when res $ error "The model appears to be non-deterministic."
  core <- getUnsatCore
  let part = toTruthValues len_st 0 (sort $ fmap (cmp Map.!) core)
      vcur' = unmaskValue (error "U1"::st) vcur
      (vcur'',[]) = maskValue (error "U2"::st) vcur' part
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
initiationAbstract :: AbstractState (LatchActs,ValueMap) -> IC3 Bool
initiationAbstract state = do
  env <- get
  fmap not $ liftIO $ withSMTPool (ic3Initiation env) $
    \vars -> stack $ do
      comment $ "initiation abstract: "++show state
      assert $ toDomainTerm state (ic3Domain env) vars
      checkSat

initiationConcrete :: (Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (Maybe Bool)),
                       Map (Ptr Instruction) (Maybe UntypedValue)) -> IC3 Bool
initiationConcrete vals = do
  env <- get
  liftIO $ fmap not $ withSMTPool (ic3Initiation env) $
    \vars -> stack $ do
      mapM assert (assignPartial vars vals)
      checkSat

-- From ConsRefConcrPred
-- XXX: Henning: Use full state to abstract domain
updateAbstraction :: IORef (State ValueMap (LatchActs,ValueMap)) -> IC3 Bool
updateAbstraction ref = do
  st <- liftIO $ readIORef ref
  dom <- gets ic3Domain
  mdl <- asks ic3Model
  succUpdated <- case stateSuccessor st of
    Nothing -> return False
    Just succ -> updateAbstraction succ
  if (not succUpdated) &&
     (stateDomainHash st == domainHash dom)
    then return False
    else (do
             full <- liftIO $ domainAbstract
                     (\x -> argEq x (liftArgs (stateFull st) (realizedLatchActs mdl,realizedLatches mdl)){-app and' $ assignPartial x (stateLifted st)-})
                     dom
             lifted <- case stateSuccessor st of
               Nothing -> lift full (stateInputs st) (stateNxtInputs st) Nothing
               Just succ -> do
                 succ' <- liftIO $ readIORef succ
                 lift full (stateInputs st) (stateNxtInputs st) (Just $ bestAbstraction succ')
             liftIO $ writeIORef ref $ st { stateDomainHash = domainHash dom
                                          , stateFullAst = Just full
                                          , stateLiftedAst = lifted
                                          }
             return True)

lift :: AbstractState (LatchActs,ValueMap)
        -> Unpacked ValueMap
        -> Unpacked ValueMap
        -> Maybe (AbstractState (LatchActs,ValueMap))
        -> IC3 (Maybe (AbstractState (LatchActs,ValueMap)))
lift toLift inps nxtInps succ = do
  lifting <- gets ic3Lifting
  domain <- gets ic3Domain
  initProp <- gets ic3InitialProperty
  mdl <- asks ic3Model
  liftAbs <- liftIO $ withSMTPool lifting $ \st -> stack $ do
    (_,rev) <- foldlM (\(i,mp) (nd,expr,act) -> do
                          cid <- assertId (if act then expr else not' expr)
                          return (i+1,Map.insert cid i mp)
                      ) (0,Map.empty) (toDomainTerms toLift domain (liftBlks st,liftInstrs st))
    assert $ argEq (liftInputs st) (liftArgs inps (realizedInputs mdl))
    assert $ argEq (liftNxtInputs st) (liftArgs nxtInps (realizedInputs mdl))
    case succ of
      Nothing -> assert $ app and' (liftNxtAsserts st)
      Just succ_abstr -> assert $ toDomainTerm succ_abstr domain (liftBlks st,liftInstrs st)
    res <- checkSat
    if res
      then return Nothing
      else (do
               core <- getUnsatCore
               return $ Just $ Vec.fromList [ toLift Vec.! (rev Map.! cid)
                                            | cid <- core ])
  case liftAbs of
    Nothing -> return Nothing
    Just lift_abs' -> do
      init_res <- initiationAbstract lift_abs'
      let nlift_abs = if init_res
                      then lift_abs'
                      else Vec.cons (initProp,False) lift_abs'
      --init_res2 <- initiationAbstract nlift_abs
      --return $ error ("Init res2: "++show init_res2)
      return $ Just nlift_abs

rebuildConsecution :: IC3 ()
rebuildConsecution = do
  env <- get
  backend <- asks ic3DefaultBackend
  mdl <- asks ic3Model
  -- TODO: Heuristic check to see if rebuild is neccessary
  case ic3Consecution env of
    Consecution { consSolver = solv } -> liftIO $ close solv
  ncons <- liftIO $ consecutionNew backend mdl
  let first_frame = Vec.head (ic3Frames env)
  init_act <- consecutionPerform ncons $ do
    init <- varNamed "init_activation"
    assert $ init .=>. (initialState mdl (fst $ consVars ncons))
    return init
  let nfirst_frame = first_frame { frameActivation = init_act }
  nframes <- mapM (\frame -> do
                      nact <- consecutionPerform ncons $ do
                        act <- varNamed "activation"
                        mapM_ (\abs -> do
                                  assert $ act .=>. (not' $ toDomainTerm abs (ic3Domain env)
                                                     (consVars ncons))
                            ) (frameFrontier frame)
                        return act
                      return $ frame { frameActivation = nact }
                  ) (Vec.tail (ic3Frames env))
  put $ env { ic3Frames = Vec.cons nfirst_frame nframes
            , ic3Consecution = ncons }

{- | Checks if an abstract state is inductive at a given level.
     This is done by searching for a solution for F_i and (not s) and T and next(s).
     If the formula is unsatisfiable, we return a possible smaller state that is still inductive
     by extracting the unsatisfiable core of the formula. This state 't' is returned as
     'Left t'.
     If the formula is satisfiable, we can extract a counter-example state by extracting
     a valuation of 's'. This counter-example state is returned via the 'Right' constructor.
 -}
abstractConsecution :: Int -- ^ The level 'i'
                       -> AbstractState (LatchActs,ValueMap) -- ^ The possibly inductive abstract state 's'
                       -> Maybe (IORef (State ValueMap (LatchActs,ValueMap)))
                       -> IC3 (Either (AbstractState (LatchActs,ValueMap))
                              (State ValueMap (LatchActs,ValueMap))
                             )
abstractConsecution fi abs_st succ = do
  --rebuildConsecution
  abs_st_str <- renderAbstractState abs_st
  ic3Debug 3 ("Original abstract state: "++abs_st_str)
  env <- get
  res <- consecutionPerform (ic3Consecution env) $ stack $ do
    assert $ not' (toDomainTerm abs_st (ic3Domain env)
                   (consVars $ ic3Consecution env))
    (_,rev) <- foldlM (\(i,mp) (nd,expr,act) -> do
                          cid <- assertId
                                 (if act then expr
                                  else not' expr)
                          return (i+1,Map.insert cid i mp)
                      ) (0,Map.empty) (toDomainTerms abs_st (ic3Domain env)
                                       (consVarsPrimed $ ic3Consecution env))
    assert $ frameActivation' env fi
    res <- checkSat
    if res
      then (do
               st <- extractSpuriousState env succ
               return $ Right st)
      else (do
               core <- getUnsatCore
               let absCore = Vec.fromList [ abs_st Vec.! (rev Map.! cid)
                                          | cid <- core ]
               return $ Left absCore)
  case res of
    Right st -> return $ Right st
    Left absCore -> do
      absInit <- initiationAbstract absCore
      let absCore' = if absInit
                     then absCore
                     else Vec.cons (ic3InitialProperty env,False) absCore
      --absInit' <- initiationAbstract absCore'
      --error $ "abstractConsecution core: "++show absCore'++" "++show absInit'
      return $ Left absCore'

concreteConsecution :: Int
                       -> (Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (Maybe Bool)),
                           Map (Ptr Instruction) (Maybe UntypedValue))
                       -> IORef (State ValueMap (LatchActs,ValueMap))
                       -> IC3 (Maybe (IORef (State ValueMap (LatchActs,ValueMap))))
concreteConsecution fi st succ = do
  env <- get
  res <- consecutionPerform (ic3Consecution env) $ do
    push
    assert $ frameActivation' env fi
    assert (app or' $ fmap not' $ assignPartial (consVars $ ic3Consecution env) st)
    mapM_ assert (assignPartial (consVarsPrimed $ ic3Consecution env) st)
    checkSat
  res' <- if res
          then (do
                   rst <- extractState (Just succ) True
                   return $ Just rst)
          else return Nothing
  consecutionPerform (ic3Consecution env) pop
  return res'

handleObligations :: Queue ValueMap (LatchActs,ValueMap) -> IC3 Bool
handleObligations queue = case Queue.minView queue of
  Nothing -> do
    ic3Debug 3 $ "All obligations handled."
    return True
  Just (obl,queue') -> do
    ic3Debug 3 $ "Obligation level: "++show (oblLevel obl)
    if oblLevel obl==0
      then (do
               st <- liftIO $ readIORef (oblState obl)
               init <- initiationConcrete (stateLifted st)
               if init
                 then handleRest obl queue'
                 else (if stateNSpurious st==0
                       then (do
                                modify $ \env -> env { ic3CexState = Just (oblState obl) }
                                return False)
                       else error "backtrackRefine..."))
      else handleRest obl queue'
  where
    handleRest obl obls = do
      updateAbstraction (oblState obl)
      rst <- liftIO $ readIORef (oblState obl)
      init <- initiationAbstract (bestAbstraction rst)
      if init
        then return ()
        else error "Initiation failed on abstract state"
      ic3Debug 1 $
        "Trying to prove abstract consecution at level "++(show $ oblLevel obl)
      consRes <- abstractConsecution (oblLevel obl) (bestAbstraction rst) (Just (oblState obl))
      case consRes of
        Right abstractPred -> do
          concConsRes <- concreteConsecution (oblLevel obl) (stateLifted rst) (oblState obl)
          case concConsRes of
            Nothing -> do
              absPred <- case stateLiftedAst rst of
                Nothing -> return $ Right abstractPred
                Just _ -> case stateFullAst rst of
                  Just full -> abstractConsecution (oblLevel obl) full (Just (oblState obl))
              maxSpur <- asks ic3MaxSpurious
              case absPred of
                Right abstractPred
                  | stateNSpurious rst >= maxSpur -> elim
                  | oblLevel obl==0 -> elim
                  | otherwise -> do
                    init <- initiationConcrete (stateLifted abstractPred)
                    if init
                      then spurious
                      else elim
                  where
                    elim = do
                      elimSpuriousTrans (oblState obl) (oblLevel obl)
                      return True
                    spurious = error "spur"
                Left core -> generalizeErase obl obls core
            Just concretePred -> do
              predRes <- predecessor obl obls concretePred
              case predRes of
                Nothing -> return False
                Just nobls -> handleObligations nobls
        Left core -> generalizeErase obl obls core
    generalizeErase obl obls core = do
      n <- abstractGeneralize (oblLevel obl) core
      tk <- k
      let nobls = if n <= tk
                  then Queue.insert (obl { oblLevel = n }) obls
                  else obls
      handleObligations nobls

removeObligations :: IORef (State inp st)
                     -> Int
                     -> Queue inp st
                     -> IC3 (Queue inp st)
removeObligations st depth obls
  = return $ Queue.filter (\obl -> oblState obl /= st ||
                                   oblDepth obl /= depth
                          ) obls

backtrackRefine :: Obligation ValueMap (LatchActs,ValueMap)
                   -> Queue ValueMap (LatchActs,ValueMap)
                   -> Bool
                   -> IC3 (Queue ValueMap (LatchActs,ValueMap))
backtrackRefine obl obls enforceRefinement
  = backtrack' (oblState obl) (oblDepth obl) obls
  where
    backtrack' st depth obls = do
      rst <- liftIO $ readIORef st
      nobls <- removeObligations st depth obls
      if stateSpuriousSucc rst && stateNSpurious rst == 1
        then (case stateSuccessor rst of
                 Just succ -> do
                   if enforceRefinement
                     then elimSpuriousTrans succ (stateSpuriousLevel rst)
                     else (do
                              updateAbstraction succ
                              rsucc <- liftIO $ readIORef succ
                              consRes <- abstractConsecution (stateSpuriousLevel rst)
                                         (bestAbstraction rsucc) Nothing
                              case consRes of
                                Left _ -> return ()
                                Right _ -> elimSpuriousTrans succ (stateSpuriousLevel rst))
                   return nobls)
        else (case stateSuccessor rst of
                 Just succ -> backtrack' succ (depth-1) nobls
                 Nothing -> error $ "backtrackRefine: State has no successor")

abstractGeneralize :: Int -> AbstractState (LatchActs,ValueMap)
                      -> IC3 Int
abstractGeneralize level cube = do
  ic3DebugAct 3 $ do
    cubeStr <- renderAbstractState cube
    liftIO $ putStrLn $ "mic: "++cubeStr
  ncube <- mic level cube
  ic3DebugAct 3 $ do
    ncubeStr <- renderAbstractState ncube
    liftIO $ putStrLn $ "mic done: "++ncubeStr
  pushForward (level+1) ncube
  where
    pushForward level cube = do
      tk <- k
      if level <= tk
        then (do
                 consRes <- abstractConsecution level cube Nothing
                 case consRes of
                   Left ncube -> pushForward (level+1) ncube
                   Right _ -> do
                     ic3Debug 3 $ "Adding cube at level "++show level
                     addAbstractCube level cube
                     return level)
        else (do
                 ic3Debug 3 $ "Adding cube at level "++show level
                 addAbstractCube level cube
                 return level)

baseCases :: RealizedBlocks -> SMT (Maybe ErrorTrace)
baseCases st = do
  comment "Basic blocks:"
  blks0 <- createBlockVars "" st
  comment "Inputs:"
  inp0 <- createInputVars "" st
  comment "Latches:"
  instrs0 <- createInstrVars "" st
  let st0 = (blks0,inp0,instrs0)
  assert $ initialState st blks0
  comment "Declare assertions:"
  (asserts0,real0) <- declareAssertions st Map.empty st0
  comment "Declare output acts:"
  (blks1,real1) <- declareOutputActs st real0 st0
  comment $ show $ fmap Map.keys blks1
  comment "Declare output instrs:"
  (instrs1,real2) <- declareOutputInstrs st real1 st0
  comment $ show instrs1
  comment "Inputs 2:"
  inp1 <- createInputVars "nxt" st
  let st1 = (blks1,inp1,instrs1)
  comment "Declare assertions 2:"
  (asserts1,_) <- declareAssertions st Map.empty st1
  assert $ not' $ app and' (asserts0++asserts1)
  res <- checkSat
  if res
    then (do
             succ0 <- mapM getValue asserts0
             if not $ and succ0
               then (do
                        cv0 <- getConcreteValues st st0
                        return (Just [cv0]))
               else (do
                        cv0 <- getConcreteValues st st0
                        cv1 <- getConcreteValues st (blks1,inp1,instrs1)
                        return (Just [cv0,cv1])))
    else return Nothing

extend :: IC3 ()
extend = do
  frames <- gets ic3Frames
  if Vec.null frames
    then (do
             fr <- newFrame True
             modify $ \env -> env { ic3Frames = Vec.singleton fr })
    else (do
             fr <- newFrame False
             modify $ \env -> env { ic3Frames = Vec.snoc (ic3Frames env) fr })

-- | Strengthens frontier to remove error successors
--   Returns 'Nothing' if strengthening failed
--   Returns 'Just False' if cubes were generated
--   Returns 'Just True' if no cubes were generated
strengthen :: IC3 (Maybe Bool)
strengthen = strengthen' True
  where
    strengthen' trivial = do
      tk <- k
      env <- get
      {-(rv,act) <- consecutionPerform (ic3Consecution env) $ do
        act <- varNamed "activation"
        assert $ act .=>. (app or' $ fmap not' $ consAssertPrimed (ic3Consecution env))
        push
        assert act
        assert $ frameActivation' env tk
        rv <- checkSat
        return (rv,act)-}
      ic3Debug 2 $ "Trying to get from frontier at level "++show tk++" to error"
      rv <- consecutionPerform (ic3Consecution env) $ do
        push
        assert $ app or' $ fmap not' $ consAssertPrimed (ic3Consecution env)
        assert $ frameActivation' env tk
        checkSat
      if rv
        then (do
                 sti <- extractState Nothing True
                 --consecutionPerform (ic3Consecution env) $ do
                 --  pop
                 --  assert $ not' act
                 consecutionPerform (ic3Consecution env) pop
                 tk <- k
                 let obl = Obligation sti (tk-1) 1
                     queue = Queue.singleton obl
                 res <- handleObligations queue
                 if res
                   then strengthen' False
                   else return Nothing)
        else (do
                 ic3Debug 2 $ "Can't get to error ("++
                   (if trivial
                    then "trivial"
                    else "not trivial")++")"
                 --consecutionPerform (ic3Consecution env) $ do
                 --  pop
                 --  assert $ not' act
                 consecutionPerform (ic3Consecution env) pop
                 return $ Just trivial)

check :: RealizedBlocks -> IO (Maybe ErrorTrace)
check st = do
  backend <- createSMTPipe "z3" ["-in","-smt2"] >>= namedDebugBackend "base"
  tr <- withSMTBackend backend (baseCases st)
  case tr of
    Just tr' -> return (Just tr')
    Nothing -> runIC3 (ic3DefaultConfig st) (do
                                                addBlkProperties
                                                addEqProperties
                                                addCmpProperties
                                                --addAssertProperties
                                                extend
                                                extend
                                                checkIt)
  where
    checkIt = do
      extend
      sres <- strengthen
      case sres of
        Nothing -> do
          real <- asks ic3Model
          cex <- gets ic3CexState
          tr <- liftIO $ getWitnessTr cex
          liftIO $ do
            pipe <- createSMTPipe "z3" ["-in","-smt2"]
            backend <- namedDebugBackend "err" pipe
            withSMTBackend backend $ do
              acts0 <- createBlockVars "" real
              assert $ initialState real acts0
              latch0 <- createInstrVars "" real
              tr' <- constructTrace real acts0 latch0 tr []
              rv <- checkSat
              if rv
                then (do
                         tr'' <- getWitness real tr'
                         return (Just tr''))
                else error $ "Error trace is infeasible."
        Just trivial -> do
          pres <- propagate trivial
          if pres==0
            then checkIt
            else return Nothing
    getWitnessTr Nothing = return []
    getWitnessTr (Just st) = do
      rst <- readIORef st
      rest <- getWitnessTr (stateSuccessor rst)
      return $ (stateLifted rst):rest
    constructTrace _ _ _ [] errs = do
      comment "Assertions"
      assert $ app or' (fmap not' errs)
      return []
    constructTrace real acts latch ((cacts,clatch):xs) asserts = do
      comment "Assignments"
      assert $ app and' $ assignPartial acts cacts
      assert $ app and' $ assignPartial latch clatch
      comment "Inputs"
      inps <- argVarsAnn (realizedInputs real)
      (assumps,real0) <- declareAssumptions real Map.empty (acts,inps,latch)
      (nacts,real1) <- declareOutputActs real real0 (acts,inps,latch)
      (nlatch,real2) <- declareOutputInstrs real real1 (acts,inps,latch)
      (ass,real3) <- declareAssertions real real2 (acts,inps,latch)
      comment "Assumptions"
      assert $ app and' assumps
      rest <- constructTrace real nacts nlatch xs (ass++asserts)
      return ((acts,latch,inps):rest)
    getWitness _ [] = return []
    getWitness real (x:xs) = do
      concr <- getConcreteValues real x
      concrs <- getWitness real xs
      return $ concr:concrs

propagate :: Bool -> IC3 Int
propagate trivial = do
  do
    frames <- gets ic3Frames
    ic3Debug 5 $ "Before propagation: "++
      (show $ fmap frameFrontier frames)
  earliest <- gets ic3Earliest
  tk <- k
  modify $ \env -> let (pre,oframes) = Vec.splitAt (earliest-1) (ic3Frames env)
                       (_,nframes) = mapAccumR (\all frame
                                                -> let rem = Set.difference (frameFrontier frame) all
                                                   in (Set.union all rem,frame { frameFrontier = rem })
                                               ) Set.empty (Vec.drop (earliest-1) oframes)
                       rframes = pre Vec.++ nframes
                   in env { ic3Frames = rframes }
  res <- pushCubes (if trivial
                    then [tk]
                    else [1..tk])
  do
    frames <- gets ic3Frames
    ic3Debug 5 $ "After propagation: "++
      (show $ fmap frameFrontier frames)
  return res  
  where
    pushCubes [] = return 0
    pushCubes (i:is) = do
      frames <- gets ic3Frames
      let frame = frames Vec.! i
          cubes = frameFrontier $ frames Vec.! i
      ncubes <- foldlM (\keep cube -> do
                           consRes <- abstractConsecution i cube Nothing
                           case consRes of
                             Left core -> do
                               addAbstractCube (i+1) core
                               return keep
                             Right _ -> return (Set.insert cube keep)
                       ) Set.empty cubes
      modify $ \env -> env { ic3Frames = (ic3Frames env) Vec.//
                                         [(i,frame { frameFrontier = ncubes })]
                           }
      if Set.null ncubes
        then return i
        else pushCubes is

predecessor :: Obligation ValueMap (LatchActs,ValueMap)
               -> Queue ValueMap (LatchActs,ValueMap)
               -> IORef (State ValueMap (LatchActs,ValueMap))
               -> IC3 (Maybe (Queue ValueMap (LatchActs,ValueMap)))
predecessor obl obls pred
  | oblLevel obl==0 = do
    oblState <- liftIO $ readIORef (oblState obl)
    if stateNSpurious oblState==0
      then (do
               modify (\env -> env { ic3CexState = Just pred })
               return Nothing)
      else (do
               res <- backtrackRefine obl obls True
               return $ Just res)
  | otherwise = do
    oblState <- liftIO $ readIORef (oblState obl)
    liftIO $ modifyIORef pred $
      \rpred -> rpred { stateSpuriousSucc = False
                      , stateSpuriousLevel = 0
                      , stateNSpurious = stateNSpurious oblState
                      }
    return $ Just $ Queue.insert (Obligation pred 0 (oblDepth obl+1)) obls

elimSpuriousTrans :: IORef (State ValueMap (LatchActs,ValueMap)) -> Int
                     -> IC3 ()
elimSpuriousTrans st level = do
  rst <- liftIO $ readIORef st
  backend <- asks ic3DefaultBackend
  env <- get
  (nrsm,props) <- liftIO $ analyzeTrace (backend {- >>= namedDebugBackend "rsm" -}) rst (ic3RSM env)
  put $ env { ic3RSM = nrsm }
  interp <- interpolate level (stateLifted rst)
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain trm
                     -> do
                       (_,ndom) <- liftIO $ domainAdd trm cdomain
                       return ndom
                    ) domain (interp++props)
  --liftIO $ domainDump ndomain >>= putStrLn
  modify $ \env -> env { ic3Domain = ndomain }

interpolate :: Int -> PartialValue (LatchActs,ValueMap)
               -> IC3 [(LatchActs,ValueMap) -> SMTExpr Bool]
interpolate j s = do
  env <- get
  cfg <- ask
  liftIO $ withSMTPool (ic3Interpolation env) $
    \st -> stack $ do
      comment $ "Interpolating at level "++show j
      -- XXX: Workaround for MathSAT:
      ante <- interpolationGroup
      post <- interpolationGroup
      if j==0
        then assertInterp (initialState (ic3Model cfg) (interpBlks st)) ante --(interpAnte st)
        else (do
                 let frames = Vec.drop j (ic3Frames env)
                 mapM_ (\fr -> mapM_ (\ast -> do
                                         let trm = toDomainTerm ast (ic3Domain env)
                                                   (interpBlks st,interpInstrs st)
                                         assertInterp (not' trm) ante --(interpAnte st)
                                     ) (frameFrontier fr)
                       ) frames)
      assertInterp (not' $ app and' $ assignPartial (interpBlks st,interpInstrs st) s)
        ante -- (interpAnte st)
      assertInterp (app and' $ assignPartial (interpNxtBlks st,interpNxtInstrs st) s)
        post -- (interpPost st)
      res <- checkSat
      when res $ error "Interpolation query is SAT"
      interp <- getInterpolant [ante,interpAnte st]
      let interp1 = cleanInterpolant interp
      interp1Str <- renderExpr interp1
      comment $ "Cleaned interpolant: "++interp1Str
      return $ fmap (relativizeInterpolant (interpReverse st)
                    ) $ splitInterpolant $ negateInterpolant interp1
  where
    cleanInterpolant (Let ann arg f) = cleanInterpolant (f arg)
    cleanInterpolant (App (SMTLogic op) es) = App (SMTLogic op)
                                              (fmap cleanInterpolant es)
    cleanInterpolant (App SMTNot e) = App SMTNot (cleanInterpolant e)
    cleanInterpolant (App (SMTOrd op) arg) = case cast arg of
      Just (lhs,rhs) -> case (do
                                 lhs' <- removeToReal lhs
                                 rhs' <- removeToReal rhs
                                 return (lhs',rhs')) of
                          Just arg' -> App (SMTOrd op) arg'
                          Nothing -> App (SMTOrd op) arg
      Nothing -> App (SMTOrd op) arg
    cleanInterpolant (App (SMTArith Plus) [x]) = cleanInterpolant x
    cleanInterpolant e = e

    removeToReal :: SMTExpr Rational -> Maybe (SMTExpr Integer)
    removeToReal (App SMTToReal e) = Just e
    removeToReal _ = Nothing

    negateInterpolant (App SMTNot e) = pushNegation e
    negateInterpolant (App (SMTLogic And) es) = App (SMTLogic Or) (fmap negateInterpolant es)
    negateInterpolant (App (SMTLogic Or) es) = App (SMTLogic And) (fmap negateInterpolant es)
    negateInterpolant (App (SMTOrd op) arg)
      = let nop = case op of
              Ge -> Lt
              Gt -> Le
              Le -> Gt
              Lt -> Ge
        in App (SMTOrd nop) arg
    negateInterpolant e = App SMTNot e

    pushNegation (App SMTNot e) = negateInterpolant e
    pushNegation (App (SMTLogic op) es) = App (SMTLogic op) (fmap pushNegation es)
    pushNegation e = e

    splitInterpolant (App (SMTLogic And) es) = concat (fmap splitInterpolant es)
    -- Henning: Maybe it's a good idea not to refine with equalities:
    splitInterpolant (App SMTEq [lhs,rhs]) = [App (SMTOrd Ge) (lhs,rhs)
                                             ,App (SMTOrd Lt) (lhs,rhs)]
    splitInterpolant e = [e]

    relativizeInterpolant rev trm (blks,instrs)
      = snd $ foldExpr (\_ expr
                        -> ((),case expr of
                               Var idx ann -> case Map.lookup idx rev of
                                 Just (Left (trg,src))
                                   -> case cast ((blks Map.! trg) Map.! src) of
                                   Just r -> r
                                 Just (Right instr)
                                   -> case entypeValue cast (instrs Map.! instr) of
                                   Just r -> r
                               _ -> expr)
                       ) () trm

mic :: Int -> AbstractState (LatchActs,ValueMap)
       -> IC3 (AbstractState (LatchActs,ValueMap))
mic level ast = mic' level ast 1

mic' :: Int -> AbstractState (LatchActs,ValueMap) -> Int
        -> IC3 (AbstractState (LatchActs,ValueMap))
mic' level ast recDepth = do
  order <- gets ic3LitOrder
  attempts <- asks ic3MicAttempts
  let sortedAst = Vec.fromList $ sortBy (\(k1,_) (k2,_)
                                         -> compareOrder order k1 k2) $
                  Vec.toList ast
  mic'' sortedAst 0 attempts
  where
    mic'' ast _ 0 = return ast
    mic'' ast i attempts
      | i >= Vec.length ast = return ast
      | otherwise = do
        let (before,after) = Vec.splitAt i ast
            cp = before Vec.++ (Vec.tail after)
        ic3Debug 3 "CTGDown"
        maxCTGs <- asks ic3MaxCTGs
        downRes <- ctgDown level cp i recDepth maxCTGs
        ic3Debug 3 "CTGDown done."
        case downRes of
          Nothing -> mic'' ast (i+1) (attempts-1)
          Just ncp -> do
            let mp = Map.fromList (Vec.toList ncp)
                nast = Vec.fromList $ reorder (Vec.toList ast) mp
            nattempts <- asks ic3MicAttempts
            mic'' nast i nattempts

    reorder [] lits = Map.toList lits
    reorder ((key,val):rest) lits
      = case Map.updateLookupWithKey
             (\_ _ -> Nothing)
             key lits of
          (Nothing,_) -> reorder rest lits
          (Just _,nlits) -> (key,val):reorder rest nlits

ctgDown :: Int -> AbstractState (LatchActs,ValueMap) -> Int -> Int -> Int
           -> IC3 (Maybe (AbstractState (LatchActs,ValueMap)))
ctgDown = ctgDown' 0 0
  where
    ctgDown' ctgs joins level ast keepTo recDepth efMaxCTGs = do
      cfg <- ask
      ic3Debug 3 ("ctgDown' ctgs="++
                  show ctgs++" joins="++
                  show joins++" level="++
                  show level++" keepTo="++
                  show keepTo++" recDepth="++
                  show recDepth++" efMaxCTGs="++
                  show efMaxCTGs)
      init <- initiationAbstract ast
      if not init
        then return Nothing
        else (if recDepth > ic3MaxDepth cfg
              then (do
                       res <- abstractConsecution level ast Nothing
                       case res of
                         Left nast -> return $ Just nast
                         Right _ -> return Nothing)
              else (do
                       res <- abstractConsecution level ast Nothing
                       case res of
                         Left core -> return (Just core)
                         Right ctg -> do
                           domain <- gets ic3Domain
                           abstractCtg <- liftIO $ domainAbstract
                                          (\x -> app and' $ assignPartial x (stateLifted ctg)
                                          ) domain
                           if ctgs < efMaxCTGs && level > 1
                             then (do
                                      init <- initiationAbstract abstractCtg
                                      if init
                                        then (do
                                                 res' <- abstractConsecution (level-1) abstractCtg Nothing
                                                 case res' of
                                                   Left ctgCore -> pushForward ctgs joins level ast keepTo recDepth efMaxCTGs ctgCore level
                                                   Right _ -> checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg)
                                        else checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg)
                             else checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg))
    checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg = do
      cfg <- ask
      if joins < ic3MaxJoins cfg
        then (case joined of
                 Nothing -> return Nothing
                 Just joined' -- XXX: Henning: The case split here is to prevent looping, find out if it is actually correct.
                   | Vec.length joined' < Vec.length ast -> ctgDown' 0 (joins+1) level joined' keepTo recDepth efMaxCTGs
                   | otherwise -> return Nothing)
        else return Nothing
      where
        joined = fmap (Vec.fromList . catMaybes) $
                 mapM (\(i,(var,val)) -> case find (\(var',_) -> var==var') abstractCtg of
                          Nothing
                            | i < keepTo -> Nothing
                            | otherwise -> Just Nothing
                          Just _ -> Just (Just (var,val))
                       ) (zip [0..] (Vec.toList ast))
    pushForward ctgs joins level ast keepTo recDepth efMaxCTGs ctgCore j = do
      env <- get
      tk <- k
      if j <= tk
        then (do
                 res <- abstractConsecution j ctgCore Nothing
                 case res of
                   Left ctgCore' -> pushForward ctgs joins level ast keepTo recDepth efMaxCTGs ctgCore' (j+1)
                   Right _ -> do
                     ctgCore' <- mic' (j-1) ctgCore (recDepth+1)
                     addAbstractCube j ctgCore'
                     ctgDown' (ctgs+1) joins level ast keepTo recDepth efMaxCTGs)
        else (do
                 ctgCore' <- mic' (j-1) ctgCore (recDepth+1)
                 addAbstractCube j ctgCore'
                 ctgDown' (ctgs+1) joins level ast keepTo recDepth efMaxCTGs)
            
addAbstractCube :: Int -> AbstractState (LatchActs,ValueMap)
                   -> IC3 ()
addAbstractCube level state = do
  frame <- fmap (Vec.! level) $ gets ic3Frames
  if Set.member state (frameFrontier frame)
    then return ()
    else (do
             env <- get
             let cons = ic3Consecution env
                 tv = toDomainTerm state (ic3Domain env) (consVars cons)
             consecutionPerform cons $ assert $ (frameActivation frame) .=>. (not' tv)
             put $ env { ic3Frames = Vec.update (ic3Frames env)
                                     (Vec.singleton (level,frame { frameFrontier = Set.insert state
                                                                                   (frameFrontier frame)
                                                                 }))
                       , ic3Earliest = min (ic3Earliest env) level
                       })

frameActivation' :: IC3Env -> Int -> SMTExpr Bool
frameActivation' env fi
  = app and' $ Vec.toList $ fmap frameActivation $ Vec.drop fi (ic3Frames env)

addEqProperties :: IC3 ()
addEqProperties = do
  mdl <- asks ic3Model
  let props = mkEqs (Map.toList (realizedLatches mdl))
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain trm -> do
                        (_,ndom) <- liftIO $ domainAdd trm cdomain
                        return ndom
                    ) domain props
  modify $ \env -> env { ic3Domain = ndomain }
  where
    mkEqs [] = []
    mkEqs [x] = []
    mkEqs ((i,x):xs) = (mkEqs' i x xs)++
                       (mkEqs xs)

    mkEqs' i x [] = []
    mkEqs' i x ((j,y):xs)
      | x==y = (\(_,instrs) -> entypeValue (\e1 -> e1 .==. (castUntypedExprValue (instrs Map.! j)))
                               (instrs Map.! i)
               ):(mkEqs' i x xs)
      | otherwise = mkEqs' i x xs

addCmpProperties :: IC3 ()
addCmpProperties = do
  mdl <- asks ic3Model
  let props = mkCmps (Map.toList (realizedLatches mdl))
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain trm -> do
                        (_,ndom) <- liftIO $ domainAdd trm cdomain
                        return ndom
                    ) domain props
  modify $ \env -> env { ic3Domain = ndomain }
  where
    intP = ProxyArgValue (undefined::Integer) ()
    
    mkCmps [] = []
    mkCmps [x] = []
    mkCmps ((i,x):xs)
      | x == intP = (mkCmps' i xs)++
                    (mkCmps xs)
      | otherwise = mkCmps xs

    mkCmps' i [] = []
    mkCmps' i ((j,y):xs)
      | y == intP = (\(_,instrs)
                     -> (castUntypedExprValue (instrs Map.! i) :: SMTExpr Integer)
                        .<.
                        (castUntypedExprValue (instrs Map.! j))
                    ):(mkCmps' i xs)
      | otherwise = mkCmps' i xs

addBlkProperties :: IC3 ()
addBlkProperties = do
  mdl <- asks ic3Model
  let props = mkActs [ (trg,src)
                     | (trg,srcs) <- Map.toList (realizedLatchActs mdl)
                     , (src,act) <- Map.toList srcs ] []
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain trm -> do
                        (_,ndom) <- liftIO $ domainAdd trm cdomain
                        return ndom
                    ) domain props
  modify $ \env -> env { ic3Domain = ndomain }
  where
    mkActs [] _ = []
    mkActs ((trg,src):xs) ys = (\(acts,_) -> app and'
                                             (((acts Map.! trg) Map.! src):
                                              [ not' $ ((acts Map.! trg') Map.! src')
                                              | (trg',src') <- xs++ys ])
                               ):(mkActs xs ((trg,src):ys))

addAssertProperties :: IC3 ()
addAssertProperties = do
  mdl <- asks ic3Model
  domain <- gets ic3Domain
  let props = fmap (\ass (acts,latch)
                    -> let inp = (acts,fmap defInput (realizedInputs mdl),latch)
                       in translateGateExpr (ass inp)
                          (realizedGates mdl) Map.empty inp
                   ) (realizedAsserts mdl)
  ndomain <- foldlM (\cdomain trm -> do
                        (_,ndom) <- liftIO $ domainAdd trm cdomain
                        return ndom
                    ) domain props
  modify $ \env -> env { ic3Domain = ndomain }
  where
    defInput (ProxyArgValue (cast -> Just (_::Bool)) ann)
      = UntypedExprValue (constant False)
    defInput (ProxyArgValue (cast -> Just (_::Integer)) ann)
      = UntypedExprValue (constant (0::Integer))

renderState :: (Map (Ptr BasicBlock) (Map (Ptr BasicBlock) (Maybe Bool)),
                Map (Ptr Instruction) (Maybe UntypedValue)) -> IC3 String
renderState (acts,mp) = do
  blk <- findBlk [ (trg,src,act)
                 | (trg,srcs) <- Map.toList acts
                 , (src,Just act) <- Map.toList srcs ]
  instrs <- mapM (\(instr,val) -> do
                     instrName <- liftIO $ getNameString instr
                     return $ instrName++"="++show val
                 ) [ (instr,val) | (instr,Just val) <- Map.toList mp ]
  return $ blk++"["++concat (intersperse "," instrs)++"]"
  where
    findBlk xs = case [ (trg,src) | (trg,src,True) <- xs ] of
      [(trg,src)] -> do
        srcName <- liftIO $ getNameString src
        trgName <- liftIO $ getNameString trg
        return (srcName++"."++trgName)

renderAbstractState :: AbstractState (LatchActs,ValueMap)
                       -> IC3 String
renderAbstractState st = do
  domain <- gets ic3Domain
  liftIO $ renderDomainTerm st domain
