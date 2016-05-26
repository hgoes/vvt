{-# LANGUAGE ExistentialQuantification,FlexibleContexts,RankNTypes,
             ScopedTypeVariables,PackageImports,GADTs,DeriveDataTypeable,
             ViewPatterns,MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric#-}
module CTIGAR where

import qualified Realization as TR
import qualified Domain as Dom
import Consecution
import Args
import PartialArgs
import SMTPool
import LitOrder
import BackendOptions
import Simplify

import Language.SMTLib2 hiding (simplify)
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Debug
import Language.SMTLib2.Timing
import Language.SMTLib2.Internals.Backend (LVar)
import qualified Language.SMTLib2.Internals.Backend as B
import qualified Language.SMTLib2.Internals.Expression as E
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Embed

import qualified Data.Map as Map
import qualified Data.Vector as Vec
import qualified Data.IntSet as IntSet
import qualified Data.Yaml as Y
import Data.IORef
import Control.Monad (when)
import Data.Functor.Identity
import "mtl" Control.Monad.Trans (MonadIO,liftIO)
import "mtl" Control.Monad.Reader (MonadReader(..),ask,asks)
import "mtl" Control.Monad.State (MonadState,gets,get,put,modify)
import Data.List (sort,sortBy,intercalate)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as Queue
import Data.Graph.Inductive (Node)
import Data.Foldable
import Data.Traversable
import Prelude hiding (sequence_,concat,mapM_,or,and,mapM,foldl)
import Data.Typeable
import Data.Bits (shiftL)
import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)
import Data.Time.Clock
import Control.Exception (Exception,SomeException,catch,throw)
import System.IO
import System.Exit
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Control.Monad.Reader (runReader)

import Stats

data AnyBackend m = forall b. (Backend b,SMTMonad b ~ m) => AnyBackend { anyBackend :: m b }

withAnyBackend :: AnyBackend m -> (forall b. Backend b => SMT b r) -> m r
withAnyBackend (AnyBackend constr) act
  = withBackend constr act

data IC3Config mdl
  = IC3Cfg { ic3Model :: mdl
           , ic3ConsecutionBackend :: AnyBackend IO
           , ic3LiftingBackend :: AnyBackend IO
           , ic3DomainBackend :: AnyBackend IO
           , ic3BaseBackend :: AnyBackend IO
           , ic3InitBackend :: AnyBackend IO
           , ic3InterpolationBackend :: AnyBackend IO
           , ic3DebugLevel :: Int
           , ic3MaxSpurious :: Int
           , ic3MicAttempts :: Int
           , ic3MaxDepth :: Int
           , ic3MaxJoins :: Int
           , ic3MaxCTGs :: Int
           , ic3CollectStats :: Bool
           , ic3DumpDomainFile :: Maybe String
           , ic3DumpStatsFile :: Maybe String
           , ic3DumpStatesFile :: Maybe String
           }

data IC3Env mdl
  = IC3Env { ic3Domain :: Dom.Domain (TR.State mdl) -- The domain talks about the outputs
           , ic3InitialProperty :: Node
           , ic3Consecution :: Consecution (TR.Input mdl) (TR.State mdl)
           , ic3Lifting :: Lifting mdl
           , ic3Initiation :: SMTPool (PoolVars (TR.State mdl))
           , ic3Interpolation :: SMTPool (InterpolationState mdl)
           , ic3LitOrder :: LitOrder
           , ic3CexState :: Maybe (IORef (State (TR.Input mdl) (TR.State mdl)))
           , ic3Earliest :: Int
           , ic3PredicateExtractor :: TR.PredicateExtractor mdl
           , ic3Stats :: Maybe IC3Stats
           }

type Lifting mdl = SMTPool (LiftingState mdl)

data InterpolationState mdl b
  = InterpolationState { interpCur :: TR.State mdl (Expr b)
                       , interpNxt :: TR.State mdl (Expr b)
                       , interpInputs :: TR.Input mdl (Expr b)
                       , interpNxtInputs :: TR.Input mdl (Expr b)
                       , interpAsserts :: [Expr b BoolType]
                       , interpReverse :: DMap (B.Var b) (RevComp (TR.State mdl))
                       }

data LiftingState mdl b
  = LiftingState { liftCur :: TR.State mdl (Expr b)
                 , liftInputs :: TR.Input mdl (Expr b)
                 , liftNxt :: TR.State mdl (Expr b)
                 , liftNxtInputs :: TR.Input mdl (Expr b)
                 , liftNxtAsserts :: [Expr b BoolType]
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

-- | In order to deal with exceptions, this is a custom monad.
newtype IC3 mdl a = IC3 { evalIC3 :: IC3Config mdl -> IORef (IC3Env mdl) -> IO a }

data State inp st = State { stateSuccessor :: Maybe (IORef (State inp st))
                          , stateLiftedAst :: Maybe (Dom.AbstractState st)
                          , stateFullAst :: Maybe (Dom.AbstractState st)
                          , stateFull :: Unpacked st
                          , stateInputs :: Unpacked inp
                          , stateNxtInputs :: Unpacked inp
                          , stateLifted :: Partial st
                          , stateLiftedInputs :: Partial inp
                          , stateSpuriousLevel :: Int
                          , stateNSpurious :: Int
                          , stateSpuriousSucc :: Bool
                          , stateDomainHash :: Int
                          }

instance Applicative (IC3 mdl) where
  pure x = IC3 (\_ _ -> return x)
  x <*> y = IC3 (\cfg env -> do
                     f <- evalIC3 x cfg env
                     v <- evalIC3 y cfg env
                     return (f v))

instance Monad (IC3 mdl) where
  (>>=) ic3 f = IC3 $ \cfg ref -> do
    r1 <- evalIC3 ic3 cfg ref
    evalIC3 (f r1) cfg ref
  return x = IC3 $ \_ _ -> return x

instance MonadIO (IC3 mdl) where
  liftIO f = IC3 $ \_ _ -> f

instance Functor (IC3 mdl) where
  fmap f act = IC3 $ \cfg ref -> do
    res <- evalIC3 act cfg ref
    return (f res)

instance MonadState (IC3Env mdl) (IC3 mdl) where
  get = IC3 $ \_ ref -> readIORef ref
  put x = IC3 $ \_ ref -> writeIORef ref x

instance MonadReader (IC3Config mdl) (IC3 mdl) where
  ask = IC3 $ \cfg _ -> return cfg
  local f act = IC3 $ \cfg ref -> evalIC3 act (f cfg) ref
  reader f = IC3 $ \cfg _ -> return $ f cfg

ic3Catch :: Exception e => IC3 mdl a -> (e -> IC3 mdl a) -> IC3 mdl a
ic3Catch act handle = IC3 $ \cfg ref -> evalIC3 act cfg ref `catch`
                                        (\ex -> evalIC3 (handle ex) cfg ref)

bestAbstraction :: State inp st -> Dom.AbstractState st
bestAbstraction st = case stateLiftedAst st of
  Just abs -> abs
  Nothing -> case stateFullAst st of
    Just abs -> abs
    Nothing -> error "State doesn't have an abstraction."

k :: IC3 mdl Int
k = do
  cons <- gets ic3Consecution
  return $ frontier cons

ic3Debug :: Int -> String -> IC3 mdl ()
ic3Debug lvl txt = ic3DebugAct lvl (liftIO $ hPutStrLn stderr txt)

ic3DebugAct :: Int -> IC3 mdl () -> IC3 mdl ()
ic3DebugAct lvl act = do
  dbgLevel <- asks ic3DebugLevel
  if dbgLevel >= lvl
    then act
    else return ()

splitLast :: [a] -> ([a],a)
splitLast [x] = ([],x)
splitLast (x:xs) = let (rest,last) = splitLast xs
                   in (x:rest,last)

mkIC3Config :: mdl -> BackendOptions
            -> Int -- ^ Verbosity
            -> Bool -- ^ Dump stats?
            -> Maybe String -- ^ Dump domain?
            -> Maybe String -- ^ Dump stats?
            -> Maybe String -- ^ Dump states?
            -> IC3Config mdl
mkIC3Config mdl opts verb stats dumpDomain dumpStats dumpStates
  = IC3Cfg { ic3Model = mdl
           , ic3ConsecutionBackend = mkPipe (optBackend opts Map.! ConsecutionBackend)
                                     (fmap (\t -> ("cons",t)) $ Map.lookup ConsecutionBackend (optDebugBackend opts))
           , ic3LiftingBackend = mkPipe (optBackend opts Map.! Lifting)
                                 (fmap (\t -> ("lift",t)) $ Map.lookup Lifting (optDebugBackend opts))
           , ic3DomainBackend = mkPipe (optBackend opts Map.! Domain)
                                (fmap (\t -> ("domain",t)) $ Map.lookup Domain (optDebugBackend opts))
           , ic3BaseBackend = mkPipe (optBackend opts Map.! Base)
                              (fmap (\t -> ("base",t)) $ Map.lookup Base (optDebugBackend opts))
           , ic3InitBackend = mkPipe (optBackend opts Map.! Initiation)
                              (fmap (\t -> ("init",t)) $ Map.lookup Initiation (optDebugBackend opts))
           , ic3InterpolationBackend = mkPipe (optBackend opts Map.! Interpolation)
                                       (fmap (\t -> ("interp",t)) $ Map.lookup Interpolation (optDebugBackend opts))
           , ic3DebugLevel = verb
           , ic3MaxSpurious = 0
           , ic3MicAttempts = 1 `shiftL` 20
           , ic3MaxDepth = 1
           , ic3MaxJoins = 1 `shiftL` 20
           , ic3MaxCTGs = 3
           , ic3CollectStats = stats
           , ic3DumpDomainFile = dumpDomain
           , ic3DumpStatsFile = dumpStats
           , ic3DumpStatesFile = dumpStates
           }
  where
    mkPipe :: BackendUse -> Maybe (String,BackendDebug) -> AnyBackend IO
    mkPipe cmd debug = createBackend cmd (\b -> case debug of
                                           Nothing -> AnyBackend b
                                           Just (name,tp) -> AnyBackend $ do
                                             b' <- b
                                             createDebugBackend name tp b')

runIC3 :: TR.TransitionRelation mdl => IC3Config mdl -> IC3 mdl a -> IO a
runIC3 cfg act = do
  let mdl = ic3Model cfg
  stats <- if ic3CollectStats cfg
           then fmap Just newIC3Stats
           else return Nothing
  -- MathSAT is really annoying, we have to take care of it like a baby
  interpolationIsMathSAT <- do
    withAnyBackend (ic3InterpolationBackend cfg) $ do
      name <- getInfo SMTSolverName
      return $ name=="MathSAT5"
  let consBackend = case stats of
        Nothing -> ic3ConsecutionBackend cfg
        Just stats -> addTiming (consecutionTime stats) (consecutionNum stats)
                      (ic3ConsecutionBackend cfg)
      liftingBackend = case stats of
        Nothing -> ic3LiftingBackend cfg -- >>= namedDebugBackend "lift"
        Just stats -> addTiming (liftingTime stats) (liftingNum stats)
                      (ic3LiftingBackend cfg)
      initiationBackend = case stats of
        Nothing -> ic3InitBackend cfg -- >>= namedDebugBackend "init"
        Just stats -> addTiming (initiationTime stats) (initiationNum stats)
                      (ic3InitBackend cfg)
      --initiationBackend = initiationBackend' >>= namedDebugBackend "init"
      domainBackend = case stats of
        Nothing -> ic3DomainBackend cfg
        Just stats -> addTiming (domainTime stats) (domainNum stats)
                      (ic3DomainBackend cfg)
      --domainBackend = domainBackend' >>= namedDebugBackend "domain"
      interpBackend' = case stats of
        Nothing -> ic3InterpolationBackend cfg -- >>= namedDebugBackend "interp"
        Just stats -> addTiming (interpolationTime stats) (interpolationNum stats)
                      (ic3InterpolationBackend cfg)
  cons <- case consBackend of
    AnyBackend cr
      -> consecutionNew cr
          (do
              cur <- TR.createState mdl
              inp <- TR.createInput mdl
              TR.stateInvariant mdl cur inp >>= assert
              (nxt,real1) <- TR.createNextState mdl cur inp
                             (TR.startingProgress mdl)
              --assert (blockConstraint nxtBlks)
              (asserts1,real2) <- TR.declareAssertions (\_ -> defineVar) mdl cur inp real1
              (assumps1,real3) <- TR.declareAssumptions (\_ -> defineVar) mdl cur inp real2
              mapM_ assert asserts1
              mapM_ assert assumps1
              nxtInp <- TR.createInput mdl
              (asserts2,real1') <- TR.declareAssertions (\_ -> defineVar) mdl nxt nxtInp
                                   (TR.startingProgress mdl)
              (assumps2,real2') <- TR.declareAssumptions (\_ -> defineVar) mdl nxt nxtInp real1'
              TR.stateInvariant mdl nxt nxtInp >>= assert
              mapM_ assert assumps2
              return $ ConsecutionVars { consecutionInput = inp
                                       , consecutionNxtInput = nxtInp
                                       , consecutionState = cur
                                       , consecutionNxtState = nxt
                                       , consecutionNxtAsserts = asserts2 })
          (mkCompExpr (TR.initialState mdl) (TR.stateAnnotation mdl))
  lifting <- case liftingBackend of
    AnyBackend cr
     -> createSMTPool cr $ do
        setOption (ProduceUnsatCores True)
        cur <- TR.createStateVars (\tp rev -> declareVar tp) mdl
        inp <- TR.createInputVars (\tp rev -> declareVar tp) mdl
        TR.stateInvariant mdl cur inp >>= assert
        (nxt,real1) <- TR.declareNextState (\_ -> defineVar) mdl cur inp
                       (TR.startingProgress mdl)
        (assumps,real2) <- TR.declareAssumptions (\_ -> defineVar) mdl cur inp real1
        mapM_ assert assumps
        inp' <- TR.createInputVars (\tp rev -> declareVar tp) mdl
        (asserts,real1') <- TR.declareAssertions (\_ -> defineVar) mdl nxt inp'
                            (TR.startingProgress mdl)
        (assumps2,real2') <- TR.declareAssumptions (\_ -> defineVar) mdl nxt inp' real1'
        TR.stateInvariant mdl nxt inp' >>= assert
        mapM_ assert assumps2
        return $ LiftingState cur inp nxt inp' asserts
  initiation <- case initiationBackend of
    AnyBackend cr -> createSMTPool cr $ do
      cur <- TR.createStateVars (\tp rev -> declareVar tp) mdl
      TR.initialState mdl cur >>= assert
      --assert $ TR.stateInvariant mdl inp cur
      return (PoolVars cur)
  interpolation <- case interpBackend' of
    AnyBackend cr -> createSMTPool cr $ do
      setOption (SMTLogic "QF_AUFLIA")
      setOption (ProduceInterpolants True)
      setOption (ProduceModels True)
      cur <- TR.createState mdl
      inp <- TR.createInput mdl
      nxtInp <- TR.createInput mdl
      (nxt,real1) <- TR.createNextState mdl cur inp (TR.startingProgress mdl)
      (asserts,real2) <- TR.declareAssertions (const defineVar) mdl cur inp real1
      (assumps,real3) <- TR.declareAssumptions (const defineVar) mdl cur inp real2
      (nxt',rev) <- TR.createRevState mdl
      mapM_ (\assump -> assertPartition assump PartitionA
            ) assumps
      mapM_ (\ass -> assertPartition ass PartitionA
            ) asserts
      inv1 <- TR.stateInvariant mdl cur inp
      inv2 <- TR.stateInvariant mdl nxt' nxtInp
      eq <- eqComposite nxt' nxt
      assertPartition inv1 PartitionA
      assertPartition inv2 PartitionB
      assertPartition eq PartitionA
      return $ InterpolationState { interpCur = cur
                                  , interpNxt = nxt'
                                  , interpInputs = inp
                                  , interpNxtInputs = nxtInp
                                  , interpAsserts = asserts
                                  , interpReverse = rev
                                  }
  dom <- case domainBackend of
    AnyBackend cr -> Dom.initialDomain (ic3DebugLevel cfg) cr
                     (TR.stateAnnotation mdl)
  (initNode,_,dom') <- Dom.domainAdd (mkCompExpr (TR.initialState mdl) (TR.stateAnnotation mdl)) dom
  extractor <- TR.defaultPredicateExtractor mdl
  ref <- newIORef (IC3Env { ic3Domain = dom'
                          , ic3InitialProperty = initNode
                          , ic3Consecution = cons
                          , ic3Lifting = lifting
                          , ic3Initiation = initiation
                          , ic3Interpolation = interpolation
                          , ic3CexState = Nothing
                          , ic3LitOrder = Map.empty
                          , ic3Earliest = 0
                          , ic3PredicateExtractor = extractor
                          , ic3Stats = stats
                          })
  evalIC3 act cfg ref

extractState :: (Backend b,PartialComp inp,PartialComp st)
                => Maybe (IORef (State inp st))
                -> ConsecutionVars inp st (Expr b)
                -> SMT b (State inp st)
extractState (succ::Maybe (IORef (State inp st))) vars = do
  inps <- unliftComp getValue (consecutionInput vars)
  nxtInps <- unliftComp getValue (consecutionNxtInput vars)
  full <- unliftComp getValue (consecutionState vars)
  return $ State { stateSuccessor = succ
                 , stateLiftedAst = Nothing
                 , stateFullAst = Nothing
                 , stateFull = full
                 , stateInputs = inps
                 , stateNxtInputs = nxtInps
                 , stateLifted = unmaskValue (Proxy::Proxy st) full
                 , stateLiftedInputs = unmaskValue (Proxy::Proxy inp) inps
                 , stateSpuriousLevel = 0
                 , stateNSpurious = 0
                 , stateSpuriousSucc = False
                 , stateDomainHash = 0 }

liftState :: (TR.TransitionRelation mdl)
             => Lifting mdl -> State (TR.Input mdl) (TR.State mdl)
             -> IO (State (TR.Input mdl) (TR.State mdl))
liftState lifting st = do
  rsuc <- case stateSuccessor st of
    Nothing -> return Nothing
    Just succ -> do
      succ' <- readIORef succ
      return $ Just succ'
  (part,partInp) <- withSMTPool lifting $
                    \vars' -> do
                      next <- case rsuc of
                        Nothing -> and' (liftNxtAsserts vars')
                        Just succ -> do
                          conj <- fmap catMaybes $
                                  assignPartial assignEq
                                    (liftNxt vars') (stateLifted succ)
                          not' $ and' conj
                      lift' (liftCur vars')
                        (liftInputs vars')
                        (liftNxtInputs vars')
                        (stateFull st)
                        (stateInputs st)
                        (stateNxtInputs st)
                        next
  return $ st { stateLifted = part
              , stateLiftedInputs = partInp }

lift' :: (Backend b,PartialComp st,PartialComp inp)
      => st (Expr b)
      -> inp (Expr b)
      -> inp (Expr b)
      -> Unpacked st
      -> Unpacked inp
      -> Unpacked inp
      -> Expr b BoolType
      -> SMT b (Partial st,Partial inp)
lift' (cur::st (Expr b)) (inp::inp (Expr b)) inp' vcur vinp vinp' vnxt = stack $ do
  assignedCur <- assignUnpacked cur vcur
  assignedInp <- assignUnpacked inp vinp
  --comment "State:"
  (cmp1,len_st) <- foldlM (\(mp,n) cond -> case cond of
                            Nothing -> return (mp,n+1)
                            Just cond' -> do
                              cid <- assertId cond'
                              return (Map.insert cid (Left n) mp,n+1)
                          ) (Map.empty,0) assignedCur
  --comment "Input:"
  (cmp2,len_inp) <- foldlM (\(mp,n) cond -> case cond of
                             Nothing -> return (mp,n+1)
                             Just cond' -> do
                               cid <- assertId cond'
                               return (Map.insert cid (Right n) mp,n+1)
                           ) (cmp1,0) assignedInp
  --assert $ argEq inp (liftArgs vinp (extractArgAnnotation inp))
  --assert $ argEq inp' (liftArgs vinp' (extractArgAnnotation inp'))
  --comment "Next state:"
  assert vnxt
  res <- checkSat
  when (res/=Unsat) $ error $ "The model appears to be non-deterministic."
  core <- getUnsatCore
  let (coreSt,coreInp) = partitionEithers $ fmap (cmp2 Map.!) core
      partSt = toTruthValues len_st 0 (sort coreSt)
      partInp = toTruthValues len_inp 0 (sort coreInp)
      vcur' = unmaskValue (Proxy::Proxy st) vcur
      vinp' = unmaskValue (Proxy::Proxy inp) vinp
      (vcur'',[]) = maskValue (Proxy::Proxy st) vcur' partSt
      (vinp'',[]) = maskValue (Proxy::Proxy inp) vinp' partInp
  return (vcur'',vinp'')
  where
    toTruthValues len n []
      | n==len = []
      | otherwise = False:toTruthValues len (n+1) []
    toTruthValues len n (x:xs)
      = if n==x
        then True:toTruthValues len (n+1) xs
        else False:toTruthValues len (n+1) (x:xs)
    assignUnpacked :: (PartialComp a,Backend b) => a (Expr b) -> Unpacked a
                   -> SMT b [Maybe (Expr b BoolType)]
    assignUnpacked (var::a (Expr b)) val
      = assignPartial assignEq var (unmaskValue (Proxy::Proxy a) val)

-- | Check if the abstract state intersects with the initial condition
initiationAbstract :: TR.TransitionRelation mdl => Dom.AbstractState (TR.State mdl) -> IC3 mdl Bool
initiationAbstract state = do
  env <- get
  liftIO $ withSMTPool (ic3Initiation env) $
    \(PoolVars vars) -> stack $ do
      --comment $ "initiation abstract: "++show state
      Dom.toDomainTerm state (ic3Domain env) vars >>= assert
      fmap (==Unsat) checkSat

initiationConcrete :: TR.TransitionRelation mdl => Partial (TR.State mdl) -> IC3 mdl Bool
initiationConcrete vals = do
  env <- get
  liftIO $ withSMTPool (ic3Initiation env) $
    \(PoolVars vars) -> stack $ do
      eqs <- assignPartial assignEq vars vals
      mapM_ assert (catMaybes eqs)
      fmap (==Unsat) checkSat

-- From ConsRefConcrPred
-- XXX: Henning: Use full state to abstract domain
updateAbstraction :: TR.TransitionRelation mdl
                     => IORef (State (TR.Input mdl) (TR.State mdl)) -> IC3 mdl Bool
updateAbstraction ref = do
  st <- liftIO $ readIORef ref
  dom <- gets ic3Domain
  mdl <- asks ic3Model
  initialPred <- gets ic3InitialProperty
  succUpdated <- case stateSuccessor st of
    Nothing -> return False
    Just succ -> updateAbstraction succ
  if (not succUpdated) &&
     (stateDomainHash st == Dom.domainHash dom)
    then return False
    else (do
             let {-concr = mkCompExpr (\x -> do
                                        eqs <- fmap catMaybes $
                                               assignPartial assignEq x (stateLifted st)
                                        and' eqs
                                    ) (TR.stateAnnotation mdl)-}
                 concrFull = mkCompExpr (\x -> do
                                            rst <- liftComp (stateFull st)
                                            eqComposite x rst
                                        ) (TR.stateAnnotation mdl)
             full <- liftIO $ Dom.domainAbstract concrFull
                     initialPred
                     dom
             lifted <- case stateSuccessor st of
               Nothing -> lift full (stateInputs st) (stateNxtInputs st) Nothing
               Just succ -> do
                 succ' <- liftIO $ readIORef succ
                 lift full (stateInputs st) (stateNxtInputs st) (Just $ bestAbstraction succ')
             liftIO $ writeIORef ref $ st { stateDomainHash = Dom.domainHash dom
                                          , stateFullAst = Just full
                                          , stateLiftedAst = lifted
                                          }
             return True)

lift :: (TR.TransitionRelation mdl,
         LiftComp (TR.Input mdl))
        => Dom.AbstractState (TR.State mdl)
        -> Unpacked (TR.Input mdl)
        -> Unpacked (TR.Input mdl)
        -> Maybe (Dom.AbstractState (TR.State mdl))
        -> IC3 mdl (Maybe (Dom.AbstractState (TR.State mdl)))
lift toLift inps nxtInps succ = do
  lifting <- gets ic3Lifting
  domain <- gets ic3Domain
  initProp <- gets ic3InitialProperty
  mdl <- asks ic3Model
  liftAbs <- liftIO $ withSMTPool lifting $ \st -> stack $ do
    trms <- Dom.toDomainTerms toLift domain (liftCur st)
    (_,rev) <- foldlM (\(i,mp) (nd,e,act) -> do
                          cond <- if act
                                  then return e
                                  else not' e
                          cid <- assertId cond
                          return (i+1,Map.insert cid i mp)
                      ) (0,Map.empty) trms
    liftedInps <- liftComp inps
    eqComposite (liftInputs st) liftedInps >>= assert
    --assert $ argEq (liftNxtInputs st) (liftArgs nxtInps (TR.annotationInput mdl))
    case succ of
      Nothing -> and' (liftNxtAsserts st) >>= assert
      Just succ_abstr -> do
        trm <- Dom.toDomainTerm succ_abstr domain (liftNxt st)
        not' trm >>= assert
    res <- checkSat
    if res==Sat
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

{- | Checks if an abstract state is inductive at a given level.
     This is done by searching for a solution for F_i and (not s) and T and next(s).
     If the formula is unsatisfiable, we return a possible smaller state that is still inductive
     by extracting the unsatisfiable core of the formula. This state 't' is returned as
     'Left t'.
     If the formula is satisfiable, we can extract a counter-example state by extracting
     a valuation of 's'. This counter-example state is returned via the 'Right' constructor.
 -}
abstractConsecution :: TR.TransitionRelation mdl
                       => Int -- ^ The level 'i'
                       -> Dom.AbstractState (TR.State mdl) -- ^ The possibly inductive abstract state 's'
                       -> Maybe (IORef (State (TR.Input mdl) (TR.State mdl)))
                       -> IC3 mdl (Either (Dom.AbstractState (TR.State mdl))
                                   (State (TR.Input mdl) (TR.State mdl))
                                  )
abstractConsecution fi abs_st succ = do
  --rebuildConsecution
  --modify (\env -> env { ic3ConsecutionCount = (ic3ConsecutionCount env)+1 })
  ic3DebugAct 3 $ do
    abs_st_str <- renderAbstractState abs_st
    liftIO $ hPutStrLn stderr ("Original abstract state: "++abs_st_str)
  env <- get
  res <- liftIO $ consecutionPerform (ic3Domain env) (ic3Consecution env) fi $ \vars -> do
    trm <- Dom.toDomainTerm abs_st (ic3Domain env) (consecutionState vars)
    not' trm >>= assert
    trms <- Dom.toDomainTerms abs_st (ic3Domain env)
            (consecutionNxtState vars)
    (_,rev) <- foldlM (\(i,mp) (nd,e,act) -> do
                          e' <- if act
                                then return e
                                else not' e
                          cid <- assertId e'
                          return (i+1,Map.insert cid i mp)
                      ) (0,Map.empty) trms
    -- Henning: This tries to take the lifted inputs of the successor into account (doesn't do anything yet)
    {-case succ of
     Nothing -> return ()
     Just s -> do
       succ' <- liftIO $ readIORef s
       assert $ app and' $ assignPartial' (consecutionNxtInput vars)
         (stateLiftedInputs succ')-}
    res <- checkSat
    if res==Sat
      then (do
               st <- extractState succ vars
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
      ic3DebugAct 3 $ do
        abs_st_str <- renderAbstractState absCore'
        liftIO $ hPutStrLn stderr ("Reduced abstract state: "++abs_st_str)
      --absInit' <- initiationAbstract absCore'
      --error $ "abstractConsecution core: "++show absCore'++" "++show absInit'
      return $ Left absCore'

concreteConsecution :: TR.TransitionRelation mdl
                       => Int -> Partial (TR.State mdl)
                       -> IORef (State (TR.Input mdl) (TR.State mdl))
                       -> IC3 mdl (Maybe (IORef (State (TR.Input mdl) (TR.State mdl))))
concreteConsecution fi st succ = do
  env <- get
  res <- liftIO $ consecutionPerform (ic3Domain env) (ic3Consecution env) fi $ \vars -> do
    eqs <- fmap catMaybes $ assignPartial assignEq (consecutionState vars) st
    not' (and' eqs) >>= assert
    {-do
      succ' <- liftIO $ readIORef succ
      assert $ app and' $ assignPartial' (consecutionNxtInput vars)
        (stateLiftedInputs succ')-}
    eqs' <- assignPartial assignEq (consecutionNxtState vars) st
    mapM_ assert (catMaybes eqs')
    sat <- checkSat
    if sat==Sat
      then (do
               rst <- extractState (Just succ) vars
               return $ Just rst)
      else return Nothing
  case res of
   Nothing -> return Nothing
   Just st -> do
     res' <- liftIO $ liftState (ic3Lifting env) st >>= newIORef
     return $ Just res'

handleObligations :: TR.TransitionRelation mdl
                     => Queue (TR.Input mdl) (TR.State mdl) -> IC3 mdl Bool
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
          ic3Debug 4 "Abstract counter-example found."
          concConsRes <- concreteConsecution (oblLevel obl) (stateLifted rst) (oblState obl)
          case concConsRes of
            Nothing -> do
              ic3Debug 4 "No corresponding concrete counter-example found."
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
                      ic3Debug 4 "Eliminating spurious counter-example."
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
      if n <= tk
        then handleObligations (Queue.insert (obl { oblLevel = n }) obls)
        else (do
                 updateStats (\stats -> stats { numErased = (numErased stats)+1 })
                 oblState <- liftIO $ readIORef (oblState obl)
                 case stateLiftedAst oblState of
                  Nothing -> updateStats (\stats -> stats { numUnliftedErased = (numUnliftedErased stats)+1 })
                  Just _ -> return ()
                 handleObligations obls)

removeObligations :: IORef (State inp st)
                     -> Int
                     -> Queue inp st
                     -> IC3 mdl (Queue inp st)
removeObligations st depth obls
  = return $ Queue.filter (\obl -> oblState obl /= st ||
                                   oblDepth obl /= depth
                          ) obls

backtrackRefine :: TR.TransitionRelation mdl
                   => Obligation (TR.Input mdl) (TR.State mdl)
                   -> Queue (TR.Input mdl) (TR.State mdl)
                   -> Bool
                   -> IC3 mdl (Queue (TR.Input mdl) (TR.State mdl))
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

abstractGeneralize :: TR.TransitionRelation mdl
                      => Int -> Dom.AbstractState (TR.State mdl)
                      -> IC3 mdl Int
abstractGeneralize level cube = do
  ic3DebugAct 3 $ do
    cubeStr <- renderAbstractState cube
    liftIO $ hPutStrLn stderr $ "mic: "++cubeStr
  ncube <- mic level cube
  ic3DebugAct 3 $ do
    ncubeStr <- renderAbstractState ncube
    liftIO $ hPutStrLn stderr $ "mic done: "++ncubeStr
  pushForward (level+1) ncube
  where
    pushForward level cube = do
      tk <- k
      if level <= tk
        then (do
                 consRes <- abstractConsecution level cube Nothing
                 case consRes of
                   Left ncube -> pushForward (level+1) ncube
                   Right _ -> addCube level cube)
        else addCube level cube
    addCube level cube = do
      ic3DebugAct 3 $ do
        cubeStr <- renderAbstractState cube
        liftIO $ hPutStrLn stderr $ "Adding cube at level "++show level++": "++cubeStr
      addAbstractCube level cube
      return level

baseCases :: (TR.TransitionRelation mdl,Backend b)
             => mdl -> SMT b (Maybe [(Unpacked (TR.State mdl),
                                      Unpacked (TR.Input mdl))])
baseCases st = do
  --comment "State:"
  cur0 <- TR.createStateVars (\tp rev -> declareVar tp) st
  --comment "Inputs:"
  inp0 <- TR.createInputVars (\tp rev -> declareVar tp) st
  TR.initialState st cur0 >>= assert
  --comment "Assumptions:"
  (assumps0,real0) <- TR.declareAssumptions (const defineVar) st cur0 inp0
                      (TR.startingProgress st)
  mapM_ assert assumps0
  --comment "Invariant:"
  TR.stateInvariant st cur0 inp0 >>= assert
  --comment "Declare assertions:"
  (asserts0,real1) <- TR.declareAssertions (const defineVar) st cur0 inp0 real0
  --comment "Declare next state:"
  (cur1,real2) <- TR.declareNextState (const defineVar) st cur0 inp0 real1
  --comment "Inputs 2:"
  inp1 <- TR.createInputVars (\tp rev -> declareVar tp) st
  --comment "Assumptions 2:"
  (assumps1,real0) <- TR.declareAssumptions (const defineVar) st cur1 inp1
                      (TR.startingProgress st)
  --comment "Invariant 2:"
  TR.stateInvariant st cur1 inp1 >>= assert
  mapM_ assert assumps1
  --comment "Declare assertions 2:"
  (asserts1,_) <- TR.declareAssertions (const defineVar) st cur1 inp1 real0
  not' (and' $ asserts0++asserts1) >>= assert
  res <- checkSat
  if res==Sat
    then (do
             succ0 <- mapM getValue asserts0
             if not $ and [ v | BoolValue v <- succ0 ]
               then (do
                        rcur0 <- unliftComp getValue cur0
                        rinp0 <- unliftComp getValue inp0
                        return (Just [(rcur0,rinp0)]))
               else (do
                        rcur0 <- unliftComp getValue cur0
                        rinp0 <- unliftComp getValue inp0
                        rcur1 <- unliftComp getValue cur1
                        rinp1 <- unliftComp getValue inp1
                        return (Just [(rcur0,rinp0),(rcur1,rinp1)])))
    else return Nothing

extend :: TR.TransitionRelation mdl => IC3 mdl ()
extend = modify (\env -> env { ic3Consecution = extendFrames (ic3Consecution env) })

-- | Strengthens frontier to remove error successors
--   Returns 'Nothing' if strengthening failed
--   Returns 'Just False' if cubes were generated
--   Returns 'Just True' if no cubes were generated
strengthen :: TR.TransitionRelation mdl
              => IC3 mdl (Maybe Bool)
strengthen = strengthen' True
  where
    strengthen' trivial = do
      tk <- k
      env <- get
      ic3Debug 2 $ "Trying to get from frontier at level "++show tk++" to error"
      rv <- liftIO $ consecutionPerform (ic3Domain env) (ic3Consecution env) tk $ \vars -> do
        not' (and' $ consecutionNxtAsserts vars) >>= assert
        sat <- checkSat
        if sat==Sat
          then (do
                   sti <- extractState Nothing vars
                   return $ Just sti)
          else return Nothing
      case rv of
       Just sti -> do
         sti' <- liftIO $ liftState (ic3Lifting env) sti
         sti'' <- liftIO $ newIORef sti'
         let obl = Obligation sti'' (tk-1) 1
             queue = Queue.singleton obl
         updateStats (\stats -> stats { numCTI = (numCTI stats)+1 })
         --ic3Debug 2 ("Enqueuing obligation "++show sti++" at level "++
         --            show (tk-1)++" and depth 1")
         res <- handleObligations queue
         if res
           then strengthen' False
           else return Nothing
       Nothing -> do
         ic3Debug 2 $ "Can't get to error ("++
           (if trivial
            then "trivial"
            else "not trivial")++")"
         return $ Just trivial

check :: TR.TransitionRelation mdl
         => mdl
         -> BackendOptions
         -> Int -- ^ Verbosity
         -> Bool -- ^ Dump stats?
         -> Maybe String -- ^ Dump domain?
         -> Maybe String -- ^ Dump stats?
         -> Maybe String -- ^ Dump states?
         -> IO (Either [(Unpacked (TR.State mdl),
                         Unpacked (TR.Input mdl))]
                       (CompositeExpr (TR.State mdl) BoolType))
check st opts verb stats dumpDomain dumpstats dumpstates = do
  runIC3 (mkIC3Config st opts verb stats dumpDomain dumpstats dumpstates) $ do
    backend <- asks ic3BaseBackend
    tr <- liftIO $ withAnyBackend backend (baseCases st)
    case tr of
      Just tr' -> do
        ic3DumpStats Nothing
        return (Left tr')
      Nothing -> (do
                      addSuggestedPredicates
                      extend
                      extend
                      res <- checkIt
                      ic3DumpStats (case res of
                                      Left _ -> Nothing
                                      Right fp -> Just fp)
                      case res of
                        Left tr -> return (Left tr)
                        Right fp -> do
                          dom <- gets ic3Domain
                          return $ Right $ renderFixpoint dom fp
                 ) `ic3Catch` (\ex -> do
                                   ic3DumpStats Nothing
                                   throw (ex::SomeException))
  where
    checkIt :: TR.TransitionRelation mdl
            => IC3 mdl (Either [(Unpacked (TR.State mdl),
                                 Unpacked (TR.Input mdl))]
                        [Dom.AbstractState (TR.State mdl)])
    checkIt = do
      ic3DebugAct 1 (do
                        lvl <- k
                        liftIO $ hPutStrLn stderr $ "Level "++show lvl)
      extend
      sres <- strengthen
      case sres of
        Nothing -> do
          real <- asks ic3Model
          cex <- gets ic3CexState
          tr <- liftIO $ getWitnessTr cex
          res <- liftIO $ do
            withBackendExitCleanly (createPipe "z3" ["-in","-smt2"]) $ do
              st0 <- TR.createStateVars (\tp rev -> declareVar tp) real
              TR.initialState real st0 >>= assert
              tr' <- constructTrace real st0 tr []
              rv <- checkSat
              if rv==Sat
                then (do
                         tr'' <- getWitness real tr'
                         return (Just tr''))
                else return Nothing
          case res of
           Nothing -> do
             rtr <- mapM renderState tr
             error $ "Error trace is infeasible:\n"++unlines rtr
           Just res' -> return (Left res')
        Just trivial -> do
          pres <- propagate trivial
          if pres==0
            then checkIt
            else (do
                     fp <- getAbstractFixpoint pres
                     checkFixpoint fp
                     return (Right fp))
    getWitnessTr Nothing = return []
    getWitnessTr (Just st) = do
      rst <- readIORef st
      rest <- getWitnessTr (stateSuccessor rst)
      return $ (stateLifted rst):rest
    constructTrace :: (TR.TransitionRelation mdl,Backend b)
                   => mdl -> TR.State mdl (Expr b)
                   -> [Partial (TR.State mdl)]
                   -> [Expr b BoolType]
                   -> SMT b [(TR.State mdl (Expr b),TR.Input mdl (Expr b))]
    constructTrace real st [] errs = do
      inps <- TR.createInputVars (\tp rev -> declareVar tp) real
      (assumps,real0) <- TR.declareAssumptions (const defineVar) real st inps
                         (TR.startingProgress real)
      (ass,_) <- TR.declareAssertions (const defineVar) real st inps real0
      --comment "Invariant"
      TR.stateInvariant real st inps >>= assert
      --comment "Assumptions"
      mapM_ assert assumps
      --comment "Assertions"
      not' (and' $ ass++errs) >>= assert
      return [(st,inps)]
    constructTrace real st (x:xs) asserts = do
      --comment "Assignments"
      eqs <- assignPartial assignEq st x
      mapM_ assert (catMaybes eqs)
      --comment "Inputs"
      inps <- TR.createInputVars (\tp rev -> declareVar tp) real
      --comment "Invariant"
      TR.stateInvariant real st inps >>= assert
      (assumps,real0) <- TR.declareAssumptions (const defineVar) real st inps
                         (TR.startingProgress real)
      (nxt_st,real1) <- TR.declareNextState (const defineVar) real st inps real0
      (ass,real2) <- TR.declareAssertions (const defineVar) real st inps real1
      --comment "Assumptions"
      and' assumps >>= assert
      rest <- constructTrace real nxt_st xs (ass++asserts)
      return ((st,inps):rest)
    getWitness _ [] = return []
    getWitness real ((x1,x2):xs) = do
      concr1 <- unliftComp getValue x1
      concr2 <- unliftComp getValue x2
      concrs <- getWitness real xs
      return $ (concr1,concr2):concrs

getFixpoint :: (Embed m e,GetType e,Composite st)
            => Dom.Domain st -> [Dom.AbstractState st] -> st e
            -> m (e BoolType)
getFixpoint domain sts inp = do
  terms <- mapM (\st -> do
                    trm <- Dom.toDomainTerm st domain inp
                    not' trm) sts
  and' terms

renderFixpoint :: (Composite st) => Dom.Domain st -> [Dom.AbstractState st]
               -> CompositeExpr st BoolType
renderFixpoint dom fp = runReader (getFixpoint dom fp arg >>= simplify ()) descr
  where
    descr = Dom.domainDescr dom
    arg = runIdentity $ createComposite
          (\_ rev -> return (CompositeExpr descr (E.Var rev))) descr

getAbstractFixpoint :: Int -> IC3 mdl [Dom.AbstractState (TR.State mdl)]
getAbstractFixpoint level = do
  cons <- gets ic3Consecution
  let frames = consecutionFrames cons
      fpFrames = Vec.drop level frames
  return [ getCube st cons
         | frame <- Vec.toList fpFrames
         , st <- IntSet.toList frame ]

propagate :: TR.TransitionRelation mdl
             => Bool -> IC3 mdl Int
propagate trivial = do
  earliest <- gets ic3Earliest
  tk <- k
  --ic3Debug 5 $ "Before propagation: "++(show frames)
  modify $
    \env -> let cons = ic3Consecution env
                frames = consecutionFrames cons
                (pre,oframes) = Vec.splitAt (earliest-1) frames
                (_,nframes) = mapAccumR (\all frame
                                         -> let rem = IntSet.difference frame all
                                            in (IntSet.union all rem,rem)
                                        ) IntSet.empty (Vec.drop (earliest-1) oframes)
                frames1 = pre Vec.++ nframes
                ncons = cons { consecutionFrames = frames1
                             , consecutionFrameHash = succ (consecutionFrameHash cons) }
            in env { ic3Consecution = ncons }
  pushCubes (if trivial
             then [tk]
             else [1..tk])
  where
    pushCubes [] = return 0
    pushCubes (i:is) = do
      cubes <- gets ((Vec.! i).consecutionFrames.ic3Consecution)
      ncubes <- foldlM (\keep cube -> do
                           cons <- gets ic3Consecution
                           consRes <- abstractConsecution i (getCube cube cons) Nothing
                           case consRes of
                             Left core -> do
                               modify $
                                 \env -> env { ic3Consecution = addCubeAtLevel cube (i+1) cons
                                             }
                               return keep
                             Right _ -> return $ IntSet.insert cube keep
                       ) IntSet.empty (IntSet.toList cubes)
      modify $
        \env -> let cons = ic3Consecution env
                    frames = consecutionFrames cons
                    ncons = cons { consecutionFrames = frames Vec.// [(i,ncubes)] }
                in env { ic3Consecution = ncons }
      if IntSet.null ncubes
        then return i
        else pushCubes is

predecessor :: TR.TransitionRelation mdl
               => Obligation (TR.Input mdl) (TR.State mdl)
               -> Queue (TR.Input mdl) (TR.State mdl)
               -> IORef (State (TR.Input mdl) (TR.State mdl))
               -> IC3 mdl (Maybe (Queue (TR.Input mdl) (TR.State mdl)))
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

elimSpuriousTrans :: TR.TransitionRelation mdl
                     => IORef (State (TR.Input mdl) (TR.State mdl)) -> Int
                     -> IC3 mdl ()
elimSpuriousTrans st level = do
  mdl <- asks ic3Model
  rst <- liftIO $ readIORef st
  backend <- asks ic3BaseBackend
  extr <- gets ic3PredicateExtractor
  mbDumpStatesFile <- asks ic3DumpStatesFile
  (nextr,props) <- TR.extractPredicates mdl extr
                   (stateFull rst)
                   (stateLifted rst)
                   mbDumpStatesFile
  modify $ \env -> env { ic3PredicateExtractor = nextr }
  updateStats (\stats -> stats { numRefinements = (numRefinements stats)+1
                               , numAddPreds = (numAddPreds stats)+(length props) })
  interp <- interpolateState level (stateLifted rst) (stateLiftedInputs rst)
  ic3Debug 4 $ "mined new predicates: " ++ (show props)
  ic3Debug 4 $ "computed interpolant: " ++ (show interp)
  domain <- gets ic3Domain
  order <- gets ic3LitOrder
  (ndomain,norder) <- foldlM (\(cdomain,corder) trm
                              -> do
                                (nd,isNew,ndom) <- liftIO $ Dom.domainAdd trm cdomain
                                let nord = if isNew
                                           then addOrderElement nd corder
                                           else corder
                                return (ndom,nord)
                             ) (domain,order) (interp++props)
  --liftIO $ domainDump ndomain >>= putStrLn
  modify $ \env -> env { ic3Domain = ndomain
                       , ic3LitOrder = norder }

interpolateState :: TR.TransitionRelation mdl => Int
                 -> Partial (TR.State mdl)
                 -> Partial (TR.Input mdl)
                 -> IC3 mdl [CompositeExpr (TR.State mdl) BoolType]
interpolateState j s inp = do
  env <- get
  cfg <- ask
  liftIO $ withSMTPool (ic3Interpolation env) $
    \st -> stack $ do
      comment $ "Interpolating at level "++show j
      if j==0
        then TR.initialState (ic3Model cfg) (interpCur st) >>=
             \init -> assertPartition init PartitionA
        else (do
                 let cons = ic3Consecution env
                     frames = Vec.drop j (consecutionFrames cons)
                 mapM_ (\fr -> mapM_ (\st_id -> do
                                         let ast = getCube st_id cons
                                         trm <- Dom.toDomainTerm ast (ic3Domain env)
                                                (interpCur st)
                                         not' trm
                                           >>= \trm' -> assertPartition trm' PartitionA
                                     ) (IntSet.toList fr)
                       ) frames)
      fmap catMaybes (assignPartial assignEq (interpCur st) s) >>=
        \eqs -> not' (and' eqs)
        >>= \eqs' -> assertPartition eqs' PartitionA
      fmap catMaybes (assignPartial assignEq (interpNxt st) s) >>=
        \eqs -> and' eqs
        >>= \eqs' -> assertPartition eqs' PartitionB
      res <- checkSat
      when (res==Sat) $ do
        curSt <- fmap (TR.renderState (ic3Model cfg)) $ unliftComp getValue (interpCur st)
        curInpSt <- fmap (TR.renderInput (ic3Model cfg)) $ unliftComp getValue (interpInputs st)
        nxtSt <- fmap (TR.renderState (ic3Model cfg)) $ unliftComp getValue (interpNxt st)
        error $ "Interpolation query is SAT.\nState:\n"++
          curSt++"\nInput:\n"++curInpSt++"\nNext state:\n"++nxtSt
      interp <- getInterpolant
      cleaned <- cleanInterpolant DMap.empty interp
      relativized <- relativizeExpr (TR.stateAnnotation $ ic3Model cfg) (interpReverse st) cleaned
      let negated = negateInterpolant relativized
      comment $ "Negated interpolant: "++show negated
      let splitted = splitInterpolant negated
      mapM (\interp -> comment $ "Split interpolant: "++show interp) splitted
      return splitted
  where
    cleanInterpolant :: (Backend b)
                     => DMap (LVar b) (Expr b)
                     -> Expr b tp
                     -> SMT b (Expr b tp)
    cleanInterpolant mp e = do
      re <- getExpr e
      case re of
        E.LVar v -> case DMap.lookup v mp of
          Just res -> return res
        E.Let args body -> do
          nmp <- List.foldM (\cmp bind -> do
                                nexpr <- cleanInterpolant cmp (E.letExpr bind)
                                return $ DMap.insert (E.letVar bind) nexpr cmp
                            ) mp args
          cleanInterpolant nmp body
        Divisible n x -> do
          nx <- cleanInterpolant mp x
          (mod' nx (cint n)) .==. (cint 0)
        Neg x -> do
          nx <- cleanInterpolant mp x
          neg nx
        Arith op (x ::: Nil)
          -> cleanInterpolant mp x
        Ord op x@(getType -> RealRepr) y -> do
          rx <- cleanInterpolant mp x
          ry <- cleanInterpolant mp y
          nx <- removeToReal rx
          case nx of
            Nothing -> ord op rx ry
            Just x' -> do
              ny <- removeToReal ry
              case ny of
                Nothing -> ord op rx ry
                Just y' -> ord op x' y'
        E.App fun args -> do
          nargs <- List.mapM (cleanInterpolant mp) args
          app fun nargs
        _ -> return e

    removeToReal :: (Backend b) => Expr b RealType -> SMT b (Maybe (Expr b IntType))
    removeToReal e = do
      e' <- getExpr e
      case e' of
        ToReal x -> return (Just x)
        _ -> return Nothing

    negateInterpolant :: Composite a => CompositeExpr a BoolType
                      -> CompositeExpr a BoolType
    negateInterpolant e = case compositeExpr e of
      Not x -> pushNegation x
      AndLst es -> e { compositeExpr = OrLst (fmap negateInterpolant es) }
      OrLst es -> e { compositeExpr = AndLst (fmap negateInterpolant es) }
      l :>=: r -> e { compositeExpr = l :<: r }
      l :>: r -> e { compositeExpr = l :<=: r }
      l :<=: r -> e { compositeExpr = l :>: r }
      l :<: r -> e { compositeExpr = l :>=: r }
      x :==: y -> e { compositeExpr = x :/=: y }
      x :/=: y -> e { compositeExpr = x :==: y }
      _ -> e { compositeExpr = Not e }

    pushNegation :: Composite a => CompositeExpr a BoolType
                 -> CompositeExpr a BoolType
    pushNegation e = case compositeExpr e of
      Not x -> negateInterpolant x
      LogicLst op xs -> e { compositeExpr = LogicLst op (fmap pushNegation xs) }
      _ -> e

    splitInterpolant :: Composite a => CompositeExpr a BoolType
                     -> [CompositeExpr a BoolType]
    splitInterpolant e = case compositeExpr e of
      AndLst es -> concat $ fmap splitInterpolant es
      -- Henning: Maybe it's a good idea not to refine with equalities:
      EqLst args@(x:_) -> case getType x of
        IntRepr -> splitEqs args
        _ -> [e]
      DistinctLst args@(x:_) -> case getType x of
        IntRepr -> splitEqs args
        _ -> [e]
      x :>=: y -> [e { compositeExpr = x :>=: y }
                  ,e { compositeExpr = x :>: y }]
      _ -> [e]

    splitEqs :: (Composite a) => [CompositeExpr a IntType]
             -> [CompositeExpr a BoolType]
    splitEqs [] = []
    splitEqs (x:xs)
      = concat (fmap (\x' -> [x { compositeExpr = x :<=: x' }
                             ,x { compositeExpr = x :==: x' }]
                     ) xs) ++
        (splitEqs xs)

mic :: TR.TransitionRelation mdl
       => Int -> Dom.AbstractState (TR.State mdl)
       -> IC3 mdl (Dom.AbstractState (TR.State mdl))
mic level ast = do
  updateStats (\stats -> stats { numMIC = (numMIC stats)+1 })
  mic' level ast 1

mic' :: TR.TransitionRelation mdl
        => Int -> Dom.AbstractState (TR.State mdl) -> Int
        -> IC3 mdl (Dom.AbstractState (TR.State mdl))
mic' level ast recDepth = do
  order <- gets ic3LitOrder
  attempts <- asks ic3MicAttempts
  let sortedAst = Vec.fromList $ sortBy (\(k1,_) (k2,_)
                                         -> compareOrder order k1 k2) $
                  Vec.toList ast
  mic'' sortedAst 0 attempts
  where
    mic'' ast _ 0 = do
      updateStats (\stats -> stats { numAbortMic = (numAbortMic stats)+1 })
      return ast
    mic'' ast i attempts
      | i >= Vec.length ast = return ast
      | otherwise = do
        let (before,after) = Vec.splitAt i ast
            cp = before Vec.++ (Vec.tail after)
        maxCTGs <- asks ic3MaxCTGs
        downRes <- ctgDown level cp i recDepth maxCTGs
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

ctgDown :: TR.TransitionRelation mdl
           => Int -> Dom.AbstractState (TR.State mdl) -> Int -> Int -> Int
           -> IC3 mdl (Maybe (Dom.AbstractState (TR.State mdl)))
ctgDown = ctgDown' 0 0
  where
    ctgDown' ctgs joins level ast keepTo recDepth efMaxCTGs = do
      cfg <- ask
      ic3Debug 5 ("ctgDown' ctgs="++
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
                         Left nast -> do
                           modify (\env -> case ic3Stats env of
                                    Nothing -> env
                                    Just stats -> if ast/=nast
                                                  then env { ic3Stats = Just (stats { numCoreReduced = (numCoreReduced stats)+1 }) }
                                                  else env)
                           return $ Just nast
                         Right _ -> return Nothing)
              else (do
                       res <- abstractConsecution level ast Nothing
                       case res of
                         Left core -> return (Just core)
                         Right ctg -> do
                           domain <- gets ic3Domain
                           initialPred <- gets ic3InitialProperty
                           let concr = mkCompExpr (\x -> do
                                                      eqs <- fmap catMaybes $
                                                             assignPartial assignEq x
                                                               (stateLifted ctg)
                                                      and' eqs
                                                  ) (TR.stateAnnotation $ ic3Model cfg)
                           abstractCtg <- liftIO $ Dom.domainAbstract concr
                                          initialPred domain
                           if ctgs < efMaxCTGs && level > 1
                             then (do
                                      init <- initiationAbstract abstractCtg
                                      if init
                                        then (do
                                                 res' <- abstractConsecution (level-1) abstractCtg Nothing
                                                 case res' of
                                                   Left ctgCore -> do
                                                     updateStats (\stats -> stats { numCTG = (numCTG stats)+1 })
                                                     pushForward ctgs joins level ast keepTo recDepth efMaxCTGs ctgCore level
                                                   Right _ -> checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg)
                                        else checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg)
                             else checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg))
    checkJoins ctgs joins level ast keepTo recDepth efMaxCTGs abstractCtg = do
      cfg <- ask
      if joins < ic3MaxJoins cfg
        then (case joined of
                 Nothing -> do
                   updateStats (\stats -> stats { numAbortJoin = (numAbortJoin stats)+1 })
                   return Nothing
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

addAbstractCube :: Int -> Dom.AbstractState (TR.State mdl) -> IC3 mdl ()
addAbstractCube lvl st
  = modify (\env -> let (st_id,cons') = getCubeId st (ic3Consecution env)
                        cons'' = addCubeAtLevel st_id lvl cons'
                    in env { ic3Consecution = cons''
                           , ic3Earliest = min (ic3Earliest env) lvl
                           , ic3LitOrder = updateOrder st (ic3LitOrder env) })

addSuggestedPredicates :: TR.TransitionRelation mdl => IC3 mdl ()
addSuggestedPredicates = do
  mdl <- asks ic3Model
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain (unique,trm)
                     -> if unique
                        then do
                          (_,ndom) <- liftIO $ Dom.domainAddUniqueUnsafe trm cdomain
                          return ndom
                        else do
                          (_,_,ndom) <- liftIO $ Dom.domainAdd trm cdomain
                          return ndom
                    ) domain (TR.suggestedPredicates mdl)
  modify $ \env -> env { ic3Domain = ndomain }

renderState :: TR.TransitionRelation mdl => Partial (TR.State mdl) -> IC3 mdl String
renderState st = do
  mdl <- asks ic3Model
  return (TR.renderPartialState mdl st)

renderAbstractState :: TR.TransitionRelation mdl
                    => Dom.AbstractState (TR.State mdl)
                    -> IC3 mdl String
renderAbstractState st = do
  domain <- gets ic3Domain
  return $ Dom.renderDomainTerm st domain

-- | Dump the internal IC3 data-structures
ic3Dump :: TR.TransitionRelation mdl => IC3 mdl ()
ic3Dump = do
  cons <- gets ic3Consecution
  let frames = consecutionFrames cons
  mapM_ (\(i,fr) -> do
            liftIO $ putStrLn $ "Frame "++show i++":"
            mapM_ (\cube_id -> do
                      cubeStr <- renderAbstractState (getCube cube_id cons)
                      liftIO $ putStrLn $ "  "++cubeStr
                  ) (IntSet.toList fr)
        ) (zip [0..] (Vec.toList frames))

checkFixpoint :: TR.TransitionRelation mdl => [Dom.AbstractState (TR.State mdl)] -> IC3 mdl ()
checkFixpoint abs_fp = do
  mdl <- asks ic3Model
  domain <- gets ic3Domain
  let fp = getFixpoint domain abs_fp
  liftIO $ withBackendExitCleanly (createPipe "z3" ["-in","-smt2"]) $ do
    setOption (ProduceModels True)
    incorrectInitial <- stack $ do
      cur <- TR.createStateVars (\tp rev -> declareVar tp) mdl
      TR.initialState mdl cur >>= assert
      fp cur >>= \fp' -> not' fp' >>= assert
      checkSat
    when (incorrectInitial/=Unsat) (error "Fixpoint doesn't cover initial condition")
    stack $ do
      cur <- TR.createStateVars (\tp rev -> declareVar tp) mdl
      inp <- TR.createInputVars (\tp rev -> declareVar tp) mdl
      TR.stateInvariant mdl cur inp >>= assert
      fp cur >>= assert
      (asserts,real0) <- TR.declareAssertions (const defineVar) mdl cur inp
                         (TR.startingProgress mdl)
      and' asserts >>= assert
      (assumps,real1) <- TR.declareAssumptions (const defineVar) mdl cur inp real0
      and' assumps >>= assert
      (nxt,real2) <- TR.declareNextState (const defineVar) mdl cur inp real1
      inp' <- TR.createInputVars (\tp rev -> declareVar tp) mdl
      (asserts',real0') <- TR.declareAssertions (const defineVar) mdl nxt inp'
                           (TR.startingProgress mdl)
      not' (and' asserts') >>= assert
      (assumps',real1') <- TR.declareAssumptions (const defineVar) mdl nxt inp' real0'
      and' assumps' >>= assert
      TR.stateInvariant mdl nxt inp' >>= assert
      errorReachable <- checkSat
      when (errorReachable/=Unsat)
        (do
           curSt <- fmap (TR.renderState mdl) $ unliftComp getValue cur
           curInpSt <- fmap (TR.renderInput mdl) $ unliftComp getValue inp
           nxtSt <- fmap (TR.renderState mdl) $ unliftComp getValue nxt
           nxtInpSt <- fmap (TR.renderInput mdl) $ unliftComp getValue inp'
           error $ "Fixpoint doesn't imply property.\nState:\n"++
             curSt++"\nInput:\n"++curInpSt++"\nNext state:\n"++nxtSt++"\nNext input:\n"++nxtInpSt
        )
    stack $ do
      cur <- TR.createStateVars (\tp rev -> declareVar tp) mdl
      inp <- TR.createInputVars (\tp rev -> declareVar tp) mdl
      TR.stateInvariant mdl cur inp >>= assert
      fp cur >>= assert
      (asserts,real0) <- TR.declareAssertions (const defineVar) mdl cur inp
                         (TR.startingProgress mdl)
      and' asserts >>= assert
      (assumps,real1) <- TR.declareAssumptions (const defineVar) mdl cur inp real0
      and' assumps >>= assert
      (nxt,real2) <- TR.declareNextState (const defineVar) mdl cur inp real1
      nxt_inp <- TR.createInputVars (\tp rev -> declareVar tp) mdl
      TR.stateInvariant mdl nxt nxt_inp >>= assert
      fp nxt >>= \fp' -> not' fp' >>= assert
      incorrectFix <- checkSat
      when (incorrectFix/=Unsat)
        (do
           curSt <- fmap (TR.renderState mdl) $ unliftComp getValue cur
           curInpSt <- fmap (TR.renderInput mdl) $ unliftComp getValue inp
           nxtSt <- fmap (TR.renderState mdl) $ unliftComp getValue nxt
           nxtInpSt <- fmap (TR.renderInput mdl) $ unliftComp getValue nxt_inp
           let fpSt = fmap (\e -> Dom.renderDomainTerm e domain
                           ) abs_fp
           liftIO $ do
             hPutStrLn stderr $ "Fixpoint "++
               intercalate ", " fpSt++
               " doesn't hold after one transition."
             hPutStrLn stderr $ "State:"
             hPutStrLn stderr $ curSt
             hPutStrLn stderr $ "Input:"
             hPutStrLn stderr $ curInpSt
             hPutStrLn stderr $ "Next state:"
             hPutStrLn stderr $ nxtSt
             hPutStrLn stderr $ "Next input:"
             hPutStrLn stderr $ nxtInpSt
           mapM_ (\e -> stack $ do
                   Dom.toDomainTerm e domain nxt >>= assert
                   reachable <- checkSat
                   when (reachable==Sat) $ liftIO $ do
                     let cube = Dom.renderDomainTerm e domain
                     hPutStrLn stderr $ "Cube reachable:"
                     hPutStrLn stderr $ "  "++cube
                ) abs_fp
           liftIO exitFailure
        )

newIC3Stats :: IO IC3Stats
newIC3Stats = do
  curTime <- getCurrentTime
  consTime <- newIORef 0
  consNum <- newIORef 0
  domTime <- newIORef 0
  domNum <- newIORef 0
  interpTime <- newIORef 0
  interpNum <- newIORef 0
  liftTime <- newIORef 0
  liftNum <- newIORef 0
  initTime <- newIORef 0
  initNum <- newIORef 0
  return $ IC3Stats { startTime = curTime
                    , consecutionTime = consTime
                    , consecutionNum = consNum
                    , domainTime = domTime
                    , domainNum = domNum
                    , interpolationTime = interpTime
                    , interpolationNum = interpNum
                    , liftingTime = liftTime
                    , liftingNum = liftNum
                    , initiationTime = initTime
                    , initiationNum = initNum
                    , numErased = 0
                    , numCTI = 0
                    , numCTG = 0
                    , numMIC = 0
                    , numCoreReduced = 0
                    , numUnliftedErased = 0
                    , numAbortJoin = 0
                    , numAbortMic = 0
                    , numRefinements = 0
                    , numAddPreds = 0 }

updateStats :: (IC3Stats -> IC3Stats) -> IC3 mdl ()
updateStats f = modify (\env -> env { ic3Stats = fmap f (ic3Stats env) })

ic3DumpStats :: TR.TransitionRelation mdl
             => Maybe [Dom.AbstractState (TR.State mdl)] -> IC3 mdl ()
ic3DumpStats fp = do
  stats <- gets ic3Stats
  case stats of
   Just stats -> do
     level <- k
     curTime <- liftIO $ getCurrentTime
     consTime <- liftIO $ readIORef (consecutionTime stats)
     consNum <- liftIO $ readIORef (consecutionNum stats)
     domTime <- liftIO $ readIORef (domainTime stats)
     domNum <- liftIO $ readIORef (domainNum stats)
     interpTime <- liftIO $ readIORef (interpolationTime stats)
     interpNum <- liftIO $ readIORef (interpolationNum stats)
     liftTime <- liftIO $ readIORef (liftingTime stats)
     liftNum <- liftIO $ readIORef (liftingNum stats)
     initTime <- liftIO $ readIORef (initiationTime stats)
     initNum <- liftIO $ readIORef (initiationNum stats)
     numPreds <- gets (Dom.domainHash . ic3Domain)
     let (numCl,numLit) = foldl (\(numCl,numLit) st -> (numCl+1,numLit+Vec.length st))
                          (0,0) (case fp of
                                  Nothing -> []
                                  Just rfp -> rfp)
         totalRuntime = diffUTCTime curTime (startTime stats)
     liftIO $ do
       putStrLn $ "Level: "++show level
       putStrLn $ "Total runtime: "++show totalRuntime
       putStrLn $ "Consecution time: "++show consTime
       putStrLn $ "Domain time: "++show domTime
       putStrLn $ "Interpolation time: "++show interpTime
       putStrLn $ "Initiation time: "++show initTime
       putStrLn $ "# of consecution queries: "++show consNum
       putStrLn $ "# of domain queries: "++show domNum
       putStrLn $ "# of interpolation queries: "++show interpNum
       putStrLn $ "# of lifting queries: "++show liftNum
       putStrLn $ "# of initiation queries: "++show initNum
       putStrLn $ "# of predicates: "++show numPreds
       putStrLn $ "# of CTIs: "++show (numCTI stats)
       putStrLn $ "# of CTGs: "++show (numCTG stats)
       putStrLn $ "# of MICs: "++show (numMIC stats)
       putStrLn $ "# of reduced cores: "++show (numCoreReduced stats)
       putStrLn $ "# of aborted joins: "++show (numAbortJoin stats)
       putStrLn $ "# of aborted mics: "++show (numAbortMic stats)
       putStrLn $ "# of refinements: "++show (numRefinements stats)
       putStrLn $ "# of additional predicates: "++show (numAddPreds stats)
       when (numCl>0) $ do
         putStrLn $ "# of fixpoint clauses: "++show numCl
         putStrLn $ "# of avg. literals per clause: "++show (numLit `div` numCl)
       putStrLn $ "# erased: "++show (numErased stats)
       putStrLn $ "% unlifted: "++
         (show $ (round $ 100*(fromIntegral $ numUnliftedErased stats) /
                  (fromIntegral $ numErased stats) :: Int))

     dumpStats <- asks ic3DumpStatsFile
     case dumpStats of
       Nothing -> return ()
       Just file ->
           let mrsStats = IC3MachineReadableStats
                          { mrs_totalTime = realToFrac totalRuntime
                          , mrs_consecutionTime = realToFrac consTime
                          , mrs_consecutionNum = consNum
                          , mrs_domainTime = realToFrac domTime
                          , mrs_domainNum = domNum
                          , mrs_interpolationTime = realToFrac interpTime
                          , mrs_interpolationNum = interpNum
                          , mrs_liftingTime = realToFrac liftTime
                          , mrs_liftingNum = liftNum
                          , mrs_initiationTime = realToFrac initTime
                          , mrs_initiationNum = initNum
                          , mrs_numErased = numErased stats
                          , mrs_numCTI = numCTI stats
                          , mrs_numUnliftedErased = numUnliftedErased stats
                          , mrs_numCTG = numCTG stats
                          , mrs_numMIC = numMIC stats
                          , mrs_numCoreReduced = numCoreReduced stats
                          , mrs_numAbortJoin = numAbortJoin stats
                          , mrs_numAbortMic = numAbortMic stats
                          , mrs_numRefinements = numRefinements stats
                          , mrs_numAddPreds = numAddPreds stats
                          , mrs_numPreds = numPreds}
           in liftIO $ Y.encodeFile file mrsStats
   Nothing -> return ()
  dumpDomain <- asks ic3DumpDomainFile
  case dumpDomain of
    Nothing -> return ()
    Just fn -> do
      domain <- gets ic3Domain
      let str = Dom.renderDomain domain
      liftIO $ writeFile fn str

addTiming :: IORef NominalDiffTime -> IORef Int -> AnyBackend IO -> AnyBackend IO
addTiming time_ref num_ref (AnyBackend act) = AnyBackend $ do
  b <- act
  return $ timingBackend (\t -> modifyIORef' time_ref (+t) >>
                                modifyIORef' num_ref (+1)
                         ) b

addDebugging :: String -> AnyBackend IO -> AnyBackend IO
addDebugging name (AnyBackend act) = AnyBackend $ do
  b <- act
  return $ namedDebugBackend name b
