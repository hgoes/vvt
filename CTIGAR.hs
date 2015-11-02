{-# LANGUAGE ExistentialQuantification,FlexibleContexts,RankNTypes,
             ScopedTypeVariables,PackageImports,GADTs,DeriveDataTypeable,
             ViewPatterns,MultiParamTypeClasses #-}
module CTIGAR where

import qualified Realization as TR
import Domain
import Consecution
import PartialArgs
import SMTPool
import LitOrder
import BackendOptions

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Pipe
import Language.SMTLib2.Debug
import Language.SMTLib2.Timing
import Language.SMTLib2.DatatypeEmulator
import Language.SMTLib2.ModulusEmulator

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import qualified Data.IntSet as IntSet
import Data.IORef
import Control.Monad (when)
import Control.Applicative (Applicative(..))
import "mtl" Control.Monad.Trans (MonadIO,liftIO)
import "mtl" Control.Monad.Reader (MonadReader(..),ask,asks)
import "mtl" Control.Monad.State (MonadState,gets)
import Data.List (sort,sortBy,genericIndex,intercalate)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as Queue
import Data.Graph.Inductive (Node)
import Data.Foldable
import Data.Traversable
import Prelude hiding (sequence_,concat,mapM_,or,and,mapM,foldl)
import Data.Typeable
import "mtl" Control.Monad.State (get,put,modify)
import Data.Bits (shiftL)
import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)
import Data.Time.Clock
import Control.Exception (Exception,SomeException,finally,catch,throw)
import System.IO
import System.Exit

data IC3Config mdl
  = IC3Cfg { ic3Model :: mdl
           , ic3ConsecutionBackend :: IO (AnyBackend IO)
           , ic3LiftingBackend :: IO (AnyBackend IO)
           , ic3DomainBackend :: IO (AnyBackend IO)
           , ic3BaseBackend :: IO (AnyBackend IO)
           , ic3InitBackend :: IO (AnyBackend IO)
           , ic3InterpolationBackend :: IO (AnyBackend IO)
           , ic3DebugLevel :: Int
           , ic3MaxSpurious :: Int
           , ic3MicAttempts :: Int
           , ic3MaxDepth :: Int
           , ic3MaxJoins :: Int
           , ic3MaxCTGs :: Int
           , ic3CollectStats :: Bool
           , ic3DumpDomainFile :: Maybe String
           }

data IC3Env mdl
  = IC3Env { ic3Domain :: Domain (TR.State mdl) -- The domain talks about the outputs
           , ic3InitialProperty :: Node
           , ic3Consecution :: Consecution (TR.Input mdl) (TR.State mdl)
           , ic3Lifting :: Lifting mdl
           , ic3Initiation :: SMTPool () (TR.State mdl)
           , ic3Interpolation :: SMTPool () (InterpolationState mdl)
           , ic3LitOrder :: LitOrder
           , ic3CexState :: Maybe (IORef (State (TR.Input mdl) (TR.State mdl)))
           , ic3Earliest :: Int
           , ic3PredicateExtractor :: TR.PredicateExtractor mdl
           , ic3Stats :: Maybe IC3Stats
           }

type Lifting mdl = SMTPool () (LiftingState mdl)

data IC3Stats = IC3Stats { startTime :: UTCTime
                         , consecutionTime :: IORef NominalDiffTime
                         , consecutionNum :: IORef Int
                         , domainTime :: IORef NominalDiffTime
                         , domainNum :: IORef Int
                         , interpolationTime :: IORef NominalDiffTime
                         , interpolationNum :: IORef Int
                         , liftingTime :: IORef NominalDiffTime
                         , liftingNum :: IORef Int
                         , initiationTime :: IORef NominalDiffTime
                         , initiationNum :: IORef Int
                         , numErased :: Int
                         , numCTI :: Int
                         , numUnliftedErased :: Int
                         , numCTG :: Int
                         , numMIC :: Int
                         , numCoreReduced :: Int
                         , numAbortJoin :: Int
                         , numAbortMic :: Int
                         , numRefinements :: Int
                         , numAddPreds :: Int
                         }

data InterpolationState mdl = InterpolationState { interpCur :: TR.State mdl
                                                 , interpNxt :: TR.State mdl
                                                 , interpInputs :: TR.Input mdl
                                                 , interpNxtInputs :: TR.Input mdl
                                                 , interpAsserts :: [SMTExpr Bool]
                                                 , interpAnte :: Either InterpolationGroup [SMTExpr Bool]
                                                 , interpPost :: Maybe InterpolationGroup
                                                 , interpReverse :: TR.RevState mdl
                                                 , interpUsingMathSAT :: Bool
                                                 }

data LiftingState mdl = LiftingState { liftCur :: TR.State mdl
                                     , liftInputs :: TR.Input mdl
                                     , liftNxt :: TR.State mdl
                                     , liftNxtInputs :: TR.Input mdl
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

-- | In order to deal with exceptions, this is a custom monad.
newtype IC3 mdl a = IC3 { evalIC3 :: IC3Config mdl -> IORef (IC3Env mdl) -> IO a }

data State inp st = State { stateSuccessor :: Maybe (IORef (State inp st))
                          , stateLiftedAst :: Maybe (AbstractState st)
                          , stateFullAst :: Maybe (AbstractState st)
                          , stateFull :: Unpacked st
                          , stateInputs :: Unpacked inp
                          , stateNxtInputs :: Unpacked inp
                          , stateLifted :: PartialValue st
                          , stateLiftedInputs :: PartialValue inp
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

bestAbstraction :: State inp st -> AbstractState st
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
ic3Debug lvl txt = ic3DebugAct lvl (liftIO $ putStrLn txt)

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
            -> IC3Config mdl
mkIC3Config mdl opts verb stats dumpDomain
  = IC3Cfg { ic3Model = mdl
           , ic3ConsecutionBackend = mkPipe (optBackend opts Map.! ConsecutionBackend)
                                     (if Set.member ConsecutionBackend (optDebugBackend opts)
                                      then Just "cons"
                                      else Nothing)
           , ic3LiftingBackend = mkPipe (optBackend opts Map.! Lifting)
                                 (if Set.member Lifting (optDebugBackend opts)
                                  then Just "lift"
                                  else Nothing)
           , ic3DomainBackend = mkPipe (optBackend opts Map.! Domain)
                                (if Set.member Domain (optDebugBackend opts)
                                 then Just "domain"
                                 else Nothing)
           , ic3BaseBackend = mkPipe (optBackend opts Map.! Base)
                              (if Set.member Base (optDebugBackend opts)
                               then Just "base"
                               else Nothing)
           , ic3InitBackend = mkPipe (optBackend opts Map.! Initiation)
                              (if Set.member Initiation (optDebugBackend opts)
                               then Just "init"
                               else Nothing)
           , ic3InterpolationBackend = mkPipe (optBackend opts Map.! Interpolation)
                                       (if Set.member Interpolation (optDebugBackend opts)
                                        then Just "interp"
                                        else Nothing)
           , ic3DebugLevel = verb
           , ic3MaxSpurious = 0
           , ic3MicAttempts = 1 `shiftL` 20
           , ic3MaxDepth = 1
           , ic3MaxJoins = 1 `shiftL` 20
           , ic3MaxCTGs = 3
           , ic3CollectStats = stats
           , ic3DumpDomainFile = dumpDomain
           }
  where
    mkPipe cmd debug = let prog:args = words cmd
                       in case debug of
                           Nothing -> fmap AnyBackend $ createSMTPipe prog args
                           Just name -> do
                             pipe <- createSMTPipe prog args
                             return (AnyBackend $ namedDebugBackend name pipe)

runIC3 :: TR.TransitionRelation mdl => IC3Config mdl -> IC3 mdl a -> IO a
runIC3 cfg act = do
  let mdl = ic3Model cfg
  stats <- if ic3CollectStats cfg
           then fmap Just newIC3Stats
           else return Nothing
  -- MathSAT is really annoying, we have to take care of it like a baby
  interpolationIsMathSAT <- do
    backend <- ic3InterpolationBackend cfg
    withSMTBackend backend $ do
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
      interpBackend'' = if interpolationIsMathSAT
                        then addModulusEmulation interpBackend'
                        else interpBackend'
  cons <- consecutionNew ({-addDebugging "cons"-} consBackend)
          (do
              cur <- TR.createStateVars "" mdl
              inp <- TR.createInputVars "" mdl
              assert (TR.stateInvariant mdl inp cur)
              (nxt,real1) <- TR.declareNextState mdl cur inp Nothing (TR.startingProgress mdl)
              --assert (blockConstraint nxtBlks)
              (asserts1,real2) <- TR.declareAssertions mdl cur inp real1
              (assumps1,real3) <- TR.declareAssumptions mdl cur inp real2
              mapM_ assert asserts1
              mapM_ assert assumps1
              nxtInp <- TR.createInputVars "nxt." mdl
              (asserts2,real1') <- TR.declareAssertions mdl nxt nxtInp (TR.startingProgress mdl)
              (assumps2,real2') <- TR.declareAssumptions mdl nxt nxtInp real1'
              assert (TR.stateInvariant mdl nxtInp nxt)
              mapM_ assert assumps2
              return $ ConsecutionVars { consecutionInput = inp
                                       , consecutionNxtInput = nxtInp
                                       , consecutionState = cur
                                       , consecutionNxtState = nxt
                                       , consecutionNxtAsserts = asserts2 })
          (TR.initialState mdl)
  lifting <- createSMTPool ({-addDebugging "lift"-} liftingBackend) $ do
    setOption (ProduceUnsatCores True)
    cur <- TR.createStateVars "" mdl
    inp <- TR.createInputVars "inp." mdl
    assert $ TR.stateInvariant mdl inp cur
    (nxt,real1) <- TR.declareNextState mdl cur inp Nothing (TR.startingProgress mdl)
    (assumps,real2) <- TR.declareAssumptions mdl cur inp real1
    mapM_ assert assumps
    inp' <- TR.createInputVars "inp.nxt." mdl
    (asserts,real1') <- TR.declareAssertions mdl nxt inp' (TR.startingProgress mdl)
    (assumps2,real2') <- TR.declareAssumptions mdl nxt inp' real1'
    assert (TR.stateInvariant mdl inp' nxt)
    mapM_ assert assumps2
    return $ LiftingState cur inp nxt inp' asserts
  initiation <- createSMTPool initiationBackend $ do
    cur <- TR.createStateVars "" mdl
    assert $ TR.initialState mdl cur
    --assert $ TR.stateInvariant mdl inp cur
    return cur
  interpolation <- createSMTPool interpBackend'' $ do
    setLogic "QF_AUFLIA"
    setOption (ProduceInterpolants True)
    setOption (ProduceModels True)
    if interpolationIsMathSAT
      then do
      ante <- interpolationGroup
      post <- interpolationGroup
      cur <- TR.createStateVars "" mdl
      inp <- TR.createInputVars "" mdl
      nxtInp <- TR.createInputVars "" mdl
      (nxt,real1) <- TR.declareNextState mdl cur inp (Just ante) (TR.startingProgress mdl)
      (asserts,real2) <- TR.declareAssertions mdl cur inp real1
      (assumps,real3) <- TR.declareAssumptions mdl cur inp real2
      (nxt',rev) <- TR.createRevState "" mdl
      mapM_ (\asump -> assertInterp asump ante) assumps
      mapM_ (\assert -> assertInterp assert ante) asserts
      assertInterp (TR.stateInvariant mdl inp cur) ante
      assertInterp (TR.stateInvariant mdl nxtInp nxt') post
      assertInterp (argEq nxt' nxt) ante
      return $ InterpolationState { interpCur = cur
                                  , interpNxt = nxt'
                                  , interpInputs = inp
                                  , interpNxtInputs = nxtInp
                                  , interpAsserts = asserts
                                  , interpAnte = Left ante
                                  , interpPost = Just post
                                  , interpReverse = rev
                                  , interpUsingMathSAT = True
                                  }
      else do
      cur <- TR.createStateVars "" mdl
      inp <- TR.createInputVars "" mdl
      nxtInp <- TR.createInputVars "" mdl
      (nxt,real1) <- TR.declareNextState mdl cur inp Nothing (TR.startingProgress mdl)
      (asserts,real2) <- TR.declareAssertions mdl cur inp real1
      (assumps,real3) <- TR.declareAssumptions mdl cur inp real2
      (nxt',rev) <- TR.createRevState "" mdl
      exprs1 <- mapM (\assump -> do
                         (assump',name) <- named "assump" assump
                         assert assump'
                         return name
                     ) assumps
      exprs2 <- mapM (\ass -> do
                         (ass',name) <- named "assertion" ass
                         assert ass'
                         return name
                     ) asserts
      (invExpr1,namedInvExpr1) <- named "invariant1" (TR.stateInvariant mdl inp cur)
      (invExpr2,namedInvExpr2) <- named "invariant2" (TR.stateInvariant mdl nxtInp nxt)
      (eqExpr,namedEqExpr) <- named "equality" (argEq nxt' nxt)
      assert invExpr1
      assert invExpr2
      assert eqExpr
      return $ InterpolationState { interpCur = cur
                                  , interpNxt = nxt'
                                  , interpInputs = inp
                                  , interpNxtInputs = nxtInp
                                  , interpAsserts = exprs2
                                  , interpAnte = Right (exprs1++exprs2++[namedInvExpr1,namedInvExpr2,namedEqExpr])
                                  , interpPost = Nothing
                                  , interpReverse = rev
                                  , interpUsingMathSAT = False
                                  }
  dom <- initialDomain (ic3DebugLevel cfg) domainBackend
         (TR.annotationState mdl)
         (TR.createStateVars "" mdl)
  (initNode,dom') <- domainAdd (TR.initialState mdl) dom
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

extractState :: (PartialArgs inp,PartialArgs st)
                => Maybe (IORef (State inp st))
                -> ConsecutionVars inp st
                -> SMT (State inp st)
extractState (succ::Maybe (IORef (State inp st))) vars = do
  inps <- getValues (consecutionInput vars)
  nxtInps <- getValues (consecutionNxtInput vars)
  full <- getValues (consecutionState vars)
  return $ State { stateSuccessor = succ
                 , stateLiftedAst = Nothing
                 , stateFullAst = Nothing
                 , stateFull = full
                 , stateInputs = inps
                 , stateNxtInputs = nxtInps
                 , stateLifted = unmaskValue (undefined::st) full
                 , stateLiftedInputs = unmaskValue (undefined::inp) inps
                 , stateSpuriousLevel = 0
                 , stateNSpurious = 0
                 , stateSpuriousSucc = False
                 , stateDomainHash = 0 }

liftState :: (PartialArgs (TR.State mdl),
              PartialArgs (TR.Input mdl))
             => Lifting mdl -> State (TR.Input mdl) (TR.State mdl)
             -> IO (State (TR.Input mdl) (TR.State mdl))
liftState lifting st = do
  nxt <- case stateSuccessor st of
    Nothing -> return $ \lft -> app and' $ liftNxtAsserts lft
    Just succ' -> do
      succ'' <- readIORef succ'
      return $ \lft -> (not' $ app and' [ cond
                                        | Just cond <- assignPartial (liftNxt lft) (stateLifted succ'')
                                        ]) {-.||.
                       (not' $ app and' [ cond
                                        | Just cond <- assignPartial (liftNxtInputs lft) (stateLiftedInputs succ'')])-}
  (part,partInp) <- withSMTPool lifting $
                    \vars' -> lift' ((liftCur vars'),
                                     liftInputs vars',
                                     liftNxtInputs vars')
                              (stateFull st,stateInputs st,stateNxtInputs st,nxt vars')
  return $ st { stateLifted = part
              , stateLiftedInputs = partInp }

lift' :: (PartialArgs st,PartialArgs inp) => (st,inp,inp)
             -> (Unpacked st,Unpacked inp,Unpacked inp,SMTExpr Bool)
             -> SMT (PartialValue st,PartialValue inp)
lift' (cur::st,inp::inp,inp') vals@(vcur,vinp,vinp',vnxt) = stack $ do
  let assignedCur = assignPartial cur (unmaskValue cur vcur)
      assignedInp = assignPartial inp (unmaskValue inp vinp)
  comment "State:"
  (cmp1,len_st) <- foldlM (\(mp,n) cond -> case cond of
                            Nothing -> return (mp,n+1)
                            Just cond' -> do
                              cid <- assertId cond'
                              return (Map.insert cid (Left n) mp,n+1)
                          ) (Map.empty,0) assignedCur
  comment "Input:"
  (cmp2,len_inp) <- foldlM (\(mp,n) cond -> case cond of
                             Nothing -> return (mp,n+1)
                             Just cond' -> do
                               cid <- assertId cond'
                               return (Map.insert cid (Right n) mp,n+1)
                           ) (cmp1,0) assignedInp
  --assert $ argEq inp (liftArgs vinp (extractArgAnnotation inp))
  --assert $ argEq inp' (liftArgs vinp' (extractArgAnnotation inp'))
  comment "Next state:"
  assert vnxt
  res <- checkSat
  when res $ error $ "The model appears to be non-deterministic."
  core <- getUnsatCore
  let (coreSt,coreInp) = partitionEithers $ fmap (cmp2 Map.!) core
      partSt = toTruthValues len_st 0 (sort coreSt)
      partInp = toTruthValues len_inp 0 (sort coreInp)
      vcur' = unmaskValue (error "U1"::st) vcur
      vinp' = unmaskValue (error "U1"::inp) vinp
      (vcur'',[]) = maskValue (error "U2"::st) vcur' partSt
      (vinp'',[]) = maskValue (error "U2"::inp) vinp' partInp
  return (vcur'',vinp'')
  where
    toTruthValues len n []
      | n==len = []
      | otherwise = False:toTruthValues len (n+1) []
    toTruthValues len n (x:xs)
      = if n==x
        then True:toTruthValues len (n+1) xs
        else False:toTruthValues len (n+1) (x:xs)

-- | Check if the abstract state intersects with the initial condition
initiationAbstract :: AbstractState (TR.State mdl) -> IC3 mdl Bool
initiationAbstract state = do
  env <- get
  fmap not $ liftIO $ withSMTPool (ic3Initiation env) $
    \vars -> stack $ do
      comment $ "initiation abstract: "++show state
      assert $ toDomainTerm state (ic3Domain env) vars
      checkSat

initiationConcrete :: PartialArgs (TR.State mdl) => PartialValue (TR.State mdl) -> IC3 mdl Bool
initiationConcrete vals = do
  env <- get
  liftIO $ fmap not $ withSMTPool (ic3Initiation env) $
    \vars -> stack $ do
      mapM assert (assignPartial' vars vals)
      checkSat

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
     (stateDomainHash st == domainHash dom)
    then return False
    else (do
             full <- liftIO $ domainAbstract
                     (\x -> {-argEq x (liftArgs (stateFull st) (TR.annotationState mdl))-}
                       app and' $ assignPartial' x (stateLifted st))
                     initialPred
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

lift :: (TR.TransitionRelation mdl,
         LiftArgs (TR.Input mdl))
        => AbstractState (TR.State mdl)
        -> Unpacked (TR.Input mdl)
        -> Unpacked (TR.Input mdl)
        -> Maybe (AbstractState (TR.State mdl))
        -> IC3 mdl (Maybe (AbstractState (TR.State mdl)))
lift toLift inps nxtInps succ = do
  lifting <- gets ic3Lifting
  domain <- gets ic3Domain
  initProp <- gets ic3InitialProperty
  mdl <- asks ic3Model
  liftAbs <- liftIO $ withSMTPool lifting $ \st -> stack $ do
    (_,rev) <- foldlM (\(i,mp) (nd,expr,act) -> do
                          cid <- assertId (if act then expr else not' expr)
                          return (i+1,Map.insert cid i mp)
                      ) (0,Map.empty) (toDomainTerms toLift domain (liftCur st))
    assert $ argEq (liftInputs st) (liftArgs inps (TR.annotationInput mdl))
    --assert $ argEq (liftNxtInputs st) (liftArgs nxtInps (TR.annotationInput mdl))
    case succ of
      Nothing -> assert $ app and' (liftNxtAsserts st)
      Just succ_abstr -> assert $ not' $ toDomainTerm succ_abstr domain (liftNxt st)
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
                       -> AbstractState (TR.State mdl) -- ^ The possibly inductive abstract state 's'
                       -> Maybe (IORef (State (TR.Input mdl) (TR.State mdl)))
                       -> IC3 mdl (Either (AbstractState (TR.State mdl))
                                   (State (TR.Input mdl) (TR.State mdl))
                                  )
abstractConsecution fi abs_st succ = do
  --rebuildConsecution
  --modify (\env -> env { ic3ConsecutionCount = (ic3ConsecutionCount env)+1 })
  ic3DebugAct 3 $ do
    abs_st_str <- renderAbstractState abs_st
    liftIO $ putStrLn ("Original abstract state: "++abs_st_str)
  env <- get
  res <- liftIO $ consecutionPerform (ic3Domain env) (ic3Consecution env) fi $ \vars -> do
    assert $ not' $ toDomainTerm abs_st (ic3Domain env) (consecutionState vars)
    (_,rev) <- foldlM (\(i,mp) (nd,expr,act) -> do
                          cid <- assertId
                                 (if act then expr
                                  else not' expr)
                          return (i+1,Map.insert cid i mp)
                      ) (0,Map.empty) (toDomainTerms abs_st (ic3Domain env)
                                       (consecutionNxtState vars))
    -- Henning: This tries to take the lifted inputs of the successor into account (doesn't do anything yet)
    {-case succ of
     Nothing -> return ()
     Just s -> do
       succ' <- liftIO $ readIORef s
       assert $ app and' $ assignPartial' (consecutionNxtInput vars)
         (stateLiftedInputs succ')-}
    res <- checkSat
    if res
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
        liftIO $ putStrLn ("Reduced abstract state: "++abs_st_str)
      --absInit' <- initiationAbstract absCore'
      --error $ "abstractConsecution core: "++show absCore'++" "++show absInit'
      return $ Left absCore'

concreteConsecution :: TR.TransitionRelation mdl
                       => Int -> PartialValue (TR.State mdl)
                       -> IORef (State (TR.Input mdl) (TR.State mdl))
                       -> IC3 mdl (Maybe (IORef (State (TR.Input mdl) (TR.State mdl))))
concreteConsecution fi st succ = do
  env <- get
  res <- liftIO $ consecutionPerform (ic3Domain env) (ic3Consecution env) fi $ \vars -> do
    assert (app or' $ fmap not' $ assignPartial' (consecutionState vars) st)
    {-do
      succ' <- liftIO $ readIORef succ
      assert $ app and' $ assignPartial' (consecutionNxtInput vars)
        (stateLiftedInputs succ')-}
    mapM_ assert (assignPartial' (consecutionNxtState vars) st)
    sat <- checkSat
    if sat
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
                      => Int -> AbstractState (TR.State mdl)
                      -> IC3 mdl Int
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
                   Right _ -> addCube level cube)
        else addCube level cube
    addCube level cube = do
      ic3DebugAct 3 $ do
        cubeStr <- renderAbstractState cube
        liftIO $ putStrLn $ "Adding cube at level "++show level++": "++cubeStr
      addAbstractCube level cube
      return level

baseCases :: TR.TransitionRelation mdl
             => mdl -> SMT (Maybe [Unpacked (TR.State mdl,TR.Input mdl)])
baseCases st = do
  comment "State:"
  cur0 <- TR.createStateVars "" st
  comment "Inputs:"
  inp0 <- TR.createInputVars "" st
  assert $ TR.initialState st cur0
  comment "Assumptions:"
  (assumps0,real0) <- TR.declareAssumptions st cur0 inp0 (TR.startingProgress st)
  mapM_ assert assumps0
  comment "Invariant:"
  assert $ TR.stateInvariant st inp0 cur0
  comment "Declare assertions:"
  (asserts0,real1) <- TR.declareAssertions st cur0 inp0 real0
  comment "Declare next state:"
  (cur1,real2) <- TR.declareNextState st cur0 inp0 Nothing real1
  comment "Inputs 2:"
  inp1 <- TR.createInputVars "nxt" st
  comment "Assumptions 2:"
  (assumps1,real0) <- TR.declareAssumptions st cur1 inp1 (TR.startingProgress st)
  comment "Invariant 2:"
  assert $ TR.stateInvariant st inp1 cur1
  mapM_ assert assumps1
  comment "Declare assertions 2:"
  (asserts1,_) <- TR.declareAssertions st cur1 inp1 real0
  assert $ not' $ app and' (asserts0++asserts1)
  res <- checkSat
  if res
    then (do
             succ0 <- mapM getValue asserts0
             if not $ and succ0
               then (do
                        cv0 <- getValues (cur0,inp0)
                        return (Just [cv0]))
               else (do
                        cv0 <- getValues (cur0,inp0)
                        cv1 <- getValues (cur1,inp1)
                        return (Just [cv0,cv1])))
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
        assert $ app or' $ fmap not' $ consecutionNxtAsserts vars
        sat <- checkSat
        if sat
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
         -> IO (Either [Unpacked (TR.State mdl,TR.Input mdl)] [AbstractState (TR.State mdl)])
check st opts verb stats dumpDomain = do
  let prog:args = words (optBackend opts Map.! Base)
  backend <- createSMTPipe prog args -- >>= namedDebugBackend "base"
  tr <- withSMTBackendExitCleanly backend (baseCases st)
  runIC3 (mkIC3Config st opts verb stats dumpDomain) $ do
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
                      return res
                 ) `ic3Catch` (\ex -> do
                                   ic3DumpStats Nothing
                                   throw (ex::SomeException))
  where
    checkIt = do
      ic3DebugAct 1 (do
                        lvl <- k
                        liftIO $ putStrLn $ "Level "++show lvl)
      extend
      sres <- strengthen
      case sres of
        Nothing -> do
          real <- asks ic3Model
          cex <- gets ic3CexState
          tr <- liftIO $ getWitnessTr cex
          res <- liftIO $ do
            backend <- createSMTPipe "z3" ["-in","-smt2"]
            withSMTBackendExitCleanly backend $ do
              st0 <- TR.createStateVars "" real
              assert $ TR.initialState real st0
              tr' <- constructTrace real st0 tr []
              rv <- checkSat
              if rv
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
    constructTrace real st [] errs = do
      inps <- TR.createInputVars "" real
      (assumps,real0) <- TR.declareAssumptions real st inps (TR.startingProgress real)
      (ass,_) <- TR.declareAssertions real st inps real0
      comment "Invariant"
      assert $ TR.stateInvariant real inps st
      comment "Assumptions"
      mapM_ assert assumps
      comment "Assertions"
      assert $ app or' (fmap not' (ass++errs))
      return [(st,inps)]
    constructTrace real st (x:xs) asserts = do
      comment "Assignments"
      assert $ app and' $ assignPartial' st x
      comment "Inputs"
      inps <- TR.createInputVars "" real
      comment "Invariant"
      assert $ TR.stateInvariant real inps st
      (assumps,real0) <- TR.declareAssumptions real st inps (TR.startingProgress real)
      (nxt_st,real1) <- TR.declareNextState real st inps Nothing real0
      (ass,real2) <- TR.declareAssertions real st inps real1
      comment "Assumptions"
      assert $ app and' assumps
      rest <- constructTrace real nxt_st xs (ass++asserts)
      return ((st,inps):rest)
    getWitness _ [] = return []
    getWitness real (x:xs) = do
      concr <- getValues x
      concrs <- getWitness real xs
      return $ concr:concrs

getFixpoint :: Domain st -> [AbstractState st] -> st -> SMTExpr Bool
getFixpoint domain sts inp = app and' [ not' $ toDomainTerm st domain inp
                                      | st <- sts ]

getAbstractFixpoint :: Int -> IC3 mdl [AbstractState (TR.State mdl)]
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
  env <- get
  (nextr,props) <- TR.extractPredicates mdl
                   (ic3PredicateExtractor env)
                   (stateFull rst)
                   (stateLifted rst)
  updateStats (\stats -> stats { numRefinements = (numRefinements stats)+1
                               , numAddPreds = (numAddPreds stats)+(length props) })
  put $ env { ic3PredicateExtractor = nextr }
  interp <- interpolateState level (stateLifted rst) (stateLiftedInputs rst)
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain trm
                     -> do
                       (_,ndom) <- liftIO $ domainAdd trm cdomain
                       return ndom
                    ) domain (interp++props)
  --liftIO $ domainDump ndomain >>= putStrLn
  modify $ \env -> env { ic3Domain = ndomain }

interpolateState :: TR.TransitionRelation mdl => Int
                 -> PartialValue (TR.State mdl)
                 -> PartialValue (TR.Input mdl)
                 -> IC3 mdl [TR.State mdl -> SMTExpr Bool]
interpolateState j s inp = do
  env <- get
  cfg <- ask
  liftIO $ withSMTPool (ic3Interpolation env) $
    \st -> stack $ do
      comment $ "Interpolating at level "++show j
      if interpUsingMathSAT st
        then do
        -- XXX: Workaround for baby MathSAT:
        ante <- interpolationGroup
        post <- interpolationGroup
        if j==0
          then assertInterp (translateToMathSAT $ TR.initialState (ic3Model cfg) (interpCur st)) ante --(interpAnte st)
          else (do
                   let cons = ic3Consecution env
                       frames = Vec.drop j (consecutionFrames cons)
                   mapM_ (\fr -> mapM_ (\st_id -> do
                                           let ast = getCube st_id cons
                                               trm = toDomainTerm ast (ic3Domain env)
                                                     (interpCur st)
                                           assertInterp (translateToMathSAT $ not' trm) ante --(interpAnte st)
                                       ) (IntSet.toList fr)
                         ) frames)
        assertInterp (translateToMathSAT $ not' $ app and' $ assignPartial' (interpCur st) s)
          ante -- (interpAnte st)
        --assertInterp (translateToMathSAT $ not' $ app and' $ assignPartial' (interpInputs st) inp)
        --  ante
        assertInterp (translateToMathSAT $ app and' $ assignPartial' (interpNxt st) s)
          post -- (interpPost st)
        --assertInterp (translateToMathSAT $ app and' $ assignPartial' (interpNxtInputs st) inp)
        --  post
        res <- checkSat
        when res $ do
          curSt <- getValues (interpCur st) >>= TR.renderState (ic3Model cfg)
          curInpSt <- getValues (interpInputs st) >>= TR.renderInput (ic3Model cfg)
          nxtSt <- getValues (interpNxt st) >>= TR.renderState (ic3Model cfg)
          error $ "Interpolation query is SAT.\nState:\n"++
            curSt++"\nInput:\n"++curInpSt++"\nNext state:\n"++nxtSt
        let Left ante' = interpAnte st
        interp <- getInterpolant [ante,ante']
        let interp1 = cleanInterpolant interp
        interp1Str <- renderExpr interp1
        comment $ "Cleaned interpolant: "++interp1Str
        return $ fmap (TR.relativizeExpr (ic3Model cfg) (interpReverse st)
                      ) $ splitInterpolant $ negateInterpolant interp1
        else do
        ante1 <- if j==0
                 then do
                   (inits,namedInits) <- named "init"
                                         (TR.initialState (ic3Model cfg) (interpCur st))
                   assert inits
                   return [namedInits]
                 else do
                   let cons = ic3Consecution env
                       frames = Vec.drop j (consecutionFrames cons)
                   fmap concat $
                     mapM (\fr -> mapM (\st_id -> do
                                           let ast = getCube st_id cons
                                               trm = toDomainTerm ast (ic3Domain env)
                                                     (interpCur st)
                                           (trm',namedTrm) <- named "trm" (not' trm)
                                           assert trm'
                                           return namedTrm
                                       ) (IntSet.toList fr)
                          ) frames
        ante2 <- do
          (asgn,namedAsgn) <- named "assign" $ not' $ app and' $ assignPartial' (interpCur st) s
          assert asgn
          return namedAsgn
        post1 <- do
          (asgn,namedAsgn) <- named "assignNxt" $ app and' $ assignPartial' (interpNxt st) s
          assert asgn
          return namedAsgn
        res <- checkSat
        when res $ error "Interpolation query is SAT"
        let Right ante = interpAnte st
        [interp] <- interpolate [post1,app and' $ ante++ante1++[ante2]]
        let interp1 = cleanInterpolant interp
        interp1Str <- renderExpr interp1
        comment $ "Cleaned interpolant: "++interp1Str
        return $ fmap (TR.relativizeExpr (ic3Model cfg) (interpReverse st)
                      ) $ splitInterpolant $ negateInterpolant interp1
  where
    cleanInterpolant (Let lvl args f)
      = let (_,f') = foldExpr (\_ e -> case e of
                                        QVar lvl' idx _
                                          | lvl==lvl' -> ((),castUntypedExpr $ args `genericIndex` idx)
                                        _ -> ((),e)
                              ) () f
        in cleanInterpolant f'
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
    cleanInterpolant (App (SMTDivisible n) x) = App SMTEq [App (SMTIntArith Mod) (x,Const n ()),Const 0 ()]
    cleanInterpolant e = e

    removeToReal :: SMTExpr Rational -> Maybe (SMTExpr Integer)
    removeToReal (App SMTToReal e) = Just e
    removeToReal _ = Nothing

    negateInterpolant :: SMTExpr Bool -> SMTExpr Bool
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

    pushNegation :: SMTExpr Bool -> SMTExpr Bool
    pushNegation (App SMTNot e) = negateInterpolant e
    pushNegation (App (SMTLogic op) es) = App (SMTLogic op) (fmap pushNegation es)
    pushNegation e = e

    splitInterpolant (App (SMTLogic And) es) = concat (fmap splitInterpolant es)
    -- Henning: Maybe it's a good idea not to refine with equalities:
    splitInterpolant (App SMTEq [lhs,rhs]) = case cast (lhs,rhs) of
      Just ((lhs',rhs')::(SMTExpr Integer,SMTExpr Integer)) -> [App (SMTOrd Ge) (lhs',rhs')
                                                               ,App (SMTOrd Gt) (lhs',rhs')]
      Nothing -> [App SMTEq [lhs,rhs]]
    splitInterpolant (App (SMTOrd Gt) (lhs,rhs)) = [App (SMTOrd Ge) (lhs,rhs)
                                                   ,App (SMTOrd Gt) (lhs,rhs)]
    splitInterpolant e = [e]

    translateToMathSAT :: SMTExpr a -> SMTExpr a
    translateToMathSAT (App SMTEq [App (SMTIntArith Mod) (x,Const n ()),y])
      = App (SMTDivisible n) (x-y)
    translateToMathSAT (App SMTEq [y,App (SMTIntArith Mod) (x,Const n ())])
      = App (SMTDivisible n) (x-y)
    translateToMathSAT (App (SMTLogic And) []) = constant True
    translateToMathSAT (App f args)
      = let args1 = fromArgs args
            args2 = fmap (\(UntypedExpr e)
                          -> UntypedExpr $ translateToMathSAT e
                         ) args1
            Just (args3,[]) = toArgs (extractArgAnnotation args) args2
        in App f args3
    translateToMathSAT x = x

mic :: TR.TransitionRelation mdl
       => Int -> AbstractState (TR.State mdl)
       -> IC3 mdl (AbstractState (TR.State mdl))
mic level ast = do
  updateStats (\stats -> stats { numMIC = (numMIC stats)+1 })
  mic' level ast 1

mic' :: TR.TransitionRelation mdl
        => Int -> AbstractState (TR.State mdl) -> Int
        -> IC3 mdl (AbstractState (TR.State mdl))
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
           => Int -> AbstractState (TR.State mdl) -> Int -> Int -> Int
           -> IC3 mdl (Maybe (AbstractState (TR.State mdl)))
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
                           abstractCtg <- liftIO $ domainAbstract
                                          (\x -> app and' $ assignPartial' x (stateLifted ctg)
                                          ) initialPred domain
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

addAbstractCube :: Int -> AbstractState (TR.State mdl) -> IC3 mdl ()
addAbstractCube lvl st
  = modify (\env -> let (st_id,cons') = getCubeId st (ic3Consecution env)
                        cons'' = addCubeAtLevel st_id lvl cons'
                    in env { ic3Consecution = cons''
                           , ic3Earliest = min (ic3Earliest env) lvl })

addSuggestedPredicates :: TR.TransitionRelation mdl => IC3 mdl ()
addSuggestedPredicates = do
  mdl <- asks ic3Model
  domain <- gets ic3Domain
  ndomain <- foldlM (\cdomain (unique,trm) -> do
                        (_,ndom) <- if unique
                                    then liftIO $ domainAddUniqueUnsafe trm cdomain
                                    else liftIO $ domainAdd trm cdomain
                        return ndom
                    ) domain (TR.suggestedPredicates mdl)
  modify $ \env -> env { ic3Domain = ndomain }

renderState :: TR.TransitionRelation mdl => PartialValue (TR.State mdl) -> IC3 mdl String
renderState st = do
  mdl <- asks ic3Model
  TR.renderPartialState mdl st

renderAbstractState :: AbstractState (TR.State mdl)
                       -> IC3 mdl String
renderAbstractState st = do
  domain <- gets ic3Domain
  liftIO $ renderDomainTerm st domain

-- | Dump the internal IC3 data-structures
ic3Dump :: IC3 mdl ()
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

checkFixpoint :: TR.TransitionRelation mdl => [AbstractState (TR.State mdl)] -> IC3 mdl ()
checkFixpoint abs_fp = do
  mdl <- asks ic3Model
  domain <- gets ic3Domain
  let fp = getFixpoint domain abs_fp
  backend <- liftIO $ {-fmap (namedDebugBackend "fp") $-} createSMTPipe "z3" ["-in","-smt2"]
  liftIO $ withSMTBackendExitCleanly backend $ do
    setOption (ProduceModels True)
    incorrectInitial <- stack $ do
      cur <- TR.createStateVars "" mdl
      assert $ TR.initialState mdl cur
      assert $ not' (fp cur)
      checkSat
    when incorrectInitial (error "Fixpoint doesn't cover initial condition")
    stack $ do
      cur <- TR.createStateVars "" mdl
      inp <- TR.createInputVars "" mdl
      assert $ TR.stateInvariant mdl inp cur
      assert $ fp cur
      (asserts,real0) <- TR.declareAssertions mdl cur inp (TR.startingProgress mdl)
      assert $ app and' asserts
      (assumps,real1) <- TR.declareAssumptions mdl cur inp real0
      assert $ app and' assumps
      (nxt,real2) <- TR.declareNextState mdl cur inp Nothing real1
      inp' <- TR.createInputVars "nxt" mdl
      (asserts',real0') <- TR.declareAssertions mdl nxt inp' (TR.startingProgress mdl)
      assert $ not' $ app and' asserts'
      (assumps',real1') <- TR.declareAssumptions mdl nxt inp' real0'
      assert $ app and' assumps'
      assert $ TR.stateInvariant mdl inp' nxt
      errorReachable <- checkSat
      when errorReachable (do
                               curSt <- getValues cur >>= TR.renderState mdl
                               curInpSt <- getValues inp >>= TR.renderInput mdl
                               nxtSt <- getValues nxt >>= TR.renderState mdl
                               nxtInpSt <- getValues inp' >>= TR.renderInput mdl
                               error $ "Fixpoint doesn't imply property.\nState:\n"++
                                 curSt++"\nInput:\n"++curInpSt++"\nNext state:\n"++nxtSt++"\nNext input:\n"++nxtInpSt
                          )
    stack $ do
      cur <- TR.createStateVars "" mdl
      inp <- TR.createInputVars "" mdl
      assert $ TR.stateInvariant mdl inp cur
      assert $ fp cur
      (asserts,real0) <- TR.declareAssertions mdl cur inp (TR.startingProgress mdl)
      assert $ app and' asserts
      (assumps,real1) <- TR.declareAssumptions mdl cur inp real0
      assert $ app and' assumps
      (nxt,real2) <- TR.declareNextState mdl cur inp Nothing real1
      nxt_inp <- TR.createInputVars "" mdl
      assert $ TR.stateInvariant mdl nxt_inp nxt
      assert $ not' $ fp nxt
      incorrectFix <- checkSat
      when incorrectFix (do
                             curSt <- getValues cur >>= TR.renderState mdl
                             curInpSt <- getValues inp >>= TR.renderInput mdl
                             nxtSt <- getValues nxt >>= TR.renderState mdl
                             nxtInpSt <- getValues nxt_inp >>= TR.renderInput mdl
                             fpSt <- liftIO $ mapM (\e -> renderDomainTerm e domain
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
                                     assert $ toDomainTerm e domain nxt
                                     reachable <- checkSat
                                     when reachable $ liftIO $ do
                                       cube <- renderDomainTerm e domain
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

ic3DumpStats :: Maybe [AbstractState (TR.State mdl)] -> IC3 mdl ()
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
     numPreds <- gets (domainHash.ic3Domain)
     let (numCl,numLit) = foldl (\(numCl,numLit) st -> (numCl+1,numLit+Vec.length st))
                          (0,0) (case fp of
                                  Nothing -> []
                                  Just rfp -> rfp)
     liftIO $ do
       putStrLn $ "Level: "++show level
       putStrLn $ "Total runtime: "++show (diffUTCTime curTime (startTime stats))
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
   Nothing -> return ()
  dumpDomain <- asks ic3DumpDomainFile
  case dumpDomain of
    Nothing -> return ()
    Just fn -> do
      domain <- gets ic3Domain
      str <- liftIO $ renderDomain domain
      liftIO $ writeFile fn str

addTiming :: IORef NominalDiffTime -> IORef Int -> IO (AnyBackend IO) -> IO (AnyBackend IO)
addTiming time_ref num_ref act = do
  AnyBackend b <- act
  return $ AnyBackend $ timingBackend (\t -> modifyIORef' time_ref (+t) >>
                                             modifyIORef' num_ref (+1)
                                      ) b

addEmulation :: IO (AnyBackend IO) -> IO (AnyBackend IO)
addEmulation act = do
  AnyBackend b <- act
  return $ AnyBackend $ emulateDataTypes b

addDebugging :: String -> IO (AnyBackend IO) -> IO (AnyBackend IO)
addDebugging name act = do
  AnyBackend b <- act
  return $ AnyBackend $ namedDebugBackend name b

addModulusEmulation :: IO (AnyBackend IO) -> IO (AnyBackend IO)
addModulusEmulation act = do
  AnyBackend b <- act
  return $ AnyBackend $ modulusEmulator True b
