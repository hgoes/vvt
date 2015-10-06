{-# LANGUAGE ExistentialQuantification,FlexibleContexts,PackageImports,GADTs,ScopedTypeVariables #-}
module Domain
      {- (Domain()
       ,AbstractState()
       ,initialDomain
       ,toDomainTerm
       ,toDomainTerms
       ,domainAdd
       ,domainAbstract
       ,domainAddUniqueUnsafe
       ,domainHash
       ,renderDomainTerm
       ,renderDomain
       )-} where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Backend hiding (setOption,getInfo,toBackend,checkSat,getValue)
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.LowLevel hiding (assert)

import Args
import SMTPool

import Control.Monad.Identity
import Data.Graph.Inductive
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (delete,intercalate)
import Data.Foldable
import Prelude hiding (foldl,mapM_)
import Control.Monad (when)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Typeable
import Data.GADT.Compare

-- Test Modules
--import Language.SMTLib2.Pipe
import "mtl" Control.Monad.Trans (liftIO)

newtype Predicate a
  = Predicate (forall m e v qv fun con field fv. Monad m
               => (forall t. GetType t
                   => Expression v qv fun con field fv e t
                   -> m (e t)) -> a e -> m (e BoolType))

newtype DomainExpr a t
  = DomainExpr (Expression (RevComp a) NoVar NoFun NoCon NoField NoVar (DomainExpr a) t)

instance Composite a => GEq (DomainExpr a) where
  geq (DomainExpr x) (DomainExpr y) = geq x y
instance Composite a => GCompare (DomainExpr a) where
  gcompare (DomainExpr x) (DomainExpr y) = gcompare x y
instance Composite a => Eq (DomainExpr a t) where
  (==) = defaultEq
instance Composite a => Ord (DomainExpr a t) where
  compare = defaultCompare

data DomainVar a = forall t. GetType t => DomainVar (RevComp a t)

-- | Stores a lattice of abstractions.
--   An edge from A to B signifies that A includes B
data Domain a = forall b. (Backend b,SMTMonad b ~ IO)
                => Domain { domainGArg :: a (RevComp a)
                          , domainGraph :: Gr (Predicate a,DomainExpr a BoolType,Set (DomainVar a)) ()
                          , domainNodesRev :: Map (DomainExpr a BoolType) Node
                          , domainNextNode :: Node
                          , domainPool :: SMTPool (DomainInstance (Expr b)) b a
                          , domainVerbosity :: Int
                          , domainTimeout :: Maybe Integer
                          }

data DomainInstance e = DomainInstance { domainNodes :: Map Node (e BoolType)
                                       , domainInstNext :: Node
                                       , domainIsFresh :: Bool
                                       }

-- | An abstract state is a partial mapping of predicates to true or false, indicating whether or not a predicate is true or false in the abstracted state.
type AbstractState a = Vector (Node,Bool)

-- | Create the initial domain containing only true and false.
initialDomain :: (Composite a,Backend b,SMTMonad b ~ IO)
              => Int -- ^ How verbose the domain should be (0 = no output)
              -> IO b -- ^ A function to create SMT backends
              -> CompDescr a -- ^ The annotation for the data type abstracted by the domain
              -> (forall m e. Monad m
                  => (forall t. GetType t
                      => RevComp a t -> m (e t)) -> m (a e)
                 ) -- ^ An SMT action to create an instance of the abstracted data type
              -> IO (Domain a)
initialDomain verb backend ann alloc = do
  let initInst = do
        top <- toBackend (Const (BoolValue True))
        bot <- toBackend (Const (BoolValue False))
        return DomainInstance { domainNodes = Map.fromList
                                                [(domainTop,top)
                                                ,(domainBot,bot)]
                                , domainInstNext = 2
                                , domainIsFresh = True }
      gArg = runIdentity $ alloc (\rev -> return rev)
  supportsTimeouts <- do
    back <- backend
    withBackendExitCleanly back $ do
      name <- getInfo SMTSolverName
      return $ name=="Z3"
  pool <- createSMTPool' backend initInst $ do
    setOption (ProduceModels True)
    alloc (\_ -> updateBackend $ \b -> do
                   (v,b1) <- declareVar b Nothing
                   B.toBackend b1 (Var v)
          )
  return $ Domain { domainGraph = mkGraph
                                  [(domainTop,(Predicate $ \f _ -> f (Const (BoolValue True)),
                                               DomainExpr (Const (BoolValue True)),Set.empty))
                                  ,(domainBot,(Predicate $ \f _ -> f (Const (BoolValue False)),
                                               DomainExpr (Const (BoolValue False)),Set.empty))]
                                  [(domainTop,domainBot,())]
                  , domainGArg = gArg
                  , domainNodesRev = Map.fromList
                                     [(DomainExpr (Const (BoolValue True)),domainTop)
                                     ,(DomainExpr (Const (BoolValue False)),domainBot)]
                  , domainNextNode = 2
                  , domainPool = pool
                  , domainVerbosity = verb
                  , domainTimeout = if supportsTimeouts
                                    then Just 2000
                                    else Nothing
                  }

updateInstance :: Backend b => Domain a -> DomainInstance (Expr b) -> a (Expr b)
               -> SMT b (DomainInstance (Expr b))
updateInstance dom inst vars
  = foldlM (\cinst nd -> do
               let Just (Predicate prop,_,_) = lab (domainGraph dom) nd
               cprop <- prop toBackend vars
               cprop' <- updateBackend $ \b -> defineVar b (Just "pred") cprop
               return (cinst { domainNodes = Map.insert nd cprop (domainNodes cinst)
                             })
           ) (inst { domainInstNext = domainNextNode dom })
    [(domainInstNext inst)..(domainNextNode dom)-1]

domainTop,domainBot :: Node
domainTop = 0
domainBot = 1
{-
generalizePredicate :: Domain a -> (a -> SMTExpr Bool) -> (SMTExpr Bool,Set Integer)
generalizePredicate dom pred = (qpred,vars)
  where
    qpred = pred (domainGArg dom)
    (vars,_) = foldExpr (\cur expr
                         -> (case expr of
                              InternalObj i _ -> case cast i of
                                Just i' -> Set.insert i' cur
                                Nothing -> cur
                              _ -> cur,expr)
                        ) Set.empty qpred

quickImplication :: SMTExpr Bool -> SMTExpr Bool -> Maybe Bool
quickImplication (Const False ()) _ = Just True
quickImplication _ (Const True ()) = Just True
quickImplication (Const True ()) (App (SMTOrd Le) (InternalObj a _,InternalObj b _))
  = Just $ a `tpEq` b
quickImplication (Const True ()) (App (SMTOrd Ge) (InternalObj a _,InternalObj b _))
  = Just $ a `tpEq` b
quickImplication (Const True ()) (App (SMTOrd _) (InternalObj _ _,InternalObj _ _))
  = Nothing
quickImplication (App (SMTOrd Lt) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Lt) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a1 `tpEq` b1 && a2 `tpEq` b2
quickImplication (App SMTEq [InternalObj a1 _,InternalObj a2 _]) (App SMTEq [InternalObj b1 _,InternalObj b2 _])
  | a1 `tpEq` b1 && a2 `tpEq` b2 = Just True
  | a1 `tpEq` b2 && a2 `tpEq` b1 = Just True
  | otherwise = Just False
--quickImplication (App (SMTOrd Lt) _) (App SMTEq _) = Just False
--quickImplication (App SMTEq _) (App (SMTOrd Lt) _) = Just False
quickImplication (App (SMTOrd Le) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Le) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a1 `tpEq` b1 && a2 `tpEq` b2
quickImplication (App (SMTOrd Lt) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Le) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a1 `tpEq` b1 && a2 `tpEq` b2
quickImplication (App (SMTOrd Le) (InternalObj _ _,InternalObj _ _)) (App (SMTOrd Lt) (InternalObj _ _,InternalObj _ _))
  = Just False
quickImplication (App (SMTOrd Gt) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Gt) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a1 `tpEq` b1 && a2 `tpEq` b2
quickImplication (App (SMTOrd Gt) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Le) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a2 `tpEq` b1 && a1 `tpEq` b2
quickImplication (App (SMTOrd Le) (InternalObj _ _,InternalObj _ _)) (App (SMTOrd Gt) (InternalObj _ _,InternalObj _ _))
  = Just False
quickImplication (App (SMTOrd Gt) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Lt) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a1 `tpEq` b2 && a2 `tpEq` b1
quickImplication (App (SMTOrd Lt) (InternalObj a1 _,InternalObj a2 _)) (App (SMTOrd Gt) (InternalObj b1 _,InternalObj b2 _))
  = Just $ a1 `tpEq` b2 && a2 `tpEq` b1
quickImplication (InternalObj a _) (InternalObj b _)
  = Just $ a `tpEq` b
quickImplication (InternalObj _ _) _ = Just False
quickImplication _ (InternalObj _ _) = Just False
quickImplication _ _ = Nothing

tpEq :: (Typeable a,Eq a,Typeable b) => a -> b -> Bool
tpEq x y = case cast y of
  Just y' -> x==y'

checkImplication :: SMTExpr Bool -> SMTExpr Bool -> SMT Bool
checkImplication e1 e2 = stack $ do
  assert e1
  assert (not' e2)
  r <- checkSat
  return $ not r

-- | Like `domainAdd` but the caller has to guarantee that the predicate is neither a sub- nor a super-set of any predicate in the domain.
domainAddUniqueUnsafe :: Args a => (a -> SMTExpr Bool) -> Domain a -> IO (Node,Domain a)
domainAddUniqueUnsafe pred dom = do
  let (qpred,vars) = generalizePredicate dom pred
      newNd = domainNextNode dom
      gr0 = insNode (newNd,(pred,qpred,vars)) (domainGraph dom)
      gr1 = insEdge (domainTop,newNd,()) gr0
      gr2 = insEdge (newNd,domainBot,()) gr1
  return (newNd,dom { domainGraph = gr2
                    , domainNextNode = succ newNd
                    , domainNodesRev = Map.insert qpred newNd
                                       (domainNodesRev dom)
                    })

-- | Add a new predicate to the domain.
--   Returns the node representing the new predicate.
domainAdd :: Args a => (a -> SMTExpr Bool) -- ^ The predicate as a boolean function over the abstracted data type.
          -> Domain a -- ^ The domain to which to add the predicate
          -> IO (Node,Domain a)
domainAdd pred dom = case Map.lookup qpred (domainNodesRev dom) of
  Just nd -> return (nd,dom)
  Nothing -> do
    Just parents <- findParents domainTop
    Just childs <- findChildren domainBot
    let intersection = Set.intersection parents childs
    case Set.toList intersection of -- Is the term redundant?
     [equiv] -> return (equiv,dom)
     [] -> do
       if domainVerbosity dom >= 2
         then (do
                  termStr <- renderDomainPred pred dom
                  liftIO $ putStrLn $ "Adding predicate "++termStr)
         else return ()
       let newNd = domainNextNode dom
           gr0 = insNode (newNd,(pred,qpred,vars)) (domainGraph dom)
           gr1 = foldl (\cgr parent
                        -> let (Just (pred,_,pterm,succs),cgr') = match parent cgr
                               succs' = foldl (\csucc x -> delete ((),x) csucc) succs childs
                               succs'' = ((),newNd):succs'
                           in (pred,parent,pterm,succs'') & cgr'
                       ) gr0 parents
           gr2 = foldl (\cgr child
                        -> let (Just (pred,_,cterm,succs),cgr') = match child cgr
                               pred' = foldl (\cpred x -> delete ((),x) cpred) pred parents
                               pred'' = ((),newNd):pred'
                           in (pred'',child,cterm,succs) & cgr'
                       ) gr1 childs
       return (newNd,dom { domainGraph = gr2
                         , domainNextNode = succ newNd
                         , domainNodesRev = Map.insert qpred newNd
                                            (domainNodesRev dom)
                         })
  where
    (qpred,vars) = generalizePredicate dom pred
    poseQuery query = do
      res <- withSMTPool' (domainPool dom) $
             \inst vars -> do
               ninst <- updateInstance dom inst vars
               let ninst' = ninst { domainIsFresh = False }
                   query' = query ninst' vars
               res <- stack $ do
                 mapM_ assert query'
                 checkSat' Nothing (noLimits { limitTime = domainTimeout dom })
               case res of
                Sat -> return (Right (True,ninst'))
                Unsat -> return (Right (False,ninst'))
                Unknown -> do
                  if domainIsFresh ninst
                    then (do
                             strs <- mapM renderExpr query'
                             return $ Left (Just strs))
                    else return $ Left Nothing
      case res of
       Left (Just exprs) -> error $ "Solver got stuck while trying to check "++
                            show exprs
       Left Nothing -> poseQuery query
       Right res -> return res
    findParents cur = do
      let curCtx = context (domainGraph dom) cur
          (curTermF,curTermQ,curTermVars) = lab' curCtx
      impl <- case quickImplication qpred curTermQ of
               Just r -> return r
               Nothing -> fmap not $ poseQuery (\inst vars -> [pred vars,not' $ curTermF vars])
      if not impl
        then return Nothing
        else (do
                 parents <- mapM findParents (suc' curCtx)
                 case catMaybes parents of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))
    findChildren cur = do
      let curCtx = context (domainGraph dom) cur
          (curTermF,curTermQ,curTermVars) = lab' curCtx
      impl <- case quickImplication curTermQ qpred of
               Just r -> return r
               Nothing -> fmap not $ poseQuery (\inst vars -> [curTermF vars,not' $ pred vars])
      if not impl
        then return Nothing
        else (do
                 childs <- mapM findChildren (pre' curCtx)
                 case catMaybes childs of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))

-- | Create an abstract state from a concrete state.
domainAbstract :: (a -> SMT b (Expr b BoolType))  -- ^ An expression which describes the concrete state
               -> Node -- ^ A property that must be considered
               -> Domain a -- ^ The domain to use for the abstraction
               -> IO (AbstractState a)
domainAbstract expr mustUse dom = do
  Right res <- withSMTPool' (domainPool dom) $ \inst vars -> do
    ninst <- updateInstance dom inst vars
    lst <- stack $ do
      updateBackend' $ \b -> assert b (expr vars)
      let reprs = filter (\(nd,_) -> nd/=domainTop && nd/=domainBot) $
                  Map.toList $ domainNodes ninst
      sol <- checkSat
      when (not sol) (error $ "Concrete state "++show (expr vars)++
                      " doesn't have a valid abstraction")
      mapM (\(nd,repr) -> do
               let Just (_,_,predVars) = lab (domainGraph dom) nd
               if nd==mustUse || (Set.null $ Set.difference predVars exprVars)
                 then (do
                          c <- getValue repr
                          return $ Just (nd,c))
                 else return Nothing
           ) reprs
    return (Right (catMaybes lst,ninst))
  return (Vec.fromList res)
  where
    (_,exprVars) = generalizePredicate dom expr
-}
-- | Create an SMT expression that represents an abstract state.
toDomainTerm :: Backend b
             => AbstractState a -- ^ The abstract state to represent
             -> Domain a -- ^ The domain to use (The abstract state must have been created using this domain)
             -> a (Expr b) -- ^ An instance of the abstracted data type
             -> SMT b (Expr b BoolType)
toDomainTerm state dom vars = do
  conj <- mapM (\(nd,act) -> do
                  let Just (Predicate term,_,_) = lab (domainGraph dom) nd
                  pr <- term toBackend vars
                  if act
                    then return pr
                    else (do
                      npr <- toBackend (App Not (Arg pr NoArg))
                      return npr)
               ) (Vec.toList state)
  case conj of
    [] -> toBackend (Const (BoolValue True))
    [x] -> return x
    xs -> allEqFromList xs $ \arg -> toBackend (App (Logic And) arg)
{-
toDomainTerms :: AbstractState a -> Domain a -> a -> Vector (Node,SMTExpr Bool,Bool)
toDomainTerms state dom vars
  = fmap (\(nd,act) -> let Just (term,_,_) = lab (domainGraph dom) nd
                       in (nd,term vars,act)
         ) state
-}
-- | Since a domain can only grow, we can hash its "version" using its size.
domainHash :: Domain a -> Int
domainHash dom = domainNextNode dom

domainRelativize :: (forall v qv fun con field fv t.
                     Expression v qv fun con field fv e t
                     -> m (e t))
                 -> (forall t. GetType t => Var b t -> RevComp a t)
                 -> Expr b t
                 -> a e -> m (e t)

{-
renderDomainTerm :: AbstractState a -> Domain a -> IO String
renderDomainTerm st dom
  = withSMTPool (domainPool dom) $
    \vars -> do
      let exprs = [ if act
                    then term vars
                    else not' $ term vars
                  | (nd,act) <- Vec.toList st,
                    let Just (term,_,_) = lab (domainGraph dom) nd]
      strs <- mapM renderExpr exprs
      return $ "{"++intercalate ", " strs++"}"

renderDomainPred :: (a -> SMTExpr Bool) -> Domain a -> IO String
renderDomainPred pred dom
  = withSMTPool (domainPool dom) $
    \vars -> renderExpr (pred vars)

renderDomain :: Domain a -> IO String
renderDomain dom
  = withSMTPool (domainPool dom) $
    \vars -> do
      nodes <- mapM (\(nd,(pred,_,_)) -> do
                         res <- renderExpr (pred vars)
                         return $ "nd"++show nd++"[label=\""++res++"\"];"
                    ) $ labNodes (domainGraph dom)
      edges <- mapM (\(n1,n2,_) -> return $ "nd"++show n1++" -> nd"++show n2++";"
                    ) $ labEdges (domainGraph dom)
      return $ unlines $ ["digraph domain {"]++nodes++edges++["}"]
-}
