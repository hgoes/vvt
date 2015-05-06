{-# LANGUAGE ExistentialQuantification,FlexibleContexts,PackageImports,GADTs,ScopedTypeVariables #-}
module Domain
       (Domain()
       ,AbstractState()
       ,initialDomain
       ,toDomainTerm
       ,toDomainTerms
       ,domainAdd
       ,domainAbstract
       ,domainAddUniqueUnsafe
       ,domainHash
       ,renderDomainTerm
       ) where

import Language.SMTLib2
import SMTPool
import Language.SMTLib2.Internals (SMTExpr(..),SMTFunction(..))
import Language.SMTLib2.Internals.Operators

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

-- Test Modules
import Language.SMTLib2.Pipe
import "mtl" Control.Monad.Trans (liftIO)

-- | Stores a lattice of abstractions.
--   An edge from A to B signifies that A includes B
data Domain a = Domain { domainAnnotation :: ArgAnnotation a
                       , domainGArg :: a
                       , domainGraph :: Gr (a -> SMTExpr Bool,SMTExpr Bool,Set Integer) ()
                       , domainNodesRev :: Map (SMTExpr Bool) Node
                       , domainNextNode :: Node
                       , domainPool :: SMTPool (DomainInstance a) a
                       , domainVerbosity :: Int
                       , domainTimeout :: Maybe Integer
                       }

data DomainInstance a = DomainInstance { domainNodes :: Map Node (SMTExpr Bool)
                                       , domainInstNext :: Node
                                       , domainIsFresh :: Bool
                                       }

-- | An abstract state is a partial mapping of predicates to true or false, indicating whether or not a predicate is true or false in the abstracted state.
type AbstractState a = Vector (Node,Bool)

-- | Create the initial domain containing only true and false.
initialDomain :: (Args a,SMTBackend b IO) => Int -- ^ How verbose the domain should be (0 = no output)
              -> IO b -- ^ A function to create SMT backends
              -> ArgAnnotation a -- ^ The annotation for the data type abstracted by the domain
              -> SMT a -- ^ An SMT action to create an instance of the abstracted data type
              -> IO (Domain a)
initialDomain verb backend ann (alloc::SMT a) = do
  let initInst = DomainInstance { domainNodes = Map.fromList
                                                [(domainTop,constant True)
                                                ,(domainBot,constant False)]
                                , domainInstNext = 2
                                , domainIsFresh = True }
      Just (gArg,[]) = toArgs ann
                       [InternalObj (i::Integer) tp
                       | (i,tp) <- zip [0..] (getTypes (undefined::a) ann)]
  supportsTimeouts <- do
    back <- backend
    withSMTBackendExitCleanly back $ do
      name <- getInfo SMTSolverName
      return $ name=="Z3"
  pool <- createSMTPool' backend initInst $ do
    setOption (ProduceModels True)
    alloc
  return $ Domain { domainGraph = mkGraph
                                  [(domainTop,(const $ constant True,constant True,Set.empty))
                                  ,(domainBot,(const $ constant False,constant False,Set.empty))]
                                  [(domainTop,domainBot,())]
                  , domainGArg = gArg
                  , domainNodesRev = Map.fromList
                                     [(constant True,domainTop)
                                     ,(constant False,domainBot)]
                  , domainNextNode = 2
                  , domainPool = pool
                  , domainVerbosity = verb
                  , domainAnnotation = ann
                  , domainTimeout = if supportsTimeouts
                                    then Just 2000
                                    else Nothing
                  }

updateInstance :: Domain a -> DomainInstance a -> a -> SMT (DomainInstance a)
updateInstance dom inst vars
  = foldlM (\cinst nd -> do
               let Just (prop,_,_) = lab (domainGraph dom) nd
               cprop <- defConstNamed ("pred"++show nd) (prop vars)
               return (cinst { domainNodes = Map.insert nd cprop (domainNodes cinst)
                             })
           ) (inst { domainInstNext = domainNextNode dom })
    [(domainInstNext inst)..(domainNextNode dom)-1]

domainTop,domainBot :: Node
domainTop = 0
domainBot = 1

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
domainAbstract :: (a -> SMTExpr Bool)  -- ^ An expression which describes the concrete state
                  -> Node -- ^ A property that must be considered
                  -> Domain a -- ^ The domain to use for the abstraction
                  -> IO (AbstractState a)
domainAbstract expr mustUse dom = do
  Right res <- withSMTPool' (domainPool dom) $ \inst vars -> do
    ninst <- updateInstance dom inst vars
    lst <- stack $ do
      assert (expr vars)
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

-- | Create an SMT expression that represents an abstract state.
toDomainTerm :: AbstractState a -- ^ The abstract state to represent
             -> Domain a -- ^ The domain to use (The abstract state must have been created using this domain)
             -> a -- ^ An instance of the abstracted data type
             -> SMTExpr Bool
toDomainTerm state dom vars
  = app and' [ if act
               then term vars
               else not' (term vars)
             | (nd,act) <- Vec.toList state,
               let Just (term,_,_) = lab (domainGraph dom) nd]

toDomainTerms :: AbstractState a -> Domain a -> a -> Vector (Node,SMTExpr Bool,Bool)
toDomainTerms state dom vars
  = fmap (\(nd,act) -> let Just (term,_,_) = lab (domainGraph dom) nd
                       in (nd,term vars,act)
         ) state

-- | Since a domain can only grow, we can hash its "version" using its size.
domainHash :: Domain a -> Int
domainHash dom = domainNextNode dom

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
