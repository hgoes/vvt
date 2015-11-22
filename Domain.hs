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

import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Backend (SMTMonad)

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
import Data.GADT.Show
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

-- Test Modules
--import Language.SMTLib2.Pipe
import "mtl" Control.Monad.Trans (liftIO)

data DomainVar a = forall t. GetType t => DomainVar (RevComp a t)

-- | Stores a lattice of abstractions.
--   An edge from A to B signifies that A includes B
data Domain a = forall b. (Backend b,SMTMonad b ~ IO)
                => Domain { domainGArg :: a (RevComp a)
                          , domainGraph :: Gr (CompositeExpr a BoolType,
                                               DMap (RevComp a) NoVar) ()
                          , domainNodesRev :: Map (CompositeExpr a BoolType) Node
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
              -> IO (Domain a)
initialDomain verb backend ann = do
  let initInst = do
        top <- [expr| true |]
        bot <- [expr| false |]
        return DomainInstance { domainNodes = Map.fromList
                                                [(domainTop,top)
                                                ,(domainBot,bot)]
                                , domainInstNext = 2
                                , domainIsFresh = True }
      gArg = runIdentity $ createComposite (\rev -> return rev) ann
  supportsTimeouts <- withBackendExitCleanly backend $ do
    name <- getInfo SMTSolverName
    return $ name=="Z3"
  pool <- createSMTPool' backend initInst $ do
    setOption (ProduceModels True)
    createComposite (\_ -> declareVar) ann
  return $ Domain { domainGraph = mkGraph
                                  [(domainTop,(CompositeExpr (Const (BoolValue True)),DMap.empty))
                                  ,(domainBot,(CompositeExpr (Const (BoolValue False)),DMap.empty))]
                                  [(domainTop,domainBot,())]
                  , domainGArg = gArg
                  , domainNodesRev = Map.fromList
                                     [(CompositeExpr (Const (BoolValue True)),domainTop)
                                     ,(CompositeExpr (Const (BoolValue False)),domainBot)]
                  , domainNextNode = 2
                  , domainPool = pool
                  , domainVerbosity = verb
                  , domainTimeout = if supportsTimeouts
                                    then Just 2000
                                    else Nothing
                  }

updateInstance :: (Backend b,Composite a) => Domain a -> DomainInstance (Expr b) -> a (Expr b)
               -> SMT b (DomainInstance (Expr b))
updateInstance dom inst vars
  = foldlM (\cinst nd -> do
               let Just (prop,_) = lab (domainGraph dom) nd
               cprop <- concretizeExpr vars prop
               cprop' <- defineVar cprop
               return (cinst { domainNodes = Map.insert nd cprop (domainNodes cinst)
                             })
           ) (inst { domainInstNext = domainNextNode dom })
    [(domainInstNext inst)..(domainNextNode dom)-1]

domainTop,domainBot :: Node
domainTop = 0
domainBot = 1

quickImplication :: (Extract i e)
                 => AnalyzedExpr i e BoolType
                 -> AnalyzedExpr i e BoolType
                 -> Maybe Bool
quickImplication [expr| false |] _ = Just True
quickImplication _ [expr| true |] = Just True
quickImplication [expr| true |] [expr| (<=.int (var $a) (var $b)) |]
  = Just (defaultEq a b)
quickImplication [expr| true |] [expr| (>=.int (var $a) (var $b)) |]
  = Just (defaultEq a b)
quickImplication
  [expr| (<.int (var $a1) (var $a2)) |]
  [expr| (<.int (var $b1) (var $b2)) |]
  = Just $ (defaultEq a1 b1) && (defaultEq a2 b2)
quickImplication
  [expr| (= (var $a1) (var $a2)) |]
  [expr| (= (var $b1) (var $b2)) |]
  = Just $ ((defaultEq a1 b1) && (defaultEq a2 b2)) ||
    ((defaultEq a1 b2) && (defaultEq a2 b1))
quickImplication
  [expr| (<=.int (var $a1) (var $a2)) |]
  [expr| (<=.int (var $b1) (var $b2)) |]
  = Just (defaultEq a1 b1 && defaultEq a2 b2)
quickImplication
  [expr| (<.int (var $a1) (var $a2)) |]
  [expr| (<=.int (var $b1) (var $b2)) |]
  = Just (defaultEq a1 b1 && defaultEq a2 b2)
quickImplication
  [expr| (<=.int (var $_) (var $_)) |]
  [expr| (<.int (var $_) (var $_)) |]
  = Just False
quickImplication
  [expr| (>.int (var $a1) (var $a2)) |]
  [expr| (>.int (var $b1) (var $b2)) |]
  = Just (defaultEq a1 b1 && defaultEq a2 b2)
quickImplication
  [expr| (>.int (var $a1) (var $a2)) |]
  [expr| (<=.int (var $b1) (var $b2)) |]
  = Just (defaultEq a2 b1 && defaultEq a1 b2)
quickImplication
  [expr| (<=.int (var $_) (var $_)) |]
  [expr| (>.int (var $_) (var $_)) |]
  = Just False
quickImplication
  [expr| (>.int (var $a1) (var $a2)) |]
  [expr| (<.int (var $b1) (var $b2)) |]
  = Just (defaultEq a1 b2 && defaultEq a2 b1)
quickImplication
  [expr| (<.int (var $a1) (var $a2)) |]
  [expr| (>.int (var $b1) (var $b2)) |]
  = Just (defaultEq a1 b2 && defaultEq a2 b1)
quickImplication
  [expr| (var $a) |]
  [expr| (var $b) |]
  = Just (defaultEq a b)
quickImplication [expr| (var $_) |] _
  = Just False
quickImplication _ [expr| (var $_) |]
  = Just False
quickImplication _ _ = Nothing

checkImplication :: Backend b => Expr b BoolType -> Expr b BoolType -> SMT b Bool
checkImplication e1 e2 = stack $ do
  assert e1
  [expr| (not e2) |] >>= assert
  r <- checkSat
  return $ r==Unsat

-- | Like `domainAdd` but the caller has to guarantee that the predicate is neither a sub- nor a super-set of any predicate in the domain.
domainAddUniqueUnsafe :: Composite a => CompositeExpr a BoolType
                      -> Domain a
                      -> IO (Node,Domain a)
domainAddUniqueUnsafe pred dom = do
  let vars = collectRevVars DMap.empty pred
      newNd = domainNextNode dom
      gr0 = insNode (newNd,(pred,vars)) (domainGraph dom)
      gr1 = insEdge (domainTop,newNd,()) gr0
      gr2 = insEdge (newNd,domainBot,()) gr1
  return (newNd,dom { domainGraph = gr2
                    , domainNextNode = succ newNd
                    , domainNodesRev = Map.insert pred newNd
                                       (domainNodesRev dom)
                    })

-- | Add a new predicate to the domain.
--   Returns the node representing the new predicate.
domainAdd :: Composite a => CompositeExpr a BoolType -- ^ The predicate.
          -> Domain a -- ^ The domain to which to add the predicate
          -> IO (Node,Domain a)
domainAdd pred dom = case Map.lookup pred (domainNodesRev dom) of
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
                  --termStr <- renderDomainPred pred dom
                  liftIO $ putStrLn $ "Adding predicate "++show pred)
         else return ()
       let newNd = domainNextNode dom
           gr0 = insNode (newNd,(pred,vars)) (domainGraph dom)
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
                         , domainNodesRev = Map.insert pred newNd
                                            (domainNodesRev dom)
                         })
  where
    vars = collectRevVars DMap.empty pred
    apred = analyze' () pred
    poseQuery :: Composite a => Domain a
              -> (forall b. Backend b => DomainInstance (Expr b) -> a (Expr b) -> SMT b [Expr b BoolType])
              -> IO Bool
    poseQuery dom query = do
      res <- case dom of
        Domain { domainPool = pool }
          -> withSMTPool' pool $
             \inst vars -> do
               ninst <- updateInstance dom inst vars
               let ninst' = ninst { domainIsFresh = False }
               query' <- query ninst' vars
               res <- stack $ do
                 mapM_ assert query'
                 checkSatWith Nothing (noLimits { limitTime = domainTimeout dom })
               case res of
                Sat -> return (Right (True,ninst'))
                Unsat -> return (Right (False,ninst'))
                Unknown -> do
                  if domainIsFresh ninst
                    then (do
                             let strs :: [String]
                                 strs = fmap (\e -> gshowsPrec 0 e "") query'
                             return $ Left (Just strs))
                    else return $ Left Nothing
      case res of
       Left (Just exprs) -> error $ "Solver got stuck while trying to check "++
                            show (exprs::[String])
       Left Nothing -> poseQuery dom query
       Right res -> return res
    findParents cur = do
      let curCtx = context (domainGraph dom) cur
          (curTerm,curTermVars) = lab' curCtx
      impl <- case quickImplication apred (analyze' () curTerm) of
               Just r -> return r
               Nothing -> fmap not $ poseQuery dom
                          (\inst vars -> do
                              pred' <- concretizeExpr vars pred
                              term' <- concretizeExpr vars curTerm
                              nterm <- [expr| (not term') |]
                              return [pred',nterm])
      if not impl
        then return Nothing
        else (do
                 parents <- mapM findParents (suc' curCtx)
                 case catMaybes parents of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))
    findChildren cur = do
      let curCtx = context (domainGraph dom) cur
          (curTerm,curTermVars) = lab' curCtx
      impl <- case quickImplication (analyze' () curTerm) apred of
               Just r -> return r
               Nothing -> fmap not $ poseQuery dom
                          (\inst vars -> do
                              term' <- concretizeExpr vars curTerm
                              pred' <- concretizeExpr vars pred
                              npred <- [expr| (not pred') |]
                              return [term',npred])
      if not impl
        then return Nothing
        else (do
                 childs <- mapM findChildren (pre' curCtx)
                 case catMaybes childs of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))

-- | Create an abstract state from a concrete state.
domainAbstract :: Composite a
               => CompositeExpr a BoolType  -- ^ An expression which describes the concrete state
               -> Node -- ^ A property that must be considered
               -> Domain a -- ^ The domain to use for the abstraction
               -> IO (AbstractState a)
domainAbstract expr mustUse dom = do
  Right res <- case dom of
    Domain { domainPool = pool }
      -> withSMTPool' pool $ \inst vars -> do
      ninst <- updateInstance dom inst vars
      lst <- stack $ do
        concretizeExpr vars expr >>= assert
        let reprs = filter (\(nd,_) -> nd/=domainTop && nd/=domainBot) $
                    Map.toList $ domainNodes ninst
        sol <- checkSat
        when (sol/=Sat) (error $ "Concrete state "++show expr++
                         " doesn't have a valid abstraction")
        mapM (\(nd,repr) -> do
                 let Just (_,predVars) = lab (domainGraph dom) nd
                 if nd==mustUse || (DMap.null $ DMap.difference predVars exprVars)
                   then (do
                            BoolValueC c <- getValue repr
                            return $ Just (nd,c))
                   else return Nothing
             ) reprs
      return (Right (catMaybes lst,ninst))
  return (Vec.fromList res)
  where
    exprVars = collectRevVars DMap.empty expr

-- | Create an SMT expression that represents an abstract state.
toDomainTerm :: (Embed m e,Composite a)
             => AbstractState a -- ^ The abstract state to represent
             -> Domain a -- ^ The domain to use (The abstract state must have been created using this domain)
             -> a e -- ^ An instance of the abstracted data type
             -> m (e BoolType)
toDomainTerm state dom vars = do
  conj <- mapM (\(nd,act) -> do
                  let Just (pred,_) = lab (domainGraph dom) nd
                  pr <- concretizeExpr vars pred
                  if act
                    then return pr
                    else (do
                      npr <- [expr| (not pr) |]
                      return npr)
               ) (Vec.toList state)
  case conj of
    [] -> [expr| true |]
    [x] -> return x
    xs -> [expr| (and # xs) |]
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

renderDomainTerm :: Composite a => AbstractState a -> Domain a -> String
renderDomainTerm st (Domain { domainGraph = gr })
  = let exprs = [ if act
                  then show pred
                  else "!"++show pred
                | (nd,act) <- Vec.toList st,
                  let Just (pred,_) = lab gr nd]
    in "{"++intercalate ", " exprs++"}"
{-
renderDomainPred :: (a -> SMTExpr Bool) -> Domain a -> IO String
renderDomainPred pred dom
  = withSMTPool (domainPool dom) $
    \vars -> renderExpr (pred vars)
-}

renderDomain :: Composite a => Domain a -> String
renderDomain (Domain { domainGraph = gr })
  = unlines $ ["digraph domain {"]++nodes++edges++["}"]
  where
    nodes = fmap (\(nd,(pred,_)) -> "nd"++show nd++"[label=\""++show pred++"\"];"
                 ) (labNodes gr)
    edges = fmap (\(n1,n2,_) -> "nd"++show n1++" -> nd"++show n2++";"
                 ) (labEdges gr)
