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

import Language.SMTLib2 hiding (simplify)
import Language.SMTLib2.Internals.Interface
import Language.SMTLib2.Internals.Expression (NoVar)
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Backend (SMTMonad)

import Args
import SMTPool
import Simplify

import Control.Monad.Identity
import Data.Graph.Inductive
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.List (delete,intercalate)
import Data.Foldable
import Prelude hiding (foldl,mapM_)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import System.IO
import Control.Monad.Reader (runReader)

-- Test Modules
--import Language.SMTLib2.Pipe
import "mtl" Control.Monad.Trans (liftIO)

-- | Stores a lattice of abstractions.
--   An edge from A to B signifies that A includes B
data Domain a = Domain { domainGArg :: a (RevComp a)
                       , domainDescr :: CompDescr a
                       , domainGraph :: Gr (CompositeExpr a BoolType,
                                            DMap (RevComp a) NoVar) ()
                       , domainNodesRev :: Map (CompositeExpr a BoolType) Node
                       , domainNextNode :: Node
                       , domainPool :: SMTPool (DomainInstance a)
                       , domainVerbosity :: Int
                       , domainTimeout :: Maybe Integer
                       }

data DomainInstance a b = DomainInstance { domainVars :: a (Expr b)
                                         , domainNodes :: Map Node (Expr b BoolType)
                                         , domainInstNext :: Node
                                         , domainIsFresh :: Bool
                                         }

-- | An abstract state is a partial mapping of predicates to true or false, indicating whether or not a predicate is true or false in the abstracted state.
type AbstractState a = Vector (Node,Bool)

-- | Create the initial domain containing only true and false.
initialDomain :: forall a b.
                 (Composite a,Backend b,SMTMonad b ~ IO)
              => Int -- ^ How verbose the domain should be (0 = no output)
              -> IO b -- ^ A function to create SMT backends
              -> CompDescr a -- ^ The annotation for the data type abstracted by the domain
              -> IO (Domain a)
initialDomain verb backend ann = do
  let initInst = do
        setOption (ProduceModels True)
        vars <- createComposite (\tp rev -> declareVarNamed tp
                                            (revName (Proxy::Proxy a) rev)
                                ) ann
        top <- true
        bot <- false
        return DomainInstance { domainVars = vars
                              , domainNodes = Map.fromList
                                              [(domainTop,top)
                                              ,(domainBot,bot)]
                              , domainInstNext = 2
                              , domainIsFresh = True }
      gArg = runIdentity $ createComposite (\_ rev -> return rev) ann
  supportsTimeouts <- withBackendExitCleanly backend $ do
    name <- getInfo SMTSolverName
    return $ name=="Z3"
  pool <- createSMTPool backend initInst
  return $ Domain { domainGraph = mkGraph
                                  [(domainTop,(CompositeExpr ann (ConstBool True),DMap.empty))
                                  ,(domainBot,(CompositeExpr ann (ConstBool False),DMap.empty))]
                                  [(domainTop,domainBot,())]
                  , domainGArg = gArg
                  , domainDescr = ann
                  , domainNodesRev = Map.fromList
                                     [(CompositeExpr ann (ConstBool True),domainTop)
                                     ,(CompositeExpr ann (ConstBool False),domainBot)]
                  , domainNextNode = 2
                  , domainPool = pool
                  , domainVerbosity = verb
                  , domainTimeout = if supportsTimeouts
                                    then Just 2000
                                    else Nothing
                  }

updateInstance :: (Backend b,Composite a) => Domain a -> DomainInstance a b
               -> SMT b (DomainInstance a b)
updateInstance dom inst
  = foldlM (\cinst nd -> do
               let Just (prop,_) = lab (domainGraph dom) nd
               cprop <- concretizeExpr (domainVars cinst) prop
               cprop' <- defineVar cprop
               return (cinst { domainNodes = Map.insert nd cprop (domainNodes cinst)
                             })
           ) (inst { domainInstNext = domainNextNode dom })
    [(domainInstNext inst)..(domainNextNode dom)-1]

domainTop,domainBot :: Node
domainTop = 0
domainBot = 1

quickImplication :: (Extract i e,GetType e)
                 => i -> e BoolType -> e BoolType
                 -> Maybe Bool
quickImplication i (extract i -> Just (ConstBool False)) _ = Just True
quickImplication i _ (extract i -> Just (ConstBool True)) = Just True
quickImplication i
  (extract i -> Just (ConstBool True))
  (extract i -> Just ((extract i -> Just (Var a)) :<=: (extract i -> Just (Var b))))
  = Just $ defaultEq a b
quickImplication i
  (extract i -> Just (ConstBool True))
  (extract i -> Just ((extract i -> Just (Var a)) :>=: (extract i -> Just (Var b))))
  = Just $ defaultEq a b
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :<: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :<: (extract i -> Just (Var b2))))
  = Just $ (defaultEq a1 b1) && (defaultEq a2 b2)
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :==: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :==: (extract i -> Just (Var b2))))
  = Just $ ((defaultEq a1 b1) && (defaultEq a2 b2)) ||
    ((defaultEq a1 b2) && (defaultEq a2 b1))
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :<=: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :<=: (extract i -> Just (Var b2))))
  = Just (defaultEq a1 b1 && defaultEq a2 b2)
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :<: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :<=: (extract i -> Just (Var b2))))
  = Just (defaultEq a1 b1 && defaultEq a2 b2)
quickImplication i
  (extract i -> Just ((extract i -> Just (Var _)) :<=: (extract i -> Just (Var _))))
  (extract i -> Just ((extract i -> Just (Var _)) :<: (extract i -> Just (Var _))))
  = Just False
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :>: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :>: (extract i -> Just (Var b2))))
  = Just (defaultEq a1 b1 && defaultEq a2 b2)
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :>: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :<=: (extract i -> Just (Var b2))))
  = Just (defaultEq a2 b1 && defaultEq a1 b2)
quickImplication i
  (extract i -> Just ((extract i -> Just (Var _)) :<=: (extract i -> Just (Var _))))
  (extract i -> Just ((extract i -> Just (Var _)) :>: (extract i -> Just (Var _))))
  = Just False
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :>: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :<: (extract i -> Just (Var b2))))
  = Just (defaultEq a1 b2 && defaultEq a2 b1)
quickImplication i
  (extract i -> Just ((extract i -> Just (Var a1)) :<: (extract i -> Just (Var a2))))
  (extract i -> Just ((extract i -> Just (Var b1)) :>: (extract i -> Just (Var b2))))
  = Just (defaultEq a1 b2 && defaultEq a2 b1)
quickImplication i
  (extract i -> Just (Var a))
  (extract i -> Just (Var b))
  = Just (defaultEq a b)
quickImplication _ _ _ = Nothing

checkImplication :: Backend b => Expr b BoolType -> Expr b BoolType -> SMT b Bool
checkImplication e1 e2 = stack $ do
  assert e1
  not' e2 >>= assert
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
--   Returns the node representing the new predicate, a boolean indicating if
--   the predicate was already present in the domain (True = predicate is new,
--   False = predicate was already present) and the resulting new domain.
domainAdd :: Composite a => CompositeExpr a BoolType -- ^ The predicate.
          -> Domain a -- ^ The domain to which to add the predicate
          -> IO (Node,Bool,Domain a)
domainAdd pred dom = case Map.lookup npred (domainNodesRev dom) of
  Just nd -> return (nd,False,dom)
  Nothing -> do
    Just parents <- findParents domainTop
    Just childs <- findChildren domainBot
    let intersection = Set.intersection parents childs
    case Set.toList intersection of -- Is the term redundant?
     [equiv] -> return (equiv,False,dom)
     [] -> do
       if domainVerbosity dom >= 2
         then (do
                  --termStr <- renderDomainPred pred dom
                  liftIO $ hPutStrLn stderr $ "Adding predicate "++show npred)
         else return ()
       let newNd = domainNextNode dom
           gr0 = insNode (newNd,(npred,vars)) (domainGraph dom)
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
       return (newNd,True,dom { domainGraph = gr2
                              , domainNextNode = succ newNd
                              , domainNodesRev = Map.insert npred newNd
                                (domainNodesRev dom)
                              })
  where
    vars = collectRevVars DMap.empty npred
    poseQuery :: Composite a => Domain a
              -> (forall b. Backend b
                  => DomainInstance a b
                  -> SMT b [Expr b BoolType])
              -> IO Bool
    poseQuery dom query = do
      res <- case dom of
        Domain { domainPool = pool }
          -> withSMTPool' pool $
             \inst -> do
               ninst <- updateInstance dom inst
               let ninst' = ninst { domainIsFresh = False }
               query' <- query ninst'
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
      impl <- case quickImplication () npred curTerm of
               Just r -> return r
               Nothing -> fmap not $ poseQuery dom
                          (\inst -> do
                              pred' <- concretizeExpr (domainVars inst) npred
                              term' <- concretizeExpr (domainVars inst) curTerm
                              nterm <- not' term'
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
      impl <- case quickImplication () curTerm npred of
               Just r -> return r
               Nothing -> fmap not $ poseQuery dom
                          (\inst -> do
                              term' <- concretizeExpr (domainVars inst) curTerm
                              pred' <- concretizeExpr (domainVars inst) npred
                              npred <- not' pred'
                              return [term',npred])
      if not impl
        then return Nothing
        else (do
                 childs <- mapM findChildren (pre' curCtx)
                 case catMaybes childs of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))
    npred = case runReader (simplify () pred) (domainDescr dom) of
      CompositeExpr { compositeExpr = Not x } -> x
      e -> e

-- | Create an abstract state from a concrete state.
domainAbstract :: Composite a
               => CompositeExpr a BoolType  -- ^ An expression which describes the concrete state
               -> Node -- ^ A property that must be considered
               -> Domain a -- ^ The domain to use for the abstraction
               -> IO (AbstractState a)
domainAbstract expr mustUse dom = do
  Right res <- case dom of
    Domain { domainPool = pool }
      -> withSMTPool' pool $ \inst -> do
      ninst <- updateInstance dom inst
      lst <- stack $ do
        concretizeExpr (domainVars inst) expr >>= assert
        let reprs = filter (\(nd,_) -> nd/=domainTop && nd/=domainBot) $
                    Map.toList $ domainNodes ninst
        sol <- checkSat
        when (sol/=Sat) (error $ "Concrete state "++show expr++
                         " doesn't have a valid abstraction")
        mapM (\(nd,repr) -> do
                 let Just (_,predVars) = lab (domainGraph dom) nd
                 -- Only use predicates which have only variables that appear in the expression
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
toDomainTerm :: (Embed m e,GetType e,Composite a)
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
                      npr <- not' pr
                      return npr)
               ) (Vec.toList state)
  case conj of
    [] -> true
    [x] -> return x
    xs -> and' xs

toDomainTerms :: (Embed m e,Composite a,GetType e)
              => AbstractState a -> Domain a -> a e -> m (Vector (Node,e BoolType,Bool))
toDomainTerms state dom vars
  = mapM (\(nd,act) -> do
             let Just (term,_) = lab (domainGraph dom) nd
             term' <- concretizeExpr vars term
             return (nd,term',act)
         ) state

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
