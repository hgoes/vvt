{-# LANGUAGE ExistentialQuantification,FlexibleContexts,PackageImports,GADTs #-}
module Domain where

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
import Data.List (delete,filter,intercalate)
import Data.Foldable
import Prelude hiding (foldl)
import Control.Monad (when)
import Data.Array (Array)
import qualified Data.Array as Array
import Data.Vector (Vector)
import qualified Data.Vector as Vec

-- Test Modules
import Language.SMTLib2.Pipe
import "mtl" Control.Monad.Trans (liftIO)

-- | Stores a lattice of abstractions
--   An edge from A to B signifies that A includes B
data Domain a = Domain { domainGraph :: Gr (a -> SMTExpr Bool) ()
                       , domainNextNode :: Node
                       , domainPool :: SMTPool (DomainInstance a) a
                       , domainVerbosity :: Int
                       }

data DomainInstance a = DomainInstance { domainNodes :: Map Node (SMTExpr Bool)
                                       , domainNodesRev :: Map (SMTExpr Bool) Node
                                       , domainInstNext :: Node
                                       }

--type AbstractState a = Map Node Bool
type AbstractState a = Vector (Node,Bool)

initialDomain :: SMTBackend b IO => Int -> IO b -> SMT a -> IO (Domain a)
initialDomain verb backend alloc = do
  let initInst = DomainInstance { domainNodes = Map.fromList
                                                [(domainTop,constant True)
                                                ,(domainBot,constant False)]
                                , domainNodesRev = Map.fromList
                                                   [(constant True,domainTop)
                                                   ,(constant False,domainBot)]
                                , domainInstNext = 2 }
  pool <- createSMTPool' backend initInst $ do
    setOption (ProduceModels True)
    alloc
  return $ Domain { domainGraph = mkGraph
                                  [(domainTop,(const $ constant True))
                                  ,(domainBot,(const $ constant False))]
                                  [(domainTop,domainBot,())]
                  , domainNextNode = 2
                  , domainPool = pool
                  , domainVerbosity = verb
                  }

updateInstance :: Domain a -> DomainInstance a -> a -> SMT (DomainInstance a)
updateInstance dom inst vars
  = foldlM (\cinst nd -> do
               let Just prop = lab (domainGraph dom) nd
               cprop <- defConstNamed ("pred"++show nd) (prop vars)
               return (cinst { domainNodes = Map.insert nd cprop (domainNodes cinst)
                             , domainNodesRev = Map.insert cprop nd (domainNodesRev cinst)
                             })
           ) (inst { domainInstNext = domainNextNode dom })
    [(domainInstNext inst)..(domainNextNode dom)-1]

domainTop,domainBot :: Node
domainTop = 0
domainBot = 1

collectVars :: SMTType t => SMTExpr t -> Set Integer -> Set Integer
collectVars expr vars
  = fst $ foldExpr (\cur expr'
                    -> case expr' of
                      Var i _ -> (Set.insert i cur,expr')
                      _ -> (cur,expr')
                   ) vars expr

quickImplication :: SMTExpr Bool -> SMTExpr Bool -> Maybe Bool
quickImplication (Const False ()) _ = Just True
quickImplication _ (Const True ()) = Just True
quickImplication (App (SMTOrd Lt) (Var a1 _,Var a2 _)) (App (SMTOrd Lt) (Var b1 _,Var b2 _))
  = Just $ a1==b1 && a2==b2
quickImplication (App SMTEq [Var a1 _,Var a2 _]) (App SMTEq [Var b1 _,Var b2 _])
  | a1==b1 && a2==b2 = Just True
  | a1==b2 && a2==b1 = Just True
  | otherwise = Just False
--quickImplication (App (SMTOrd Lt) _) (App SMTEq _) = Just False
--quickImplication (App SMTEq _) (App (SMTOrd Lt) _) = Just False
quickImplication (App (SMTOrd Le) (Var a1 _,Var a2 _)) (App (SMTOrd Le) (Var b1 _,Var b2 _))
  = Just $ a1==b1 && a2==b2
quickImplication (App (SMTOrd Lt) (Var a1 _,Var a2 _)) (App (SMTOrd Le) (Var b1 _,Var b2 _))
  = Just $ a1==b1 && a2==b2
quickImplication (App (SMTOrd Le) (Var _ _,Var _ _)) (App (SMTOrd Lt) (Var _ _,Var _ _))
  = Just False
quickImplication (App (SMTOrd Gt) (Var a1 _,Var a2 _)) (App (SMTOrd Gt) (Var b1 _,Var b2 _))
  = Just $ a1==b1 && a2==b2
quickImplication (App (SMTOrd Gt) (Var a1 _,Var a2 _)) (App (SMTOrd Le) (Var b1 _,Var b2 _))
  = Just $ a2==b1 && a1==b2
quickImplication (App (SMTOrd Le) (Var _ _,Var _ _)) (App (SMTOrd Gt) (Var _ _,Var _ _))
  = Just False
quickImplication (App (SMTOrd Gt) (Var a1 _,Var a2 _)) (App (SMTOrd Lt) (Var b1 _,Var b2 _))
  = Just $ a1==b2 && a2==b1
quickImplication (App (SMTOrd Lt) (Var a1 _,Var a2 _)) (App (SMTOrd Gt) (Var b1 _,Var b2 _))
  = Just $ a1==b2 && a2==b1
quickImplication _ _ = Nothing

checkImplication :: SMTExpr Bool -> SMTExpr Bool -> SMT Bool
checkImplication e1 e2 = stack $ do
  assert e1
  assert (not' e2)
  r <- checkSat
  return $ not r

domainAdd :: (a -> SMTExpr Bool) -> Domain a -> IO (Node,Domain a)
domainAdd pred dom
  = withSMTPool' (domainPool dom) $
    \inst vars -> do
      ninst <- updateInstance dom inst vars
      case Map.lookup (pred vars) (domainNodesRev ninst) of
       Just nd -> return ((nd,dom),ninst)
       Nothing -> do
         Just parents <- domainFindParents ninst vars domainTop pred
         Just childs <- domainFindChildren ninst vars domainBot pred
         let intersection = Set.intersection parents childs
         case Set.toList intersection of -- Is the term redundant?
          [equiv] -> return ((equiv,dom),ninst) -- Do we have to account for the variables in the term?
          [] -> do
            if domainVerbosity dom >= 2
              then (do
                       termStr <- renderExpr (pred vars)
                       liftIO $ putStrLn $ "Adding predicate "++termStr)
              else return ()
            let newNd = domainNextNode dom
                gr0 = insNode (newNd,pred) (domainGraph dom)
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
            return ((newNd,dom { domainGraph = gr2
                               , domainNextNode = succ newNd }),ninst)
  where
    domainFindParents inst vars cur term = do
      let Just curTerm = Map.lookup cur (domainNodes inst)
          curCtx = context (domainGraph dom) cur
          curTermF = lab' curCtx
      impl <- case quickImplication (term vars) (curTermF vars) of
               Just r -> return r
               Nothing -> checkImplication (term vars) curTerm
      if not impl
        then return Nothing
        else (do
                 parents <- mapM (\s -> domainFindParents inst vars s term
                                 ) (suc' curCtx)
                 case catMaybes parents of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))

    domainFindChildren inst vars cur term = do
      let Just curTerm = Map.lookup cur (domainNodes inst)
          curCtx = context (domainGraph dom) cur
          curTermF = lab' curCtx
      impl <- case quickImplication (curTermF vars) (term vars) of
               Just r -> return r
               Nothing -> checkImplication curTerm (term vars)
      if not impl
        then return Nothing
        else (do
                 childs <- mapM (\s -> domainFindChildren inst vars s term
                                ) (pre' curCtx)
                 case catMaybes childs of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))

domainAbstract :: (a -> SMTExpr Bool)  -- ^ An expression which describes the concrete state
                  -> Domain a
                  -> IO (AbstractState a)
domainAbstract expr dom = do
  res <- withSMTPool' (domainPool dom) $ \inst vars -> do
    ninst <- updateInstance dom inst vars
    lst <- stack $ do
      assert (expr vars)
      let reprs = filter (\(nd,_) -> nd/=domainTop && nd/=domainBot) $
                  Map.toList $ domainNodes ninst
      sol <- checkSat
      when (not sol) (error $ "Concrete state "++show (expr vars)++
                      " doesn't have a valid abstraction")
      mapM (\(nd,repr) -> do
               val <- getValue repr
               return (nd,val)
           ) reprs
    return (lst,ninst)
  return (Vec.fromList res)

toDomainTerm :: AbstractState a -> Domain a -> a -> SMTExpr Bool
toDomainTerm state dom vars
  = app and' [ if act
               then term vars
               else not' (term vars)
             | (nd,act) <- Vec.toList state,
               let Just term = lab (domainGraph dom) nd]

toDomainTerms :: AbstractState a -> Domain a -> a -> Vector (Node,SMTExpr Bool,Bool)
toDomainTerms state dom vars
  = fmap (\(nd,act) -> let Just term = lab (domainGraph dom) nd
                       in (nd,term vars,act)
         ) state

-- | Since a domain can only grow, we can hash its "version" using its size.
domainHash :: Domain a -> Int
domainHash dom = domainNextNode dom

{-
newtype Str = Str String

instance Show Str where
  show (Str x) = x

domainDump :: Domain a -> IO String
domainDump dom
  = withSMTPool (domainPool dom) $
    \vars -> do
      let nodes = labNodes (domainGraph dom)
          edges = labEdges (domainGraph dom)
      nodes' <- mapM (\(nd,term) -> do
                         str <- renderExpr (term vars)
                         return (nd,Str $ show nd++": "++str)
                     ) nodes
      let edges' = fmap (\(x,y,()) -> (x,y,Str "")) edges
          gr = mkGraph nodes' edges' :: Gr Str Str
      return $ graphviz' gr-}

renderDomainTerm :: AbstractState a -> Domain a -> IO String
renderDomainTerm st dom
  = withSMTPool (domainPool dom) $
    \vars -> do
      let exprs = [ if act
                    then term vars
                    else not' $ term vars
                  | (nd,act) <- Vec.toList st,
                    let Just term = lab (domainGraph dom) nd]
      strs <- mapM renderExpr exprs
      return $ "{"++intercalate ", " strs++"}"
