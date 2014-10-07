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
data Domain a = Domain { domainGraph :: Gr (a -> SMTExpr Bool,SMTExpr Bool) ()
                       , domainNodes :: Map (SMTExpr Bool) Node
                       , domainNextNode :: Node
                       , domainPool :: SMTPool a
                       }

--type AbstractState a = Map Node Bool
type AbstractState a = Vector (Node,Bool)

initialDomain :: SMTPool a -> Domain a
initialDomain pool
  = Domain { domainGraph = mkGraph
                           [(domainTop,(const $ constant True,constant True))
                           ,(domainBot,(const $ constant False,constant False))]
                           [(domainTop,domainBot,())]
           , domainNodes = Map.fromList [(constant True,domainTop)
                                        ,(constant False,domainBot)]
           , domainNextNode = 2
           , domainPool = pool
           }

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
domainAdd abs dom = withSMTPool (domainPool dom) $
                    \vars -> {-liftIO (putStrLn ("Adding term "++show (abs vars))) >> -} domainAdd' vars abs
  where
    domainFindParents vars cur term = do
      let curCtx = context (domainGraph dom) cur
          (curTermF,curTerm) = lab' curCtx
      impl <- case quickImplication (term vars) (curTermF vars) of
               Just r -> return r
               Nothing -> checkImplication (term vars) curTerm
      if not impl
        then return Nothing
        else (do
                 parents <- mapM (\s -> domainFindParents vars s term
                                 ) (suc' curCtx)
                 case catMaybes parents of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))

    domainFindChildren vars cur term = do
      let curCtx = context (domainGraph dom) cur
          (curTermF,curTerm) = lab' curCtx
      impl <- case quickImplication (curTermF vars) (term vars) of
               Just r -> return r
               Nothing -> checkImplication curTerm (term vars)
      if not impl
        then return Nothing
        else (do
                 childs <- mapM (\s -> domainFindChildren vars s term
                                ) (pre' curCtx)
                 case catMaybes childs of
                   [] -> return $ Just (Set.singleton cur)
                   xs -> return $ Just (Set.unions xs))

    domainAdd' vars term = {-liftIO (print $ domainNodes dom) >>-} case Map.lookup (term vars) (domainNodes dom) of
      Just nd -> {- liftIO (putStrLn "Already in.") >> -} return (nd,dom)
      Nothing -> do
        termStr <- renderExpr (term vars)
        --liftIO $ putStrLn ("Adding term "++termStr)
        -- Because we have top and bottom nodes, these must succeed
        --liftIO $ putStrLn "Finding parents..."
        Just parents <- domainFindParents vars domainTop term
        --liftIO $ putStrLn "Finding children..."
        Just childs <- domainFindChildren vars domainBot term
        --liftIO $ putStrLn "done."
        let intersection = Set.intersection parents childs
        case Set.toList intersection of -- Is the term redundant?
          [equiv] -> return (equiv,dom) -- Do we have to account for the variables in the term?
          [] -> do
            entr <- defConst (term vars)
            let newNd = domainNextNode dom
                gr0 = insNode (newNd,(term,entr)) (domainGraph dom)
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
                              , domainNodes = Map.insert (term vars) newNd (domainNodes dom)
                              , domainNextNode = succ newNd
                              })

domainAbstract :: (a -> SMTExpr Bool)  -- ^ An expression which describes the concrete state
                  -> Domain a
                  -> IO (AbstractState a)
domainAbstract expr dom = do
  res <- withSMTPool (domainPool dom) $ \vars -> stack $ do
    assert (expr vars)
    let reprs = filter (\(nd,_) -> nd/=0 && nd/=1) $ labNodes $ domainGraph dom
    sol <- checkSat
    when (not sol) $ error $ "Concrete state "++show (expr vars)++" doesn't have a valid abstraction"
    mapM (\(nd,(_,repr)) -> do
             val <- getValue repr
             return (nd,val)
         ) reprs
  return (Vec.fromList res)

toDomainTerm :: AbstractState a -> Domain a -> a -> SMTExpr Bool
toDomainTerm state dom vars
  = app and' [ if act
               then term vars
               else not' (term vars)
             | (nd,act) <- Vec.toList state,
               let Just (term,_) = lab (domainGraph dom) nd]

toDomainTerms :: AbstractState a -> Domain a -> a -> Vector (Node,SMTExpr Bool,Bool)
toDomainTerms state dom vars
  = fmap (\(nd,act) -> let Just (term,_) = lab (domainGraph dom) nd
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
                    let Just (term,_) = lab (domainGraph dom) nd]
      strs <- mapM renderExpr exprs
      return $ "{"++intercalate ", " strs++"}"
