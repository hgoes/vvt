{-# LANGUAGE OverloadedStrings,ViewPatterns,GADTs #-}
module Realization.LispKarr where

import Karr
import Realization.Lisp
import qualified Data.Text as T
import qualified Data.AttoLisp as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Fix
import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Pipe
import Language.SMTLib2.Debug
import Prelude hiding (sequence,mapM)
import Data.Traversable
import Control.Monad.State (runStateT,get,put,lift)
import Data.Typeable
import qualified Data.IntMap as IMap
import qualified Data.Vector as Vec

type LinearExpr = (Map T.Text (SMTExpr Integer),SMTExpr Integer)
type LinearGates = Map T.Text (Either (SMTExpr Untyped) LinearExpr)

addKarrPredicates :: LispProgram -> IO LispProgram
addKarrPredicates prog = do
  (linVars,init,trans) <- getKarrTrans prog
  let preds = getKarrPredicates linVars init trans
  return $ foldl addPredicate prog preds

getKarrPredicates :: Map T.Text Int
                  -> T.Text
                  -> [(T.Text,Maybe T.Text,Map T.Text (Map T.Text Integer,Integer))]
                  -> [SMTExpr Bool]
getKarrPredicates linVars init_st trans
  = [ (app plus [ case f of
                   1 -> x
                   -1 -> negate x
                   _ -> (constant f)*x
                | (name,idx) <- Map.toList linVars
                , let f = vec Vec.! idx
                , f/=0
                , let x = InternalObj (LispVar name State NormalAccess) ()]) `op`
      (constant c)
    | (nd,diag) <- IMap.toList $ karrNodes karr1
    , (vec,c) <- extractPredicateVec diag
    , op <- [(.>.),(.>=.)]]
  where
    (st_mp,tmap) = buildMp Map.empty Map.empty trans
    buildMp st_mp mp [] = (st_mp,mp)
    buildMp st_mp mp ((from,to,lins):rest)
      = let (from_st,st_mp1) = case Map.lookup (Just from) st_mp of
              Just i -> (i,st_mp)
              Nothing -> (Map.size st_mp,Map.insert (Just from) (Map.size st_mp) st_mp)
            (to_st,st_mp2) = case Map.lookup to st_mp1 of
              Just i -> (i,st_mp1)
              Nothing -> (Map.size st_mp1,Map.insert to (Map.size st_mp1) st_mp1)
            nmp = Map.insertWith (Map.unionWith (++)) from_st
                  (Map.singleton to_st [(Vec.fromList
                                         [ Vec.fromList $ Map.elems lins
                                         | (lins,_) <- Map.elems lins ],
                                         Vec.fromList
                                         [ c | (_,c) <- Map.elems lins ])])
                  mp
        in buildMp st_mp2 nmp rest
    karr0 = initKarr (Map.size linVars) (st_mp Map.! (Just init_st))
            (\from to -> case Map.lookup from tmap of
              Just tos -> case Map.lookup to tos of
                Just trans -> trans)
            (\from -> case Map.lookup from tmap of
              Just tos -> Map.keys tos
              Nothing -> []
            )
    karr1 = finishKarr karr0

getKarrTrans :: LispProgram -> IO (Map T.Text Int,T.Text,[(T.Text,Maybe T.Text,Map T.Text (Map T.Text Integer,Integer))])
getKarrTrans prog = do
  let pcVars = Map.mapMaybe (\(sort,ann) -> case sort of
                              Fix BoolSort -> case Map.lookup "pc" ann of
                                Just (L.Symbol "true") -> Just ()
                                _ -> Nothing
                              _ -> Nothing
                            ) (programState prog)
      linVars' = Map.mapMaybe (\(_,ann) -> case Map.lookup "linear" ann of
                                Just (L.Symbol "true") -> Just ()
                                _ -> Nothing
                              ) (programState prog)
      (numLins,linVars) = Map.mapAccum (\n _ -> (n+1,n)) 0 linVars'
      linInps = Map.mapMaybe (\(_,ann) -> case Map.lookup "linear" ann of
                               Just (L.Symbol "true") -> Just ()
                               _ -> Nothing
                             ) (programInput prog)
  pipe <- createSMTPipe "z3" ["-smt2","-in"] -- >>= namedDebugBackend "karr"
  withSMTBackend pipe $ do
    pcSt <- sequence $ Map.mapWithKey
            (\name _ -> varNamedAnn (T.unpack name) ()) pcVars
    normalSt <- sequence $ Map.mapWithKey
                (\name (tp,_) -> case withSort (programDataTypes prog) tp $
                                      \u ann -> asValueType u ann $
                                                \u' ann' -> varNamedAnn (T.unpack name)
                                                            (ProxyArgValue u' ann') of
                                  Just r -> fmap Left r)
                (Map.difference (Map.difference (programState prog) linVars) pcVars)
    linSt <- sequence $ Map.mapWithKey
             (\name num -> do
                 xs <- mapM (\i -> defConstNamed (T.unpack name++"."++show i)
                                   (constant $ if i==num
                                               then 1
                                               else 0)
                            ) linVars
                 c <- defConstNamed (T.unpack name++".c") (constant 0)
                 return (Right (xs,c))
             ) linVars
    let state = Map.unions [fmap (Left . UntypedExprValue) pcSt,normalSt,linSt]
    initSt <- stack $ do
      mapM_ (\init -> do
                (init',_) <- translateCond prog linVars state Map.empty Map.empty init
                assert init'
            ) (programInitial prog)
      checkSat
      pcs <- mapM getValue pcSt
      case [ name | (name,True) <- Map.toList pcs ] of
       [n] -> return n
    normalInp <- sequence $ Map.mapWithKey
                 (\name (tp,_) -> case withSort (programDataTypes prog) tp $
                                       \u ann -> asValueType u ann $
                                                 \u' ann' -> varNamedAnn (T.unpack name)
                                                             (ProxyArgValue u' ann') of
                                   Just r -> fmap Left r)
                 (Map.difference (programInput prog) linInps)
    linearInp <- sequence $ Map.mapWithKey (\name _ -> do
                                               b <- varNamedAnn (T.unpack name) ()
                                               return (Right (fmap (const $ constant 0) linVars,
                                                              ite b (constant 1) (constant 0)))
                                           ) linInps
    let inp = Map.union normalInp linearInp
    (invars,gt0) <- runStateT (mapM (\invar -> do
                                        gates <- get
                                        (invar',ngates) <- lift $ translateCond prog linVars state inp gates invar
                                        put ngates
                                        return invar'
                                    ) (programInvariant prog)
                              ) Map.empty
    mapM_ assert invars
    (nLinear,gt1) <- runStateT (mapM (\nxt -> do
                                         gates <- get
                                         (nxt',ngates) <- lift $ translateLinear prog linVars state inp gates (castUntypedExpr nxt)
                                         put ngates
                                         return nxt'
                                     ) (Map.intersection (programNext prog) linSt)
                               ) gt0
    (nPCs,gt2) <- runStateT (mapM (\nxt -> do
                                      gates <- get
                                      (nxt',ngates) <- lift $ translateCond prog linVars state inp gates (castUntypedExpr nxt)
                                      put ngates
                                      return nxt'
                                  ) (Map.intersection (programNext prog) pcVars)
                            ) gt1
    res <- allSat pcSt nPCs nLinear
    return (linVars,initSt,res)
  where
    allSat pcs npcs lins = do
      hasSol <- checkSat
      if hasSol
        then (do
                 vPCs <- mapM getValue pcs
                 vNPCs <- mapM getValue npcs
                 vLins <- mapM (\(lin_v,lin_c) -> do
                                   v <- mapM getValue lin_v
                                   c <- getValue lin_c
                                   return (v,c)
                               ) lins
                 let fromLoc = case [ name | (name,True) <- Map.toList vPCs ] of
                       [n] -> n
                     toLoc = case [ name | (name,True) <- Map.toList vNPCs ] of
                       [n] -> Just n
                       [] -> Nothing
                 assert $ app or' $
                   (Map.elems $ Map.intersectionWith
                    (\var val -> not' $ var .==. (constant val)) pcs vPCs)++
                   (Map.elems $ Map.intersectionWith
                    (\var val -> not' $ var .==. (constant val)) npcs vNPCs)++
                   (concat $ Map.elems $ Map.intersectionWith
                    (\(lin_v,lin_c) (v,c)
                     -> (not' $ lin_c .==. constant c):
                        (Map.elems $ Map.intersectionWith
                         (\var val -> not' $ var .==. constant val)
                         lin_v v)
                    ) lins vLins)
                 rest <- allSat pcs npcs lins
                 return ((fromLoc,toLoc,vLins):rest)
             )
        else return []

translateLinear :: Monad m
                => LispProgram
                -> Map T.Text Int
                -> Map T.Text (Either (SMTExpr UntypedValue) LinearExpr)
                -> Map T.Text (Either (SMTExpr UntypedValue) LinearExpr)
                -> LinearGates
                -> SMTExpr Integer
                -> SMT' m (LinearExpr,LinearGates)
translateLinear prog linVars state inp gates (InternalObj (cast -> Just (LispVar name cat acc)) _)
  = case cat of
     State -> case Map.lookup name state of
       Just (Right lin) -> return (lin,gates)
       Just (Left expr) -> return (toLinear linVars (castUntypedExprValue expr),gates)
     Input -> case Map.lookup name inp of
       Just (Right lin) -> return (lin,gates)
       Just (Left expr) -> return (toLinear linVars (castUntypedExprValue expr),gates)
     Gate ->  case Map.lookup name gates of
       Just (Right lin) -> return (lin,gates)
       Just (Left expr) -> return (toLinear linVars (castUntypedExpr expr),gates)
       Nothing -> case Map.lookup name (programGates prog) of
         Just (_,expr) -> do
           ((nvars,nc),ngates) <- translateLinear prog linVars state inp gates (castUntypedExpr expr)
           nlin <- sequence $ Map.mapWithKey
                   (\name expr -> defConstNamed (T.unpack name) expr
                   ) nvars
           nnc <- defConstNamed (T.unpack name++".c") nc
           return ((nlin,nnc),Map.insert name (Right (nlin,nnc)) ngates)
translateLinear prog linVars state inp gates e@(Const _ ())
  = return (toLinear linVars e,gates)
translateLinear prog linVars state inp gates (App (SMTArith Plus) [lhs,rhs]) = do
  ((lhs_v,lhs_c),gates1) <- translateLinear prog linVars state inp gates lhs
  ((rhs_v,rhs_c),gates2) <- translateLinear prog linVars state inp gates1 rhs
  return ((Map.unionWith (+) lhs_v rhs_v,lhs_c+rhs_c),gates2)
translateLinear prog linVars state inp gates (App SMTMinus (lhs,rhs)) = do
  ((lhs_v,lhs_c),gates1) <- translateLinear prog linVars state inp gates lhs
  ((rhs_v,rhs_c),gates2) <- translateLinear prog linVars state inp gates1 rhs
  return ((Map.unionWith (+) lhs_v (fmap negate rhs_v),lhs_c-rhs_c),gates2)
translateLinear prog linVars state inp gates (App SMTITE (cond,lhs,rhs)) = do
  (cond',gates1) <- translateCond prog linVars state inp gates cond
  ((lhs_v,lhs_c),gates2) <- translateLinear prog linVars state inp gates1 lhs
  ((rhs_v,rhs_c),gates3) <- translateLinear prog linVars state inp gates2 rhs
  return ((Map.intersectionWith (ite cond') lhs_v rhs_v,
           ite cond' lhs_c rhs_c),gates3)
translateLinear prog linVars state inp gates expr = error $ "Failed to translate linear expression "++show expr

translateCond :: Monad m
              => LispProgram
              -> Map T.Text Int
              -> Map T.Text (Either (SMTExpr UntypedValue) LinearExpr)
              -> Map T.Text (Either (SMTExpr UntypedValue) LinearExpr)
              -> LinearGates
              -> SMTExpr Bool
              -> SMT' m (SMTExpr Bool,LinearGates)
translateCond prog linVars state inp gates (InternalObj (cast -> Just (LispVar name cat acc)) _)
  = case cat of
     State -> case Map.lookup name state of
       Just (Left expr) -> return (castUntypedExprValue expr,gates)
     Input -> case Map.lookup name inp of
       Just (Left expr) -> return (castUntypedExprValue expr,gates)
     Gate -> case Map.lookup name gates of
       Just (Left expr) -> return (castUntypedExpr expr,gates)
       Nothing -> case Map.lookup name (programGates prog) of
         Just (_,expr) -> do
           (nexpr,ngates) <- translateCond prog linVars state inp gates (castUntypedExpr expr)
           nnexpr <- defConstNamed (T.unpack name) nexpr
           return (nnexpr,Map.insert name (Left $ UntypedExpr nexpr) ngates)
translateCond _ _ _ _ gates (Const x ()) = return (Const x (),gates)
translateCond prog linVars state inp gates (App (SMTLogic op) xs) = do
  (xs',ngates) <- runStateT (mapM (\x -> do
                                      gates <- get
                                      (nx,ngates) <- lift $ translateCond prog linVars state inp gates x
                                      put ngates
                                      return nx
                                  ) xs
                            ) gates
  return (App (SMTLogic op) xs',ngates)
translateCond prog linVars state inp gates (App SMTNot x) = do
  (nx,ngates) <- translateCond prog linVars state inp gates x
  return (App SMTNot nx,ngates)
translateCond prog linVars state inp gates (App (SMTOrd op) (lhs,rhs)) = case cast (lhs,rhs) of
  Just (lhs',rhs') -> do
    ((lhs_v,lhs_c),gates1) <- translateLinear prog linVars state inp gates lhs'
    ((rhs_v,rhs_c),gates2) <- translateLinear prog linVars state inp gates1 rhs'
    nondet <- varNamed "nondet"
    return (ite (app and' $
                 [ v .==. 0 | v <- Map.elems lhs_v ]++
                 [ v .==. 0 | v <- Map.elems rhs_v ]
                ) (App (SMTOrd op) (lhs_c,rhs_c)) nondet,gates2)
translateCond prog linVars state inp gates (App SMTEq [lhs,rhs]) = case cast (lhs,rhs) of
  Just (lhs',rhs') -> do
    ((lhs_v,lhs_c),gates1) <- translateLinear prog linVars state inp gates lhs'
    ((rhs_v,rhs_c),gates2) <- translateLinear prog linVars state inp gates1 rhs'
    nondet <- varNamed "nondet"
    return (ite (app and' $
                 [ v .==. 0 | v <- Map.elems lhs_v ]++
                 [ v .==. 0 | v <- Map.elems rhs_v ]
                ) (App SMTEq [lhs_c,rhs_c]) nondet,gates2)
translateCond _ _ _ _ _ expr = error $ "Failed to translate boolean expression "++show expr

toLinear :: Map T.Text Int -> SMTExpr Integer -> LinearExpr
toLinear linVars expr = (fmap (const $ constant 0) linVars,expr)
