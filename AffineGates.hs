{-# LANGUAGE DeriveDataTypeable,GADTs,ScopedTypeVariables #-}
module AffineGates where

import Affine
import Gates

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Data.Typeable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

import Debug.Trace

data InputVar = InputVar Integer deriving (Typeable,Show,Eq,Ord)

getAffineFromGates :: (Monad m,Args inps,Args arg,Functor m) => latchs -> ArgAnnotation inps -> (latchs -> inps -> arg)
                      -> (RealizedGates -> [SMTExpr Bool] -> arg -> SMT' m ([gate],RealizedGates))
                      -> GateMap arg -> [(a,SMTExpr Integer)]
                      -> RealizedGates
                      -> SMT' m ([([gate],[(a,AffineExpr Integer)])],RealizedGates)
getAffineFromGates latchs inp_ann (mkArg::latchs -> inps -> arg) allSat gates expr real = do
  ((_,freeMp),[inps,freeInps],_) <- foldsExprs (\(i,mp) _ ann -> do
                                                   v <- varAnn ann
                                                   return ((i+1,Map.insert i (UntypedExpr v) mp),[InternalObj (InputVar i) ann,v],undefined)
                                               ) (0,Map.empty)
                                    [(undefined,()),(undefined::inps,())] inp_ann
  trace'' freeMp freeInps inps [] real expr
  where
    mkFree freeMp = snd . foldExpr (\_ expr' -> case expr' of
                                       InternalObj obj ann -> case cast obj of
                                         Just (InputVar i) -> ((),castUntypedExpr $ freeMp Map.! i)
                                         Nothing -> ((),expr')
                                       _ -> ((),expr')
                                   ) ()

    trace'' freeMp freeInps inps cond real ((k,x):xs) = do
      (affs,nreal) <- trace' freeMp freeInps inps cond real x
      let foldRes creal ((aff,cond'):affs) = do
            (affs',nreal) <- trace'' freeMp freeInps inps cond' creal xs
            (rest,nreal') <- foldRes nreal affs
            return ((fmap (\(gates,p) -> (gates,(k,aff):p)) affs'):rest,nreal')
          foldRes creal [] = return ([],creal)
      (res,nreal') <- foldRes nreal affs
      return (concat res,nreal')
    trace'' _ freeInps _ cond real [] = do
      (gates,nreal) <- allSat real cond (mkArg latchs freeInps)
      return ([(gates,[])],nreal)
    
    trace' :: (Monad m) => Map Integer UntypedExpr -> inps -> inps -> [SMTExpr Bool] -> RealizedGates -> SMTExpr Integer
              -> SMT' m ([(AffineExpr Integer,[SMTExpr Bool])],RealizedGates)
    trace' freeMp freeInps inps cond real e@(InternalObj obj ann) = case cast obj of
      Just (InputVar i) -> do
        let ncond = (castUntypedExpr $ freeMp Map.! i) .==. (constant (0::Integer))
        zeroFeas <- stack $ do
          assert $ app and' (cond++[ncond])
          checkSat
        oneFeas <- stack $ do
          assert $ app and' (cond++[not' ncond])
          checkSat
        return ((if zeroFeas
                 then [(AffineExpr Map.empty 0 (),cond++[ncond])]
                 else [])++
                (if oneFeas
                 then [(AffineExpr Map.empty 1 (),cond++[not' ncond])]
                 else []),real)
      Nothing -> case cast obj of
        Just gt -> let gate = getGate gt gates
                   in trace' freeMp freeInps inps cond real (gateTransfer gate (mkArg latchs inps))
    trace' freeMp freeInps inps cond real (Const n ()) = do
      return ([(AffineExpr Map.empty n (),cond)],real)
    trace' freeMp freeInps inps cond real (Var i ()) = do
      return ([(AffineExpr (Map.singleton i 1) 0 (),cond)],real)
    trace' freeMp freeInps inps cond real (App SMTITE (cond',ifTrue,ifFalse)) = do
      (condExpr,nreal) <- declareGate (mkFree freeMp cond') real gates (mkArg latchs freeInps)
      tIsFeas <- stack $ do
        assert $ app and' (cond++[condExpr])
        checkSat
      fIsFeas <- stack $ do
        assert $ app and' (cond ++ [not' condExpr])
        checkSat
      (tres,real1) <- if tIsFeas
                      then trace' freeMp freeInps inps (cond ++ [condExpr]) nreal ifTrue
                      else return ([],nreal)
      (fres,real2) <- if fIsFeas
                      then trace' freeMp freeInps inps (cond ++ [not' condExpr]) real1 ifFalse
                      else return ([],real1)
      return (tres++fres,real2)
    trace' freeMp freeInps inps cond real (App SMTMinus (x,y)) = do
      (xress,real1) <- trace' freeMp freeInps inps cond real x
      let foldRes creal [] = return ([],creal)
          foldRes creal ((aff,ncond):affs) = do
            (yress,nreal1) <- trace' freeMp freeInps inps ncond creal y
            (rest,nreal2) <- foldRes nreal1 affs
            return ((fmap (\(aff',cond') -> (affineAdd aff (affineNeg aff'),cond')) yress)++rest,nreal2)
      foldRes real1 xress
    trace' freeMp freeInps inps cond real (App (SMTArith Plus) [x,y]) = do
      (xress,real1) <- trace' freeMp freeInps inps cond real x
      let foldRes creal [] = return ([],creal)
          foldRes creal ((aff,ncond):affs) = do
            (yress,nreal1) <- trace' freeMp freeInps inps ncond creal y
            (rest,nreal2) <- foldRes nreal1 affs
            return ((fmap (\(aff',cond') -> (affineAdd aff aff',cond')) yress)++rest,nreal2)
      foldRes real1 xress
    trace' freeMp freeInps inps cond real (App (SMTArith Mult) [x,y]) = do
      (xress,real1) <- trace' freeMp freeInps inps cond real x
      let foldRes creal [] = return ([],creal)
          foldRes creal ((aff,ncond):affs) = do
            (yress,nreal1) <- trace' freeMp freeInps inps ncond creal y
            (rest,nreal2) <- foldRes nreal1 affs
            return ((mapMaybe (\(aff',cond') -> do
                                  res <- affineMul aff aff'
                                  return (res,cond')) yress)++rest,nreal2)
      foldRes real1 xress
    trace' _ _ _ _ _ expr = error $ "trace' "++show expr
