module Realization.Lisp.Karr where

import Args
import PartialArgs
import Realization.Lisp
import Realization.Lisp.Value
import Karr

import Language.SMTLib2
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import qualified Language.SMTLib2.Internals.Backend as B

import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.AttoLisp as L
import Data.Proxy
import Data.Functor.Identity
import Data.GADT.Compare
import Control.Monad.State
import Data.Maybe
import Control.Monad.State
import Debug.Trace
import qualified Data.Vector as Vec
import qualified Data.IntMap as IMap

data KarrExtractor e = KarrExtractor { nonlinState :: LispState (LinearExpr e)
                                     , nonlinInput :: LispState (LinearExpr e)
                                     , nonlinGates :: LispState (LinearExpr e)
                                     }

type KarrPCState = DMap LispName LispUVal
type KarrLinState = Map (LispRev IntType) (Map (LispRev IntType) Integer,Integer)

karrPredicates :: Backend b => LispProgram -> SMT b [LispExpr BoolType]
karrPredicates prog = do
  (initPc,initLins,trans) <- getKarrTrans prog
  let (st_mp,tmap) = buildMp (Map.singleton initPc 1)
                     (Map.singleton 0
                      (Map.singleton 1
                       [(Vec.fromList
                         [ Vec.fromList $ Map.elems lins
                         | (lins,_) <- Map.elems initLin ],
                         Vec.fromList
                         [ c | (_,c) <- Map.elems initLin ])
                       | initLin <- initLins ]))
                     trans
      karr0 = initKarr (Map.size lins) 0
              (\from to -> case Map.lookup from tmap of
                Just tos -> case Map.lookup to tos of
                  Just trans -> trans)
              (\from -> case Map.lookup from tmap of
                Just tos -> Map.keys tos
                Nothing -> [])
      karr1 = finishKarr karr0
  trace (show [ (nd,vec,c)
              | (nd,diag) <- IMap.toList $ karrNodes karr1
              , (vec,c) <- extractPredicateVec diag ] ) $
    --trace (show karr1) $
    return [ LispExpr (App (Ord NumInt op)
                       (Arg (case [ case f of
                                    1 -> x
                                    -1 -> LispExpr (App (Arith NumInt Minus (Succ Zero)) (Arg x NoArg))
                                    _ -> LispExpr (App (Arith NumInt Mult (Succ (Succ Zero)))
                                                   (Arg
                                                    (LispExpr (Const (IntValue f)))
                                                    (Arg x NoArg)))
                                  | (LispRev name (RevVar Zero rev),idx) <- Map.toList lins
                                  , let f = vec Vec.! idx
                                  , f/=0
                                  , let x :: LispExpr IntType
                                        x = LispRef (NamedVar name State) rev (ArrGet Zero IntRepr) ] of
                             [x] -> x
                             xs -> allEqFromList xs $
                                   \n args -> LispExpr (App (Arith NumInt Plus n) args))
                        (Arg (LispExpr (Const (IntValue c))) NoArg)))
           | (nd,diag) <- IMap.toList $ karrNodes karr1
           , (vec,c) <- extractPredicateVec diag
           , op <- [Gt,Ge] ]
  where
    (_,lins) = Map.mapAccum (\n _ -> (n+1,n)) (0::Int) (getLinears prog)
    
    buildMp st_mp mp [] = (st_mp,mp)
    buildMp st_mp mp ((from,to,lins):rest)
      = let (from_st,st_mp1) = case Map.lookup from st_mp of
              Just i -> (i,st_mp)
              Nothing -> (Map.size st_mp+1,Map.insert from (Map.size st_mp+1) st_mp)
            (to_st,st_mp2) = case Map.lookup to st_mp1 of
              Just i -> (i,st_mp1)
              Nothing -> (Map.size st_mp1+1,Map.insert to (Map.size st_mp1+1) st_mp1)
            nmp = Map.insertWith (Map.unionWith (++)) from_st
                  (Map.singleton to_st [(Vec.fromList
                                         [ Vec.fromList $ Map.elems lins
                                         | (lins,_) <- Map.elems lins ],
                                         Vec.fromList
                                         [ c | (_,c) <- Map.elems lins ])])
                  mp
        in buildMp st_mp2 nmp rest

getKarrTrans :: Backend b => LispProgram
             -> SMT b (KarrPCState,[KarrLinState],
                       [(KarrPCState,KarrPCState,KarrLinState)])
getKarrTrans prog = do
  extr1 <- makeKarrExtractor prog
  (invs,extr2) <- makeInvariants prog extr1
  mapM_ assert invs
  res <- checkSat
  if res/=Sat
    then return (DMap.empty,[],[])
    else do
    (initPc,extr3) <- makeInitPCs prog extr2
    (initLin,extr4) <- makeInitLins prog extr3
    (nxtPc,extr5) <- makeNextPCs prog extr4
    (nxtLin,extr6) <- makeNextLins prog extr5
    (trans,extr7) <- runLin (traceTrans extr6 nxtPc nxtLin (Set.singleton initPc) Set.empty initPc []) extr6
    return (initPc,initLin,trans)
  where
    allLinear = getLinears prog
    traceTrans :: Backend b => KarrExtractor (Expr b)
               -> LispState (LinearExpr (Expr b))
               -> LispState (LinearExpr (Expr b))
               -> Set KarrPCState
               -> Set KarrPCState
               -> KarrPCState
               -> [(KarrPCState,KarrPCState,KarrLinState)]
               -> LinearM b [(KarrPCState,KarrPCState,KarrLinState)]
    traceTrans extr nxtPc nxtLin done queue st res = do
      trgs <- do
        lin push
        -- I have no idea...
        (_::[()]) <- mapM (\(name@(LispName _ _ _) :=> val) -> do
                              val' <- liftComp val
                              case DMap.lookup name (lispState $ nonlinState extr) of
                                Just (LispValue' var) -> do
                                  NonLinear cond <- eqComposite var val'
                                  lin (assert cond)
                          ) (DMap.toAscList st)
        trgs <- allTrgs nxtPc nxtLin []
        lin pop
        return trgs
      let nqueue = foldl (\cqueue (npc,_) -> if Set.member npc done
                                             then cqueue
                                             else Set.insert npc cqueue
                         ) queue trgs
          nres = [ (st,nst,lin) | (nst,lin) <- trgs ]++res
      case Set.minView nqueue of
        Nothing -> return nres
        Just (npc,nnqueue) -> traceTrans extr nxtPc nxtLin (Set.insert npc done) nnqueue npc nres
      return res
    allTrgs :: Backend b => LispState (LinearExpr (Expr b))
            -> LispState (LinearExpr (Expr b))
            -> [(KarrPCState,KarrLinState)]
            -> LinearM b [(KarrPCState,KarrLinState)]
    allTrgs nxtPc nxtLin res = do
      hasMore <- lin checkSat
      if hasMore==Sat
        then do
        LispConcr trgPc <- unliftComp (\(NonLinear x) -> lin (getValue x)
                                      ) nxtPc
        trgLin <- sequence $ Map.mapWithKey
                  (\rev _ -> do
                      let Linear coeff c = accessComposite rev nxtLin
                      rcoeff <- mapM (\e -> do
                                         IntValueC v <- lin (getValue e)
                                         cv <- lin $ embedConst (IntValueC v)
                                         cond <- lin [expr| (= e cv) |]
                                         return (v,cond)
                                     ) coeff
                      IntValueC rc <- lin (getValue c)
                      crc <- lin $ embedConst (IntValueC rc)
                      cond <- lin [expr| (= c crc) |]
                      return ((fmap fst rcoeff,rc),cond : Map.elems (fmap snd rcoeff))
                  ) allLinear
        rtrgPc <- liftComp (LispConcr trgPc)
        NonLinear conj1 <- eqComposite nxtPc rtrgPc
        let conj2 = concat $ Map.elems $ fmap snd trgLin
        lin ([expr| (not (and # ${conj1:conj2})) |] >>= assert)
        allTrgs nxtPc nxtLin ((trgPc,fmap fst trgLin):res)
        else return res

getLinears :: LispProgram -> Map (LispRev IntType) ()
getLinears prog
  = execState
    (do
        (_::LispState Repr) <- createComposite
                               (\rev -> case getType rev of
                                 IntRepr -> do
                                   modify (Map.insert rev ())
                                   return IntRepr
                                 tp -> return tp
                               ) (programState prog)
        return ()
    ) Map.empty
          
makeInitPCs :: Backend b => LispProgram -> KarrExtractor (Expr b)
            -> SMT b (KarrPCState,KarrExtractor (Expr b))
makeInitPCs prog extr
  = runLin
    (do
        pcVars <- mapM (\(name :=> _) -> case DMap.lookup name (programInit prog) of
                         Just (LispInit pcVal) -> do
                           pcVal' <- relativizeLinValue prog
                                     (nonlinState extr) (nonlinInput extr) pcVal
                           return (name :=> (LispValue' pcVal'))
                       ) (DMap.toAscList pcs)
        LispConcr res <- unliftComp (\(NonLinear x) -> lin (getValue x)
                                    ) (LispState (DMap.fromAscList pcVars))
        return res
    ) extr
  where
    pcs = DMap.filterWithKey (\_ (Annotation ann) -> case Map.lookup "pc" ann of
                               Just (L.Symbol "true") -> True
                               _ -> False
                             ) (programState prog)

makeNextPCs :: Backend b => LispProgram -> KarrExtractor (Expr b)
            -> SMT b (LispState (LinearExpr (Expr b)),KarrExtractor (Expr b))
makeNextPCs prog extr
  = runLin
    (do
        pcVars <- mapM (\(name :=> _) -> case DMap.lookup name (programNext prog) of
                         Just pcVar -> do
                           pcVar' <- relativizeLinVar prog
                                     (nonlinState extr) (nonlinInput extr) pcVar
                           return (name :=> (LispValue' pcVar'))
                       ) (DMap.toAscList pcs)
        return (LispState $ DMap.fromAscList pcVars)) extr
  where
    pcs = DMap.filterWithKey (\_ (Annotation ann) -> case Map.lookup "pc" ann of
                               Just (L.Symbol "true") -> True
                               _ -> False
                             ) (programState prog)

makeInitLins :: Backend b => LispProgram -> KarrExtractor (Expr b)
             -> SMT b ([KarrLinState],KarrExtractor (Expr b))
makeInitLins prog extr
  = runLin
    (do
        lst <- execStateT
               (do
                (_::LispState Repr) <- createComposite
                                       (\rev@(LispRev name idx)
                                        -> case getType rev of
                                        IntRepr -> do
                                          lst <- get
                                          case DMap.lookup name (programInit prog) of
                                             Just (LispInit val) -> do
                                               rval <- lift $ relativizeLinValue prog
                                                       (nonlinState extr)
                                                       (nonlinInput extr) val
                                               let Linear _ rval' = accessComposite idx rval
                                               IntValueC v <- lift $ lin $ getValue rval'
                                               put ((rev,Just v):lst)
                                               return IntRepr
                                             Nothing -> do
                                               put ((rev,Nothing):lst)
                                               return IntRepr
                                        tp -> return tp) (programState prog)
                return ()) []
        return $ fmap Map.fromList $ complete lst) extr
  where
    complete [] = [[]]
    complete ((rev,Just v):vs) = fmap ((rev,(Map.empty,v)):) (complete vs)
    complete ((rev,Nothing):vs) = [ (rev,(Map.empty,x)):xs
                                  | xs <- complete vs
                                  , x <- [0,1] ]

makeNextLins :: Backend b => LispProgram -> KarrExtractor (Expr b)
             -> SMT b (LispState (LinearExpr (Expr b)),
                       KarrExtractor (Expr b))
makeNextLins prog extr
  = runLin
    (do
        nxt <- mapM (\(name :=> var) -> do
                        val <- relativizeLinVar prog
                               (nonlinState extr)
                               (nonlinInput extr) var
                        return (name :=> (LispValue' val))
                    ) (DMap.toAscList (programNext prog))
        return $ LispState (DMap.fromAscList nxt)) extr

makeInvariants :: Backend b => LispProgram -> KarrExtractor (Expr b)
               -> SMT b ([Expr b BoolType],KarrExtractor (Expr b))
makeInvariants prog extr
  = runLin (mapM (\inv -> do
                     NonLinear ninv <- relativizeLinExpr prog
                                       (nonlinState extr) (nonlinInput extr) inv
                     return ninv
                 ) (programInvariant prog)) extr

makeKarrExtractor :: Backend b => LispProgram -> SMT b (KarrExtractor (Expr b))
makeKarrExtractor prog = do
  st <- createComposite declareLinear
        (programState prog)
  inp <- createComposite declareLinear
         (programInput prog)
  return KarrExtractor { nonlinState = st
                       , nonlinInput = inp
                       , nonlinGates = LispState DMap.empty }

relativizeLinValue :: Backend b
                   => LispProgram
                   -> LispState (LinearExpr (Expr b))
                   -> LispState (LinearExpr (Expr b))
                   -> LispValue tp LispExpr
                   -> LinearM b (LispValue tp (LinearExpr (Expr b)))
relativizeLinValue prog st inp
  = relativizeValue st inp
    (\name -> do
        LispState gts <- LinearM get
        case DMap.lookup name gts of
          Just (LispValue' res) -> return res
          Nothing -> case DMap.lookup name (programGates prog) of
            Just gt -> do
              res <- relativizeLinVar prog st inp (gateDefinition gt)
              LinearM $ modify (\(LispState mp)
                                -> LispState (DMap.insert name (LispValue' res) mp))
              return res)

relativizeLinVar :: Backend b
                 => LispProgram
                 -> LispState (LinearExpr (Expr b))
                 -> LispState (LinearExpr (Expr b))
                 -> LispVar LispExpr tp
                 -> LinearM b (LispValue tp (LinearExpr (Expr b)))
relativizeLinVar prog st inp
  = relativizeVar st inp
    (\name -> do
        LispState gts <- LinearM get
        case DMap.lookup name gts of
          Just (LispValue' res) -> return res
          Nothing -> case DMap.lookup name (programGates prog) of
            Just gt -> do
              res <- relativizeLinVar prog st inp (gateDefinition gt)
              LinearM $ modify (\(LispState mp)
                                -> LispState (DMap.insert name (LispValue' res) mp))
              return res)

relativizeLinExpr :: (Backend b)
                  => LispProgram
                  -> LispState (LinearExpr (Expr b))
                  -> LispState (LinearExpr (Expr b))
                  -> LispExpr tp
                  -> LinearM b (LinearExpr (Expr b) tp)
relativizeLinExpr prog st inp
  = relativize st inp
    (\name -> do
        LispState gts <- LinearM get
        case DMap.lookup name gts of
          Just (LispValue' res) -> return res
          Nothing -> case DMap.lookup name (programGates prog) of
            Just gt -> do
              res <- relativizeLinVar prog st inp (gateDefinition gt)
              LinearM $ modify (\(LispState mp)
                                -> LispState (DMap.insert name (LispValue' res) mp))
              return res)
                 
                         
data LinearExpr e tp where
  NonLinear :: e tp -> LinearExpr e tp
  Linear :: Map (LispRev IntType) (e IntType) -> e IntType -> LinearExpr e IntType

instance GetType e => GetType (LinearExpr e) where
  getType (NonLinear e) = getType e
  getType (Linear _ _) = IntRepr

declareLinear :: (Backend b) => LispRev tp -> SMT b (LinearExpr (Expr b) tp)
declareLinear rev = declare' rev (getType rev)
  where
    declare' :: (Backend b) => LispRev tp -> Repr tp -> SMT b (LinearExpr (Expr b) tp)
    declare' rev IntRepr = do
      c0 <- [expr| 0 |]
      c1 <- [expr| 1 |]
      return (Linear (Map.singleton rev c1) c0)
    declare' _ tp = fmap NonLinear (declareVar' tp)

mkLinear :: GetType e => e tp -> LinearExpr e tp
mkLinear e = case getType e of
  IntRepr -> Linear Map.empty e
  _ -> NonLinear e

newtype LinearM b r = LinearM (StateT (LispState (LinearExpr (Expr b))) (SMT b) r)
                    deriving (Functor,Applicative,Monad)

lin :: Backend b => SMT b r -> LinearM b r
lin = LinearM . lift

runLin :: Backend b => LinearM b r -> KarrExtractor (Expr b)
       -> SMT b (r,KarrExtractor (Expr b))
runLin (LinearM act) extr = do
  (res,ngts) <- runStateT act (nonlinGates extr)
  return (res,extr { nonlinGates = ngts })

instance (Backend b,e ~ Expr b) => Embed (LinearM b) (LinearExpr e) where
  type EmVar (LinearM b) (LinearExpr e) = B.Var b
  type EmQVar (LinearM b) (LinearExpr e) = B.QVar b
  type EmFun (LinearM b) (LinearExpr e) = B.Fun b
  type EmConstr (LinearM b) (LinearExpr e) = B.Constr b
  type EmField (LinearM b) (LinearExpr e) = B.Field b
  type EmFunArg (LinearM b) (LinearExpr e) = B.FunArg b
  type EmLVar (LinearM b) (LinearExpr e) = B.LVar b
  embedConst (IntValueC n) = do
    c <- lin $ embedConst (IntValueC n)
    return (Linear Map.empty c)
  embedConst n = do
    c <- lin $ embedConst n
    return (NonLinear c)
  embed (Const (IntValue n)) = do
    c <- lin (embed (Const (IntValue n)))
    return (Linear Map.empty c)
  embed (Const c) = do
    nc <- lin (embed (Const c))
    return (NonLinear nc)
  embed (App (Eq tp n) args) = case tp of
    IntRepr -> do
      c0 <- lin (embed (Const (IntValue 0)))
      let xs :: [LinearExpr e IntType]
          xs = allEqToList n args
          allVars = Map.unions $ fmap (\(Linear cs _) -> fmap (const ()) cs) xs
      conj <- sequence $ Map.elems $ Map.mapWithKey
              (\var _ -> let eqs = fmap (\(Linear cs _) -> case Map.lookup var cs of
                                          Nothing -> c0
                                          Just x -> x
                                        ) xs
                         in lin [expr| (= # ${eqs}) |]
              ) allVars
      fmap NonLinear $ lin [expr| (and # ${conj}) |]
    _ -> do
      nargs <- mapArgs (\(NonLinear x) -> return x) args
      res <- lin (embed (App (Eq tp n) nargs))
      return (NonLinear res)
  embed (App (Ord NumInt op) (Arg (Linear coeff1 c1) (Arg (Linear coeff2 c2) NoArg))) = do
    allZero1 <- mapM (\x -> lin [expr| (= x 0) |]) coeff1
    allZero2 <- mapM (\x -> lin [expr| (= x 0) |]) coeff2
    let allZero = Map.elems allZero1 ++ Map.elems allZero2
    nondet <- lin declareVar
    cond <- lin (embed (App (Ord NumInt op) (Arg c1 (Arg c2 NoArg))))
    fmap NonLinear $ lin [expr| (ite (and # ${allZero}) cond nondet) |]
  embed (App (Arith NumInt Plus n) args) = do
    let xs :: [LinearExpr e IntType]
        xs = allEqToList n args
        allVars = Map.unions $ fmap (\(Linear cs _) -> fmap (const ()) cs) xs
    ncoeffs <- sequence $ Map.mapWithKey
               (\var _ -> let sum = catMaybes $ fmap (\(Linear cs _) -> Map.lookup var cs
                                                     ) xs
                          in lin [expr| (+ # ${sum}) |]
               ) allVars
    let cs = fmap (\(Linear _ c) -> c) xs
    nc <- lin [expr| (+ # ${cs}) |]
    return $ Linear ncoeffs nc
  embed (App (Arith NumInt Minus (Succ Zero)) (Arg (Linear coeff c) NoArg)) = do
    ncoeff <- mapM (\e -> lin [expr| (- e) |]) coeff
    nc <- lin [expr| (- c) |]
    return $ Linear ncoeff nc
  embed (App (Arith NumInt Minus n) args) = do
    let x@(Linear coeff c):xs = allEqToList n args :: [LinearExpr e IntType]
        allVars = Map.unions $ fmap (\(Linear cs _) -> fmap (const ()) cs) (x:xs)
    neg_coeffs <- mapM (\(Linear cs _) -> mapM (\e -> lin [expr| (- e) |]) cs
                       ) xs
    neg_cs <- mapM (\(Linear _ c) -> lin [expr| (- c) |]) xs
    ncoeffs <- sequence $ Map.mapWithKey
               (\var _ -> let sum = catMaybes $ fmap (Map.lookup var) (coeff:neg_coeffs)
                          in lin [expr| (+ # ${sum}) |]
               ) allVars
    let cs = c:neg_cs
    nc <- lin [expr| (+ # ${cs}) |]
    return $ Linear ncoeffs nc
  embed (App (Arith NumInt Mult (Succ (Succ Zero))) (Arg (Linear coeff1 c1) (Arg (Linear coeff2 c2) NoArg)))
    | Map.null coeff1 = do
        ncoeff <- mapM (\e -> lin [expr| (* e c1) |]) coeff2
        nc <- lin [expr| (* c1 c2) |]
        return $ Linear ncoeff nc
    | Map.null coeff2 = do
        ncoeff <- mapM (\e -> lin [expr| (* e c2) |]) coeff1
        nc <- lin [expr| (* c1 c2) |]
        return $ Linear ncoeff nc
    | otherwise = do
        nondet <- lin declareVar
        c <- lin [expr| (ite nondet 1 0) |]
        return $ Linear Map.empty c
  embed (App (Abs NumInt) (Arg (Linear coeff c) NoArg))
    | Map.null coeff = do
        nc <- lin [expr| (abs c) |]
        return $ Linear Map.empty nc
    | otherwise = do
        nondet <- lin declareVar
        nc <- lin [expr| (ite nondet 1 0) |]
        return $ Linear Map.empty nc
  embed (App ToInt (Arg (NonLinear x) NoArg)) = do
    c <- lin [expr| (to_int x) |]
    return $ Linear Map.empty c
  embed (App (ITE _) (Arg (NonLinear c) (Arg (Linear coeff1 c1) (Arg (Linear coeff2 c2) NoArg)))) = do
    ncoeff <- lin $ sequence $ Map.mergeWithKey (\_ x y -> Just [expr| (ite c x y) |])
              (fmap (\v -> [expr| (ite c v 0) |]))
              (fmap (\v -> [expr| (ite c 0 v) |])) coeff1 coeff2
    nc <- lin [expr| (ite c c1 c2) |]
    return $ Linear ncoeff nc
  embed (App f args) = do
    nargs <- mapArgs (\i -> case i of
                       NonLinear i' -> return i'
                       Linear _ _ -> lin declareVar
                     ) args
    fmap mkLinear $ lin $ embed (App f nargs)
