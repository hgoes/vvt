{-# LANGUAGE ViewPatterns,ParallelListComp,OverloadedStrings,RankNTypes,
             ScopedTypeVariables,FlexibleContexts,ImpredicativeTypes,
             ExistentialQuantification,TypeFamilies,DeriveDataTypeable,
             GADTs #-}
module Realization.Lisp.Karr where

import PartialArgs
import Realization.Lisp
import Realization.Lisp.Value
import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Internals.Instances
import Data.Unit
import Karr

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Text as T
import Data.Typeable
import Control.Monad.State (runStateT,get,put,lift)
import Data.Fix
import Data.Foldable
import Data.Traversable
import Prelude hiding (sequence,mapM,mapM_,concat,foldl)
import qualified Data.Vector as Vec
import qualified Data.IntMap as IMap
import Debug.Trace

data KarrExtractor = KarrExtractor { allLinears :: Map (T.Text,LispRev) Int
                                   , pcVars :: Map T.Text LispValue
                                   , linVars :: Map T.Text LinearValue
                                   , input :: Map T.Text LinearValue
                                   , gates :: Map T.Text LinearValue
                                   }

type KarrPCState = Map T.Text (LispStruct LispUValue)
type KarrLinState = Map (T.Text,LispRev) (Map (T.Text,LispRev) Integer,Integer)

karrPredicates :: Monad m => LispProgram -> SMT' m [SMTExpr Bool]
karrPredicates prog = do
  (lins,initPc,initLins,trans) <- getKarrTrans' prog
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
    return [ (case [ case f of
                        1 -> x
                        -1 -> negate x
                        _ -> (constant f)*x
                     | ((name,rev),idx) <- Map.toList lins
                     , let f = vec Vec.! idx
                     , f/=0
                     , let x = InternalObj (case rev of
                                             ElementSpec idx
                                               -> LispVarAccess (NamedVar name State
                                                                 (fst $ (programState prog) Map.! name))
                                                  idx []) () ] of
               [x] -> x
               xs -> app plus xs) `op`
             (constant c)
         | (nd,diag) <- IMap.toList $ karrNodes karr1
         , (vec,c) <- extractPredicateVec diag
         , op <- [(.>.),(.>=.)] ]
  where
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

getKarrTrans' :: Monad m => LispProgram
              -> SMT' m (Map (T.Text,LispRev) Int,
                         KarrPCState,[KarrLinState],
                         [(KarrPCState,KarrPCState,KarrLinState)])
getKarrTrans' prog = do
  extr1 <- makeKarrExtractor prog
  (invars,extr2) <- makeInvariants prog extr1
  mapM_ assert invars
  checkSat
  (initPc,extr3) <- makeInitPCs prog extr2
  (initLin,extr4) <- makeInitLins prog extr3
  (nxtPc,extr5) <- makeNextPCs prog extr4
  (nxtLin,extr6) <- makeNextLins prog extr5
  trans <- traceTrans extr6 nxtPc nxtLin (Set.singleton initPc) Set.empty initPc []
  return (allLinears extr4,initPc,initLin,trans)
  where
    traceTrans extr nxtPc nxtLin done queue st res = do
      trgs <- stack $ do
        mapM_ assert (assignPCValues (pcVars extr) st)
        allTrgs nxtPc nxtLin []
      let nqueue = foldl (\cqueue (npc,_) -> if Set.member npc done
                                             then cqueue
                                             else Set.insert npc cqueue
                         ) queue trgs
          nres = [ (st,nst,lin) | (nst,lin) <- trgs ]++res
      case Set.minView nqueue of
       Nothing -> return nres
       Just (npc,nnqueue) -> traceTrans extr nxtPc nxtLin (Set.insert npc done) nnqueue npc nres
    allTrgs nxtPc nxtLin res = do
      sat <- checkSat
      if sat
        then do
        trgPc <- extractPCValues nxtPc
        trgLin <- extractLinValues nxtLin
        assert $ not' $ app and' $
          (assignPCValues nxtPc trgPc)++
          (assignLinValues nxtLin trgLin)
        allTrgs nxtPc nxtLin ((trgPc,toLinState trgLin):res)
        else return res
    
getKarrTrans :: Monad m => LispProgram
             -> SMT' m (Map (T.Text,LispRev) Int,
                        [KarrPCState],
                        [(KarrPCState,KarrPCState,KarrLinState)])
getKarrTrans prog = do
  extr1 <- makeKarrExtractor prog
  (invars,extr2) <- makeInvariants prog extr1
  mapM_ assert invars
  inits <- stack $ do
    exprs <- makeInitState prog extr2
    mapM_ assert exprs
    allStates extr2
  (nxtPc,extr3) <- makeNextPCs prog extr2
  (nxtLin,extr4) <- makeNextLins prog extr3
  trans <- allTrans extr3 nxtPc nxtLin
  return (allLinears extr4,inits,trans)
  where
    allStates extr = do
      res <- checkSat
      if res
        then do
        pc <- extractPCValues (pcVars extr)
        assert $ not' $ app and' $ assignPCValues (pcVars extr) pc
        pcs <- allStates extr
        return (pc:pcs)
        else return []
    allTrans extr nxtPc nxtLin = do
      res <- checkSat
      if res
        then do
        from <- extractPCValues (pcVars extr)
        to <- extractPCValues nxtPc
        vals <- extractLinValues nxtLin
        assert $ not' $ app and' $
          (assignPCValues (pcVars extr) from)++
          (assignPCValues nxtPc to)++
          (assignLinValues nxtLin vals)
        trans <- allTrans extr nxtPc nxtLin
        return $ (from,to,toLinState vals):trans
        else return []

toLinState :: Map T.Text (Maybe (LispStruct (Maybe (Map (T.Text,LispRev) Integer,Integer))))
           -> KarrLinState
toLinState = Map.foldlWithKey (\cur name val -> case val of
                                Nothing -> cur
                                Just val' -> toLinState' val' name [] cur
                              ) Map.empty
  where
    toLinState' (Singleton Nothing) _ _ cur = cur
    toLinState' (Singleton (Just (vec,c))) name idx cur
      = Map.insert (name,ElementSpec idx) (vec,c) cur
    toLinState' (Struct xs) name idx cur
      = foldl (\cur (i,x) -> toLinState' x name (idx++[i]) cur
              ) cur (zip [0..] xs)

makeKarrExtractor :: Monad m => LispProgram -> SMT' m KarrExtractor
makeKarrExtractor prog = do
  pcSt <- argVarsAnnNamed "pc" (fmap fst pcs)
  let makeStruct :: Monad m => Map (T.Text,LispRev) a -> T.Text -> [Integer] -> LispStruct (Either Sort ())
                 -> SMT' m (LispStruct (Either LispVal (Map (T.Text,LispRev) (SMTExpr Integer),SMTExpr Integer)))
      makeStruct mp name idx (Singleton (Left sort))
        = withIndexableSort (undefined::SMTExpr Integer) sort $
          \(_::t) -> do
            val <- argVarsAnnNamed (T.unpack name) unit
            return (Singleton (Left (Val (val::SMTExpr t))))
      makeStruct mp name idx (Singleton (Right _)) = do
        let vals = Map.mapWithKey (\(name',rev') _ -> if name==name' &&
                                                         rev'==ElementSpec idx
                                                      then constant 1
                                                      else constant 0
                                  ) mp
        return (Singleton (Right (vals,constant 0)))
      makeStruct mp name idx (Struct xs) = do
        nxs <- mapM (\(i,x) -> makeStruct mp name (idx++[i]) x
                    ) (zip [0..] xs)
        return (Struct nxs)
  normalSt <- sequence $ Map.mapWithKey
              (\name (tp,ann)
               -> case translateType tp of
                   NonLinearType tp -> do
                     res <- argVarsAnnNamed (T.unpack name) tp
                     return (NonLinearValue res)
                   LinearType mp tp -> do
                     val <- makeStruct mp name [] tp
                     return (LinearValue mp val)
              ) nonPcs
  inputSt <- mapM (\tp -> case tp of
                    NonLinearType tp -> do
                      val <- argVarsAnnNamed "input" tp
                      return (NonLinearValue val)
                    LinearType mp tp -> do
                      vals <- mapM (\def -> case def of
                                     Left srt -> withIndexableSort (undefined::SMTExpr Integer) srt $
                                                 \(_::t) -> do
                                                   v <- varNamed "input"
                                                   return (Left (Val (v::SMTExpr t)))
                                     Right _ -> do
                                       cond <- varNamed "input-sw"
                                       return (Right (fmap (const (constant 0)) mp,
                                                      ite cond (constant 1) (constant 0)))
                                   ) tp
                      return (LinearValue mp vals)
                  ) inps
  return $ KarrExtractor { allLinears = allLins
                         , pcVars = pcSt
                         , linVars = normalSt
                         , input = inputSt
                         , gates = Map.empty }
  where
    (pcs,nonPcs) = Map.partition (\(tp,ann) -> Map.member "pc" ann)
                   (programState prog)
    nonPcs' = fmap (\(tp,ann) -> translateType tp) nonPcs
    allLins :: Map (T.Text,LispRev) Int
    allLins = enumVars (\_ -> Just (Accessor (\u i -> do
                                                 (_::Integer) <- cast u
                                                 return i)))
              nonPcs
    inps = fmap (\(tp,ann) -> translateType tp) (programInput prog)
    translateType :: LispType -> LinearType
    translateType tp = if typeLevel tp == 0
                       then LinearType allLins (fmap (\sort -> case sort of
                                                       Fix IntSort -> Right ()
                                                       _ -> Left sort) (typeBase tp))
                       else NonLinearType tp  

makeInitState :: Monad m => LispProgram -> KarrExtractor -> SMT' m [SMTExpr Bool]
makeInitState prog extr
  = mapM (\(name,init) -> do
             let expr = InternalObj (LispEq (NamedVar name State
                                             (fst $ (programState prog) Map.! name))
                                     (LispConstr init)) ()
             (init',_) <- translateNonLinExpr prog extr expr
             return init'
         ) (Map.toList $ programInit prog)

makeInitPCs :: Monad m => LispProgram -> KarrExtractor
            -> SMT' m (KarrPCState,KarrExtractor)
makeInitPCs prog extr = do
  let pcs = Map.intersection (programInit prog) (pcVars extr)
  runStateT (mapM (\val -> do
                      extr <- get
                      (nval,nextr) <- lift $ translateValue prog extr val
                      put nextr
                      rval <- lift $ toNonLinValue nval
                      lift $ unliftArgs rval getValue
                  ) pcs) extr

makeInitLins :: Monad m => LispProgram -> KarrExtractor
             -> SMT' m ([KarrLinState],KarrExtractor)
makeInitLins prog extr
  = runStateT (do
                  base <- mapM (\val -> do
                                   extr <- get
                                   (nval,nextr) <- lift $ translateValue prog extr val
                                   put nextr
                                   return nval
                               ) (programInit prog)  >>=
                          lift . extractLinValues >>= return.toLinState
                  let missing = Map.difference (allLinears extr) base
                  return $ complete base (Map.toList missing)
              ) extr
  where
    complete mp [] = [mp]
    complete mp ((var,_):rest) = [ mp'
                                 | i <- [0,1]
                                 , mp' <- complete (Map.insert var
                                                    (fmap (const 0)
                                                     (allLinears extr),i) mp) rest ]

makeInvariants :: Monad m => LispProgram -> KarrExtractor -> SMT' m ([SMTExpr Bool],KarrExtractor)
makeInvariants prog extr
  = runStateT (mapM (\invar -> do
                        extr <- get
                        (invar',nextr) <- lift $ translateNonLinExpr prog extr invar
                        put nextr
                        return invar'
                    ) (programInvariant prog)) extr

makeNextPCs :: Monad m => LispProgram -> KarrExtractor -> SMT' m (Map T.Text LispValue,KarrExtractor)
makeNextPCs prog extr = do
  let pcs = Map.intersection (programNext prog) (pcVars extr)
  runStateT (mapM (\var -> do
                      extr <- get
                      (val,nextr) <- lift $ translateVar prog extr var
                      put nextr
                      lift $ toNonLinValue val
                  ) pcs) extr

makeNextLins :: Monad m => LispProgram -> KarrExtractor
             -> SMT' m (Map T.Text LinearValue,KarrExtractor)
makeNextLins prog extr
  = runStateT (mapM (\nxt -> do
                        extr <- get
                        (nval,nextr) <- lift $ translateVar prog extr nxt
                        put nextr
                        return nval
                    ) lins) extr
  where
    lins = Map.intersection (programNext prog) (linVars extr)

extractPCValues :: Monad m => Map T.Text LispValue -> SMT' m KarrPCState
extractPCValues = mapM (\v -> unliftArgs v getValue)

assignPCValues :: Map T.Text LispValue -> KarrPCState -> [SMTExpr Bool]
assignPCValues vars vals = assignPartial' vars uvals
  where
    uvals = unmaskValue vars vals

extractLinValues :: Monad m => Map T.Text LinearValue
                 -> SMT' m (Map T.Text (Maybe (LispStruct (Maybe (Map (T.Text,LispRev) Integer,Integer)))))
extractLinValues
  = mapM (\v -> case v of
                 NonLinearValue _ -> return Nothing
                 LinearValue mp val -> do
                   res <- mapM (\v -> case v of
                                 Left _ -> return Nothing
                                 Right (vec,c) -> do
                                   vec' <- mapM getValue vec
                                   c' <- getValue c
                                   return (Just (vec',c'))
                               ) val
                   return (Just res)
         )

assignLinValues :: Map T.Text LinearValue
                -> Map T.Text (Maybe (LispStruct (Maybe (Map (T.Text,LispRev) Integer,Integer))))
                -> [SMTExpr Bool]
assignLinValues vars vals
  = concat $ Map.elems $ Map.intersectionWith assignLinVal vars vals
  where
    assignLinVal :: LinearValue
                 -> Maybe (LispStruct (Maybe (Map (T.Text,LispRev) Integer,Integer)))
                 -> [SMTExpr Bool]
    assignLinVal (NonLinearValue _) Nothing = []
    assignLinVal (LinearValue mp var) (Just val)
      = concat $ linearizeStruct $ zipStruct assignLinElem var val
    assignLinElem :: Either LispVal LinearExpr -> Maybe (Map (T.Text,LispRev) Integer,Integer)
                  -> [SMTExpr Bool]
    assignLinElem (Left _) Nothing = []
    assignLinElem (Right (vec,c)) (Just (vec',c'))
      = assignPartial' vec (unmaskValue vec vec') ++
        [c .==. constant c']

{-translateInit :: Monad m => LispProgram -> KarrExtractor -> SMTExpr Bool
              -> SMT' m (Maybe (SMTExpr Bool),KarrExtractor)
translateInit prog extr (App SMTEq [InternalObj (cast -> Just (LispVarAccess (NamedVar name _ _) [] [])) _,InternalObj (cast -> Just -}

translateValue :: Monad m => LispProgram -> KarrExtractor -> LispValue
               -> SMT' m (LinearValue,KarrExtractor)
translateValue prog extr val = case size val of
  Size [] -> do
    (res,extr') <- translateLin (value val)
    return (LinearValue (allLinears extr) res,extr')
  _ -> do
    (res,extr') <- translateNonLin val
    return (NonLinearValue res,extr')
  where
    translateLin val = runStateT (mapM (\(Val e) -> do
                                           extr <- get
                                           (e',extr') <- lift $ translateExpr prog extr e
                                           put extr'
                                           return e'
                                       ) val) extr
    translateNonLin (LispValue (Size sz) val) = do
      (nsz,extr1) <- runStateT (mapM (\(SizeElement el) -> do
                                         extr <- get
                                         (nel,nextr) <- lift $ translateNonLinExpr prog extr el
                                         put nextr
                                         return (SizeElement nel)
                                     ) sz) extr
      (nval,extr2) <- runStateT (mapM (\(Val v) -> do
                                          extr <- get
                                          (nv,nextr) <- lift $ translateNonLinExpr prog extr v
                                          put nextr
                                          return (Val nv)
                                      ) val) extr1
      return (LispValue (Size nsz) nval,extr2)

translateVar :: Monad m => LispProgram -> KarrExtractor -> LispVar
             -> SMT' m (LinearValue,KarrExtractor)
translateVar prog extr (NamedVar name cat tp) = case cat of
  Input -> case Map.lookup name (input extr) of
    Just val -> return (val,extr)
  State -> case Map.lookup name (linVars extr) of
    Just val -> return (val,extr)
    Nothing -> case Map.lookup name (pcVars extr) of
      Just val -> return (NonLinearValue val,extr)
  Gate -> case Map.lookup name (gates extr) of
    Just val -> return (val,extr)
    Nothing -> case Map.lookup name (programGates prog) of
      Just (_,var) -> do
        (lin,extr') <- translateVar prog extr var
        nlin <- defineLinValue (T.unpack name) lin
        return (nlin,extr' { gates = Map.insert name nlin (gates extr') })
translateVar prog extr (LispStore var idx dyn val)
  = entype (\(val1::SMTExpr t)
            -> let ann = extractAnnotation val1
                   sort = getSort (undefined::t) ann
               in withIndexableSort (undefined::SMTExpr Integer) sort $
                  \(_::s) -> case cast val1 of
                              Just (val2::SMTExpr s) -> do
                                (val3,extr1) <- translateExpr prog extr val2
                                (lin,extr2) <- translateVar prog extr1 var
                                let (_,nlin) = accessLinearValue
                                               (\_ -> ((),case val3 of
                                                        Left (Val v) -> case cast v of
                                                          Just rv -> rv))
                                               (\_ -> ((),case val3 of
                                                        Right lin' -> lin'))
                                               idx dyn lin
                                return (nlin,extr2)) val
translateVar prog extr (LispConstr val) = translateValue prog extr val
translateVar prog extr (LispITE cond ifT ifF) = do
  (ncond,extr1) <- translateNonLinExpr prog extr cond
  (valT,extr2) <- translateVar prog extr1 ifT
  (valF,extr3) <- translateVar prog extr2 ifF
  return (argITE ncond valT valF,extr3)

translateAccess :: Monad m => LispProgram -> KarrExtractor -> LispVarAccess
              -> SMT' m (Either LispVal LinearExpr,KarrExtractor)
translateAccess prog extr (LispVarAccess var idx dyn) = do
  (val,extr1) <- translateVar prog extr var
  let (res,_) = accessLinearValue (\e -> (Left (Val e),e))
                (\lin -> (Right lin,lin)) idx dyn val
  return (res,extr1)
translateAccess prog extr (LispSizeAccess var dyn) = do
  (NonLinearValue val,extr1) <- translateVar prog extr var
  let (res,_) = accessSize (\sz -> (Val sz,sz)) dyn val
  return (Left res,extr1)
translateAccess prog extr (LispSizeArrAccess var idx) = do
  (NonLinearValue val,extr1) <- translateVar prog extr var
  let (res,_) = accessSizeArr (\e -> (Val e,e)) idx val
  return (Left res,extr1)
translateAccess prog extr (LispEq v1 v2) = do
  (val1,extr1) <- translateVar prog extr v1
  (val2,extr2) <- translateVar prog extr1 v2
  val1' <- toNonLinValue val1
  val2' <- toNonLinValue val2
  return (Left (Val $ valueEq val1' val2'),extr2)

translateLinExpr :: Monad m => LispProgram -> KarrExtractor -> SMTExpr Integer
                 -> SMT' m (LinearExpr,KarrExtractor)
translateLinExpr prog extr (InternalObj (cast -> Just acc) _) = do
  (res,extr1) <- translateAccess prog extr acc
  case res of
   Left (Val v) -> case cast v of
     Just v' -> return ((fmap (const $ constant 0) (allLinears extr1),v'),extr1)
   Right lin -> return (lin,extr1)
translateLinExpr prog extr (Const i ())
  = return ((fmap (const $ constant 0) (allLinears extr),constant i),extr)
translateLinExpr prog extr (App SMTMinus (lhs,rhs)) = do
  ((vecL,cL),extr1) <- translateLinExpr prog extr lhs
  ((vecR,cR),extr2) <- translateLinExpr prog extr rhs
  return ((Map.unionWith (-) vecL vecR,cL-cR),extr2)
translateLinExpr prog extr (App (SMTArith Plus) vals) = do
  (lins,extr1) <- translateLinExprs prog extr vals
  return ((Map.unionsWith (+) (fmap fst lins),app plus (fmap snd lins)),extr1)
translateLinExpr prog extr (App (SMTArith Mult) [lhs,rhs]) = case lhs of
  Const l _ -> do
    ((vecR,cR),extr1) <- translateLinExpr prog extr rhs
    return ((fmap (*(constant l)) vecR,cR*(constant l)),extr1)
  _ -> case rhs of
    Const r _ -> do
      ((vecL,cL),extr1) <- translateLinExpr prog extr lhs
      return ((fmap (*(constant r)) vecL,cL*(constant r)),extr1)
    _ -> do
      nondet <- varNamed "nondet"
      return ((fmap (const $ constant 0) (allLinears extr),ite nondet 1 0),extr)
translateLinExpr prog extr (App SMTITE (cond,lhs,rhs)) = do
  (ncond,extr1) <- translateNonLinExpr prog extr cond
  (nlhs,extr2) <- translateLinExpr prog extr1 lhs
  (nrhs,extr3) <- translateLinExpr prog extr2 rhs
  return (argITE ncond nlhs nrhs,extr3)
translateLinExpr prog extr expr = error $ "Cannot translate linear expression "++show expr
  
translateLinExprs :: Monad m => LispProgram -> KarrExtractor -> [SMTExpr Integer]
                  -> SMT' m ([LinearExpr],KarrExtractor)
translateLinExprs _ extr [] = return ([],extr)
translateLinExprs prog extr (x:xs) = do
  (nx,extr1) <- translateLinExpr prog extr x
  (nxs,extr2) <- translateLinExprs prog extr1 xs
  return (nx:nxs,extr2)

translateExpr :: (Monad m,Indexable t (SMTExpr Integer))
              => LispProgram -> KarrExtractor -> SMTExpr t
              -> SMT' m (Either LispVal LinearExpr,KarrExtractor)
translateExpr prog extr expr = case cast expr of
  Just lin -> do
    (res,extr') <- translateLinExpr prog extr lin
    return (Right res,extr')
  Nothing -> do
    (res,extr') <- translateNonLinExpr prog extr expr
    return (Left (Val res),extr')

translateNonLinExpr :: Monad m => LispProgram -> KarrExtractor -> SMTExpr t
                    -> SMT' m (SMTExpr t,KarrExtractor)
translateNonLinExpr prog extr (Const x ann) = return (Const x ann,extr)
translateNonLinExpr prog extr (InternalObj (cast -> Just acc) _) = do
  (Left (Val e),extr') <- translateAccess prog extr acc
  case cast e of
   Just e' -> return (e',extr')
translateNonLinExpr prog extr (App (SMTOrd op) (cast -> Just (lhs,rhs))) = do
  ((vecL,cL),extr1) <- translateLinExpr prog extr lhs
  ((vecR,cR),extr2) <- translateLinExpr prog extr1 rhs
  nondet <- varNamed "nondet"
  return (ite (app and' $
               [ v .==. 0 | v <- Map.elems vecL ]++
               [ v .==. 0 | v <- Map.elems vecR ]) (App (SMTOrd op) (cL,cR))
          nondet,extr2)
translateNonLinExpr prog extr (App SMTEq (cast -> Just [lhs,rhs])) = do
  ((vecL,cL),extr1) <- translateLinExpr prog extr lhs
  ((vecR,cR),extr2) <- translateLinExpr prog extr1 rhs
  nondet <- varNamed "nondet"
  return (ite (app and' $
               [ v .==. 0 | v <- Map.elems vecL ]++
               [ v .==. 0 | v <- Map.elems vecR ]) (App SMTEq [cL,cR])
          nondet,extr2)
translateNonLinExpr prog extr (App fun args) = do
  (extr',args') <- foldExprs (\extr expr _ -> do
                                 (nexpr,nextr) <- translateNonLinExpr prog extr expr
                                 return (nextr,nexpr)
                             ) extr args (extractArgAnnotation args)
  case fun of
   SMTBuiltIn "exactly-one" _ -> case cast args' of
     Just args'' -> case cast (oneOf args'') of
       Just r -> return (r,extr')
   _ -> return (App fun args',extr')
translateNonLinExpr _ _ expr = error $ "Cannot translate non-linear expression "++show expr

toNonLinValue :: Monad m => LinearValue -> SMT' m LispValue
toNonLinValue (NonLinearValue v) = return v
toNonLinValue (LinearValue _ val) = do
  nval <- mapM toNonLin val
  return $ LispValue (Size []) nval
  where
    toNonLin (Left val) = return val
    toNonLin (Right (vec,c)) = do
      nondet <- varNamed "nondet"
      return (Val (ite (app and' [ v .==. 0 | v <- Map.elems vec ])
                   c nondet))

                    
accessLinearValue :: (forall t. Indexable t (SMTExpr Integer) => SMTExpr t -> (a,SMTExpr t))
                  -> (LinearExpr -> (a,LinearExpr))
                  -> [Integer] -> [SMTExpr Integer]
                  -> LinearValue -> (a,LinearValue)
accessLinearValue f g idx dyn (NonLinearValue val) = (res,NonLinearValue nval)
  where
    (res,nval) = accessValue f idx dyn val
accessLinearValue f g idx [] (LinearValue mp val) = (res,LinearValue mp nval)
  where
    (res,nval) = accessStruct (\v -> case v of
                                Left (Val x) -> let (res,nx) = f x
                                                in (res,Left (Val nx))
                                Right lin -> let (res,nlin) = g lin
                                             in (res,Right nlin)
                              ) idx val

data Accessor a = Accessor (forall t. (SMTType t,Unit (SMTAnnotation t)) => t -> Int -> Maybe a)

enumVars :: (Annotation -> Maybe (Accessor a))
         -> Map T.Text (LispType,Annotation) -> Map (T.Text,LispRev) a
enumVars f mp
  = snd $ Map.foldlWithKey (\(n,mp) name (tp,ann)
                            -> case f ann of
                                Nothing -> (n,mp)
                                Just (Accessor g)
                                  -> foldTypeWithIndex
                                     (\(n,mp) idx t
                                      -> case g t n of
                                          Nothing -> (n,mp)
                                          Just x -> (n+1,Map.insert (name,idx) x mp)
                                     ) (n,mp) tp
                           ) (0,Map.empty) mp

defineLinValue :: Monad m => String -> LinearValue -> SMT' m LinearValue
defineLinValue name (NonLinearValue val) = do
  nval <- defineValue name val
  return (NonLinearValue nval)
defineLinValue name (LinearValue mp val) = do
  nval <- mapM (\val -> case val of
                 Left (Val e) -> do
                   ne <- defConstNamed name e
                   return (Left (Val ne))
                 Right (vec,c) -> do
                   nvec <- mapM (defConstNamed name) vec
                   nc <- defConstNamed name c
                   return (Right (nvec,nc))
               ) val
  return (LinearValue mp nval)

type LinearExpr = (Map (T.Text,LispRev) (SMTExpr Integer),SMTExpr Integer)

data LinearValue = NonLinearValue LispValue
                 | LinearValue (Map (T.Text,LispRev) Int) (LispStruct (Either LispVal LinearExpr))
                 deriving (Typeable,Eq,Ord,Show)

data LinearType = NonLinearType LispType
                | LinearType (Map (T.Text,LispRev) Int) (LispStruct (Either Sort ()))
                deriving (Typeable,Eq,Ord,Show)

instance Args LinearValue where
  type ArgAnnotation LinearValue = LinearType
  foldExprs f s ~(NonLinearValue val) (NonLinearType tp) = do
    (s1,nval) <- foldExprs f s val tp
    return (s1,NonLinearValue nval)
  foldExprs f s ~(LinearValue _ val) (LinearType mp tp) = do
    (s1,nval) <- foldStruct g s val tp
    return (s1,LinearValue mp nval)
    where
      g s ~(Left val) (Left tp) = do
        (s1,nval) <- foldLispVal 0 f s val tp
        return (s1,Left nval)
      g s ~(Right (vec,c)) (Right n) = do
        (s1,nvec) <- foldExprs f s vec (fmap (const ()) mp)
        (s2,nc) <- foldExprs f s1 c ()
        return (s2,Right (nvec,nc))
  foldsExprs f s lst (NonLinearType tp) = do
    (s1,nlst,res) <- foldsExprs f s (fmap (\(NonLinearValue v,b) -> (v,b)) lst) tp
    return (s1,fmap NonLinearValue nlst,NonLinearValue res)
  foldsExprs f s lst (LinearType mp tp) = do
    (s1,nlst,res) <- foldsStruct g s (fmap (\(LinearValue _ v,b) -> (v,b)) lst) tp
    return (s1,fmap (LinearValue mp) nlst,LinearValue mp res)
    where
      g s lst (Left tp) = do
        (s1,nlst,res) <- foldsLispVal 0 f s (fmap (\(Left v,b) -> (v,b)) lst) tp
        return (s1,fmap Left nlst,Left res)
      g s lst (Right n) = do
        (s1,nvecs,nvec) <- foldsExprs f s (fmap (\(Right (vec,c),b) -> (vec,b)) lst)
                           (fmap (const ()) mp)
        (s2,ncs,nc) <- foldsExprs f s1 (fmap (\(Right (vec,c),b) -> (c,b)) lst) ()
        return (s2,zipWith (\v c -> Right (v,c)) nvecs ncs,Right (nvec,nc))
  extractArgAnnotation (NonLinearValue val) = NonLinearType (extractArgAnnotation val)
  extractArgAnnotation (LinearValue mp val) = LinearType mp (fmap extract val)
    where
      extract (Left (Val (e::SMTExpr t))) = Left $ getSort (undefined::t) unit
      extract (Right _) = Right ()
  toArgs (NonLinearType tp) xs = do
    (res,xs1) <- toArgs tp xs
    return (NonLinearValue res,xs1)
  toArgs (LinearType mp tp) xs = do
    (res,xs1) <- toArgsStruct f tp xs
    return (LinearValue mp res,xs1)
    where
      f (Left sort) xs = do
        (val,xs1) <- toArgsLispVal 0 sort xs
        return (Left val,xs1)
      f (Right _) xs = do
        (lins,xs1) <- toArgs (fmap (const ()) mp) xs
        (c,xs2) <- toArgs () xs1
        return (Right (lins,c),xs2)
  getTypes _ (NonLinearType tp) = getTypes (undefined::LispValue) tp
  getTypes _ (LinearType mp tp) = getTypesStruct f tp
    where
      f (Left sort) = getTypesLispVal 0 sort
      f (Right _) = getTypes (undefined::LinearExpr) (fmap (const ()) mp,())

toLinear :: Map (T.Text,LispRev) Int -> SMTExpr Integer -> LinearExpr
toLinear linVars expr = (fmap (const $ constant 0) linVars,expr)
