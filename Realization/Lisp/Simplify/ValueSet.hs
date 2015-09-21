{-# LANGUAGE GADTs,FlexibleContexts,RankNTypes,ScopedTypeVariables,ViewPatterns #-}
module Realization.Lisp.Simplify.ValueSet where

import Realization
import Realization.Lisp
import Realization.Lisp.Value

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe
import Language.SMTLib2.Debug

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.List
import Data.Maybe (catMaybes)
import Data.Typeable (cast,gcast)
import Data.Constraint
import Control.Monad.Trans

import Debug.Trace

data ValueSet = ValueSet { valueMask :: [(T.Text,[[Int]])]
                         , values :: [[LispUValue]]
                         , vsize :: !Int
                         }

valueSetAnalysis :: Int -> LispProgram -> IO LispProgram
valueSetAnalysis threshold prog = do
  vs <- deduceValueSet threshold prog
  let consts = getConstants vs
  return $ foldl (\prog' (name,idx,c) -> replaceConstantProg name (fmap fromIntegral idx) c prog') prog consts

replaceConstantProg :: T.Text -> [Integer] -> LispUValue -> LispProgram -> LispProgram
replaceConstantProg name idx c prog
  = prog { programNext = fmap (replaceConstant name idx c) (del $ programNext prog)
         , programProperty = fmap (replaceConstantExpr name idx c) (programProperty prog)
         , programGates = fmap (\(tp,var) -> (tp,replaceConstant name idx c var))
                          (programGates prog)
         , programAssumption = fmap (replaceConstantExpr name idx c) (programAssumption prog)
         , programInvariant = fmap (replaceConstantExpr name idx c) (programInvariant prog)
         , programState = del (programState prog)
         , programInit = del (programInit prog)
         }
  where
    del :: Map T.Text a -> Map T.Text a
    del mp = if idx==[] then Map.delete name mp else mp

replaceConstant :: T.Text -> [Integer] -> LispUValue -> LispVar -> LispVar
replaceConstant name idx c var@(NamedVar name' cat tp)
  = if cat==State && name==name'
    then (if idx==[]
          then LispConstr (liftArgs (Singleton c) tp)
          else mkStore var idx [] c)
    else var
  where
    mkStore :: LispVar -> [Integer] -> [SMTExpr Integer] -> LispUValue -> LispVar
    mkStore var idx dyn (LispUValue x)
      = LispStore var (fmap fromIntegral idx) dyn (UntypedExpr (constant x))
    mkStore var idx dyn (LispUArray arr)
      = fst $ foldl (\(var',n) el -> (mkStore var' idx (dyn++[constant n]) el,n+1)
                    ) (var,0) arr
replaceConstant name idx c (LispStore var idx' dyn expr)
  = LispStore (replaceConstant name idx c var) idx'
    (fmap (replaceConstantExpr name idx c) dyn)
    (replaceConstantExpr name idx c expr)
replaceConstant name idx c (LispConstr val)
  = LispConstr (LispValue { size = Size $ fmap
                                   (\(SizeElement e) -> SizeElement (replaceConstantExpr name idx c e)
                                   ) (sizeElements $ size val)
                          , value = fmap (\(Val e) -> Val (replaceConstantExpr name idx c e)
                                         ) (value val)
                          })
replaceConstant name idx c (LispITE cond ifT ifF)
  = LispITE (replaceConstantExpr name idx c cond)
            (replaceConstant name idx c ifT)
            (replaceConstant name idx c ifF)

replaceConstantExpr :: T.Text -> [Integer] -> LispUValue -> SMTExpr t -> SMTExpr t
replaceConstantExpr name idx c (InternalObj (cast -> Just acc) ann)
  = case acc of
     LispVarAccess (NamedVar name' State tp) idx' dyn
       | name==name' && idx==idx' -> access c dyn
       where
         access :: SMTType t => LispUValue -> [SMTExpr Integer] -> SMTExpr t
         access (LispUValue x) [] = case gcast (constant $ derefConst (undefined::SMTExpr Integer) x) of
           Just x' -> x'
         access (LispUArray xs) (i:is)
           = access' 0 xs i is
         access' :: SMTType t => Integer -> [LispUValue] -> SMTExpr Integer
                 -> [SMTExpr Integer] -> SMTExpr t
         access' _ [x] _ is = access x is
         access' n (x:xs) i is = ite (i .==. (constant n))
                                     (access x is)
                                     (access' (n+1) xs i is)
     LispVarAccess var idx' dyn -> InternalObj (LispVarAccess
                                                (replaceConstant name idx c var)
                                                idx'
                                                (fmap (replaceConstantExpr name idx c) dyn)
                                               ) ann
     LispSizeAccess var idx' -> InternalObj (LispSizeAccess
                                             (replaceConstant name idx c var)
                                             (fmap (replaceConstantExpr name idx c) idx')
                                            ) ann
     LispSizeArrAccess var idx' -> InternalObj (LispSizeArrAccess
                                                (replaceConstant name idx c var)
                                                idx') ann
     LispEq lhs rhs -> InternalObj (LispEq (replaceConstant name idx c lhs)
                                           (replaceConstant name idx c rhs)) ann
replaceConstantExpr name idx c (App fun args)
  = App fun $ snd $ foldExprsId (\_ e _ -> ((),replaceConstantExpr name idx c e)) () args
                    (extractArgAnnotation args)
replaceConstantExpr _ _ _ e = e

deduceValueSet :: Int -> LispProgram -> IO ValueSet
deduceValueSet threshold prog = do
  pipe <- createSMTPipe "z3" ["-smt2","-in"]
  let pipe' = debugBackend pipe
  withSMTBackend pipe $ initialValueSet threshold prog >>= refineValueSet threshold prog

getConstants :: ValueSet -> [(T.Text,[Int],LispUValue)]
getConstants vs = getConstants' 0 (valueMask vs)
  where
    getConstants' n [] = []
    getConstants' n ((name,idxs):rest) = let (consts,n') = getConstants'' name n idxs
                                         in consts++(getConstants' n' rest)
    getConstants'' name n [] = ([],n)
    getConstants'' name n (i:is)
      = let (consts,n') = getConstants'' name (n+1) is
        in case getConstant (fmap (!!n) (values vs)) of
             Nothing -> (consts,n')
             Just c -> ((name,i,c):consts,n')

    getConstant [] = Nothing
    getConstant [x] = Just x
    getConstant (x1:x2:xs) = if x1==x2
                             then getConstant (x2:xs)
                             else Nothing

showValueSet :: ValueSet -> String
showValueSet vs = intercalate "\n" $
                  fmap (\vals -> "["++intercalate "," (showValues (valueMask vs) vals)++"]"
                       ) (values vs)
  where
    showValues [] [] = []
    showValues ((name,idxs):rest) vals
      = let (strs,vals') = showValue name idxs vals
        in strs++showValues rest vals'
    showValue name [] vals = ([],vals)
    showValue name (idx:idxs) (val:vals)
      = let (rest,vals') = showValue name idxs vals
        in ((T.unpack name++
             (case idx of
                [] -> ""
                _ -> show idx)++"="++show val):rest,vals')

addState :: [LispUValue] -> ValueSet -> ValueSet
addState vs vals = vals { values = vs:values vals
                        , vsize = (vsize vals)+1 }

refineValueSet :: MonadIO m => Int -> LispProgram -> ValueSet -> SMT' m ValueSet
refineValueSet threshold prog vs = stack $ do
  cur <- createStateVars "" prog
  inp <- createInputVars "" prog
  (nxt,_) <- declareNextState prog cur inp Nothing (startingProgress prog)
  getValues cur nxt vs
  where
    getValues cur nxt vs = do
      nvs <- stack $ do
        assert $ app or' [ app and' (eqValueState vs cur val) | val <- values vs ]
        mapM (\val -> assert $ not' $ app and' (eqValueState vs nxt val)
             ) (values vs)
        hasMore <- checkSat
        if hasMore
          then do
            nst <- extractValueState vs nxt
            return $ Just $ enforceThreshold threshold $ addState nst vs
          else return Nothing
      case nvs of
        Just vs' -> getValues cur nxt vs'
        Nothing -> return vs
            
initialValueSet :: MonadIO m => Int -> LispProgram -> SMT' m ValueSet
initialValueSet threshold prog = stack $ do
  vars <- createStateVars "" prog
  assert $ initialState prog vars
  let vs = ValueSet { valueMask = mkMask (Map.toList (programState prog))
                    , values = []
                    , vsize = 0 }
  push
  getValues vars vs
  where
    mkMask [] = []
    mkMask ((name,(tp,_)):rest) = (name,mkMask' (typeBase tp)):mkMask rest

    mkMask' (Singleton tp) = [[]]
    mkMask' (Struct tps) = concat $ zipWith (\tp i -> fmap (i:) (mkMask' tp)) tps [0..]

    getValues vars vs = do
      hasMore <- checkSat
      if hasMore
        then (do
                 nst <- extractValueState vs vars
                 let vs' = addState nst vs
                 if vsize vs' > threshold
                   then (do
                            let vs'' = enforceThreshold threshold vs'
                            pop
                            push
                            mapM (\val -> assert $ not' $ app and' $ eqValueState vs'' vars val
                                 ) (values vs'')
                            getValues vars vs'')
                   else do
                     assert $ not' $ app and' $ eqValueState vs' vars nst
                     getValues vars vs')
        else pop >> return vs

extractValueState :: Monad m => ValueSet -> Map T.Text LispValue -> SMT' m [LispUValue]
extractValueState vs vars = do
  vals <- mapM (\(name,idxs) -> case Map.lookup name vars of
                   Just (LispValue (Size sz) val) -> mapM (\idx -> extractValue sz val idx) idxs
               ) (valueMask vs)
  return $ concat vals
  where
    extractValue sz (Singleton (Val v)) [] = extract sz v
    extractValue sz (Struct xs) (i:is) = extractValue sz (xs !! i) is
    extract :: (Indexable t (SMTExpr Integer),Monad m) => [SizeElement] -> SMTExpr t
            -> SMT' m LispUValue
    extract [] (v::SMTExpr t) = case recIndexable (undefined::t) (undefined::SMTExpr Integer) of
      Dict -> do
        res <- getValue (deref (undefined::SMTExpr Integer) v)
        return $ LispUValue res
    extract (SizeElement x:xs) arr = do
      sz <- getValue (deref (undefined::SMTExpr Integer) x)
      els <- mapM (\i -> fst $ index
                         (\narr -> (do
                                       let nxs = fmap (\(SizeElement x)
                                                       -> fst $ index (\y -> (SizeElement y,y))
                                                          x (constant i)) xs
                                       extract nxs narr,narr)
                         ) arr (constant i)
                  ) [0..sz-1]
      return $ LispUArray els

eqValueState :: ValueSet -> Map T.Text LispValue -> [LispUValue] -> [SMTExpr Bool]
eqValueState vs vars st
  = blockValues (valueMask vs) st
  where
    blockValues [] [] = []
    blockValues ((name,idxs):rest) st
      = let Just val = Map.lookup name vars
            (conds,st') = blockValues' (value val) idxs st
            conds' = blockValues rest st'
        in concat conds++conds'

    blockValues' _ [] st = ([],st)
    blockValues' val (i:is) (v:vs)
      = let cond = blockValue val i v
            (conds,nst) = blockValues' val is vs
        in (cond:conds,nst)

    blockValue (Singleton (Val v)) [] x = blockValue' v x
    blockValue (Struct xs) (i:is) x = blockValue (xs !! i) is x

    blockValue' :: Indexable t (SMTExpr Integer) => SMTExpr t -> LispUValue -> [SMTExpr Bool]
    blockValue' x (LispUValue y) = case cast y of
      Just y' -> [deref (undefined::SMTExpr Integer) x .==. constant y']
    blockValue' x (LispUArray arr)
      = concat [ fst $ index (\el' -> (blockValue' el' el,el')) x (constant (i::Integer))
               | (el,i) <- zip arr [0..] ]

enforceThreshold :: Int -> ValueSet -> ValueSet
enforceThreshold threshold vs
  = if vsize vs > threshold
    then enforceThreshold threshold (reduceValueSet vs)
    else vs

columns :: ValueSet -> Int
columns vs = columns' 0 (valueMask vs)
  where
    columns' n [] = n
    columns' n ((name,idx):rest) = columns' (n+length idx) rest

reduceValueSet :: ValueSet -> ValueSet
reduceValueSet vs = nvs
  where
    nvs =  ValueSet { valueMask = nmask
                    , values = nvalues
                    , vsize = length nvalues }
    idx = maxIdx $ countUniques vs
    nmask = removeMask idx (valueMask vs)
    nvalues = nub $ fmap (removeColumn idx) (values vs)

    removeMask :: Int -> [(T.Text,[[Int]])] -> [(T.Text,[[Int]])]
    removeMask n ((name,idx):xs) = case removeMask' n idx of
      Left nidx -> (name,nidx):xs
      Right n' -> (name,idx):removeMask n' xs

    removeMask' :: Int -> [[Int]] -> Either [[Int]] Int
    removeMask' n [] = Right n
    removeMask' 0 (x:xs) =  Left xs
    removeMask' n (x:xs) = case removeMask' (n-1) xs of
                             Left xs' -> Left (x:xs')
                             Right n' -> Right n'

    removeColumn :: Int -> [LispUValue] -> [LispUValue]
    removeColumn 0 (x:xs) = xs
    removeColumn i (x:xs) = x:removeColumn (i-1) xs

    countUniques :: ValueSet -> [Int]
    countUniques vs = [ countUniques' i vs
                      | i <- [0..columns vs-1] ]

    countUniques' :: Int -> ValueSet -> Int
    countUniques' i vs = length $ nub $ fmap (!!i) (values vs)

    maxIdx :: [Int] -> Int
    maxIdx (x:xs) = maxIdx' x 0 1 xs

    maxIdx' :: Int -> Int -> Int -> [Int] -> Int
    maxIdx' mVal mIdx _ [] = mIdx
    maxIdx' mVal mIdx idx (x:xs)
      = if x>mVal then maxIdx' x idx (idx+1) xs
                  else maxIdx' mVal mIdx (idx+1) xs
