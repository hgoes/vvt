{-# LANGUAGE GADTs,FlexibleContexts,RankNTypes,ScopedTypeVariables,ViewPatterns #-}
module Realization.Lisp.Simplify.ValueSet where

import Realization
import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Transforms
import Args

import Language.SMTLib2
import Language.SMTLib2.Pipe
import Language.SMTLib2.Internals.Embed
import qualified Language.SMTLib2.Internals.Type.Struct as Struct

import Data.List
import System.IO
import Control.Monad.Trans (liftIO)
import Control.Monad
import Data.GADT.Compare
import Data.Functor.Identity
import Data.Dependent.Sum
import qualified Data.Dependent.Map as DMap

import Debug.Trace

data ValueSet = ValueSet { valueMask :: [Header]
                         , values :: [[Entry]]
                         , vsize :: !Int
                         }

data Header = forall tp. Header (LispRev tp)

data Entry = forall tp. Entry (Value tp)

instance Eq Entry where
  (==) (Entry x) (Entry y) = defaultEq x y

valueSetAnalysis :: Int -> Int -> String -> LispProgram -> IO LispProgram
valueSetAnalysis verbosity threshold solver prog = do
  vs <- deduceValueSet verbosity threshold solver prog
  when (verbosity >= 1)
    (hPutStrLn stderr $ "Value set:\n"++showValueSet vs)
  let consts = getConstants vs
  return $ foldl' (\prog' (Header rev,Entry val)
                   -> case geq (getType rev) (getType val) of
                   Just Refl -> replaceVarWith rev (runIdentity $ constant val) prog'
                  ) prog consts

deduceValueSet :: Int -> Int -> String -> LispProgram -> IO ValueSet
deduceValueSet verbosity threshold solver prog = do
  let bin:args = words solver
  --let pipe' = debugBackend pipe
  withBackend (createPipe bin args) $ initialValueSet verbosity threshold prog
    >>= refineValueSet verbosity threshold prog

getConstants :: ValueSet -> [(Header,Entry)]
getConstants vs = concat $ zipWith getConstants' [0..] (valueMask vs)
  where
    getConstants' i h = case same [ vals!!i | vals <- values vs ] of
      Just r -> [(h,r)]
      Nothing -> []

    same :: Eq a => [a] -> Maybe a
    same [] = Nothing
    same (x:xs) = if all (==x) xs
                  then Just x
                  else Nothing

showValueSet :: ValueSet -> String
showValueSet vs = intercalate "\n" $
                  fmap (\vals -> "["++intercalate "," (zipWith showEntry (valueMask vs) vals)++"]"
                       ) (values vs)
  where
    showEntry (Header rev) (Entry val) = show rev++"="++show val

addState :: [Entry] -> ValueSet -> ValueSet
addState vs vals = vals { values = vs:values vals
                        , vsize = (vsize vals)+1 }

refineValueSet :: (Backend b,SMTMonad b ~ IO) => Int -> Int -> LispProgram -> ValueSet
               -> SMT b ValueSet
refineValueSet verbosity threshold prog vs = stack $ do
  cur <- createState prog
  inp <- createInput prog
  stateInvariant prog cur inp >>= assert
  (nxt,_) <- createNextState prog cur inp (startingProgress prog)
  res <- getValues cur nxt vs
  return res
  where
    getValues cur nxt vs = do
      if verbosity >= 2
        then liftIO $ hPutStrLn stderr $ "Current value set:\n"++showValueSet vs
        else return ()
      nvs <- stack $ do
        curEqs <- mapM (\val -> do
                           eqs <- eqValueState vs cur val
                           and' eqs
                       ) (values vs)
        or' curEqs >>= assert
        mapM (\val -> do
                 nxtEq <- eqValueState vs nxt val
                 not' (and' nxtEq) >>= assert
             ) (values vs)
        hasMore <- checkSat
        if hasMore==Sat
          then do
            nst <- extractValueState vs nxt
            return $ Just $ enforceThreshold verbosity threshold $ addState nst vs
          else return Nothing
      case nvs of
        Just vs' -> getValues cur nxt vs'
        Nothing -> return vs
            
initialValueSet :: (Backend b) => Int -> Int -> LispProgram -> SMT b ValueSet
initialValueSet verbosity threshold prog = stack $ do
  vars <- createState prog
  initialState prog vars >>= assert
  let vs = ValueSet { valueMask = mkMask (DMap.toList (programState prog))
                    , values = []
                    , vsize = 0 }
  push
  getValues vars vs
  where
    mkMask :: [DSum LispName Annotation] -> [Header]
    mkMask [] = []
    mkMask ((name@(LispName _ _ _) :=> _):rest) = mkMask' name ++ mkMask rest

    mkMask' :: LispName '(sz,tps) -> [Header]
    mkMask' name@(LispName sz tps _)
      = runIdentity $ Struct.flattenIndex (\idx _ -> return [Header (LispRev name (RevVar idx))]
                                          ) (return.concat) tps

    getValues vars vs = do
      hasMore <- checkSat
      if hasMore==Sat
        then (do
                 nst <- extractValueState vs vars
                 let vs' = addState nst vs
                 if vsize vs' > threshold
                   then (do
                            let vs'' = enforceThreshold verbosity threshold vs'
                            pop
                            push
                            mapM (\val -> do
                                     eqs <- eqValueState vs'' vars val
                                     not' (and' eqs) >>= assert
                                 ) (values vs'')
                            getValues vars vs'')
                   else do
                     eqs <- eqValueState vs' vars nst
                     not' (and' eqs) >>= assert
                     getValues vars vs')
        else pop >> return vs

extractValueState :: (Backend b) => ValueSet -> LispState (Expr b) -> SMT b [Entry]
extractValueState vs vars
  = mapM (\(Header rev) -> do
             val <- getValue (accessComposite rev vars)
             return (Entry val)
         ) (valueMask vs)

eqValueState :: (Backend b) => ValueSet -> LispState (Expr b) -> [Entry]
             -> SMT b [Expr b BoolType]
eqValueState vs vars st
  = zipWithM (\(Header h) (Entry e)
              -> let h' = accessComposite h vars
                 in case geq (getType h') (getType e) of
                 Just Refl -> do
                   ce <- constant e
                   h' .==. ce
             ) (valueMask vs) st

enforceThreshold :: Int -> Int -> ValueSet -> ValueSet
enforceThreshold verbosity threshold vs
  = if vsize vs > threshold
    then enforceThreshold verbosity threshold (reduceValueSet verbosity vs)
    else vs

reduceValueSet :: Int -> ValueSet -> ValueSet
reduceValueSet verbosity vs
  = (if verbosity >= 2
     then trace ("Delete column "++show idx)
     else id) nvs
  where
    nvs =  ValueSet { valueMask = nmask
                    , values = nvalues
                    , vsize = length nvalues }
    idx = maxIdx $ countUniques vs
    nmask = removeColumn idx (valueMask vs)
    nvalues = nub $ fmap (removeColumn idx) (values vs)

    removeColumn :: Int -> [a] -> [a]
    removeColumn 0 (x:xs) = xs
    removeColumn i (x:xs) = x:removeColumn (i-1) xs

    countUniques :: ValueSet -> [Int]
    countUniques vs = [ countUniques' i vs
                      | (i,_) <- zip [0..] (valueMask vs) ]

    countUniques' :: Int -> ValueSet -> Int
    countUniques' i vs = length $ nub $ fmap (!!i) (values vs)

    maxIdx :: [Int] -> Int
    maxIdx (x:xs) = maxIdx' x 0 1 xs

    maxIdx' :: Int -> Int -> Int -> [Int] -> Int
    maxIdx' mVal mIdx _ [] = mIdx
    maxIdx' mVal mIdx idx (x:xs)
      = if x>mVal then maxIdx' x idx (idx+1) xs
                  else maxIdx' mVal mIdx (idx+1) xs
