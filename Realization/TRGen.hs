{-# LANGUAGE TypeFamilies #-}
module Realization.TRGen where

import Realization
import RSM

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe
import qualified Data.Text as Text
import Data.AttoLisp (Lisp(Symbol),lisp,atom)
import Data.Attoparsec.ByteString (parse,choice,IResult(..))
import qualified Data.ByteString.Char8 as BS
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (sequence)
import Data.Traversable (sequence)
import Data.Typeable (cast)
import Data.List (intersperse,partition)

data TRGen = TRGen { trVars :: Map String ProxyArgValue
                   , trNondets :: Map String ProxyArgValue
                   , trTR :: [Assignment]
                   , trInit :: [Lisp]
                   , trAsserts :: [Lisp]
                   , trSuggested :: [Lisp]
                   , trUseDefines :: Bool
                   } deriving Show

data Assignment = Assignment { assignState :: Integer
                             , assignVar :: String
                             , assignCond :: Maybe Lisp
                             , assignAssertion :: Lisp
                             , assignRHS :: Lisp
                             } deriving Show
                               

readTRGen :: Bool -> String -> IO TRGen
readTRGen useDefines cfile = do
  vars <- readVarFile (cfile++".vars")
  nondets <- readVarFile (cfile++".nondet")
  tr <- readTRFile (cfile++".tr")
  init <- readPredFile (cfile++".init")
  asserts <- readPredFile (cfile++".asrts")
  suggest <- readPredFile (cfile++".trx")
  return $ TRGen { trVars = vars
                 , trNondets = nondets
                 , trTR = tr
                 , trInit = init
                 , trAsserts = asserts
                 , trSuggested = suggest
                 , trUseDefines = useDefines }

readVarFile :: String -> IO (Map String ProxyArgValue)
readVarFile file = do
  cont <- readFile file
  return $ Map.fromList [ case words ln of
                           [tp,name] -> (name,
                                         case tp of
                                          "int" -> ProxyArgValue (undefined::Integer) ()
                                          "bool" -> ProxyArgValue (undefined::Bool) ())
                        | ln <- lines cont ]

readTRFile :: String -> IO [Assignment]
readTRFile file = do
  cont <- readFile file
  return [ case breakSemi ln of
            [st,cond,var,ass,expr]
              -> Assignment { assignState = read st
                            , assignCond = case cond of
                                            "" -> Nothing
                                            _ -> Just $ getLisp cond
                            , assignVar = var
                            , assignAssertion = getLisp ass
                            , assignRHS = getLisp expr
                            }
         | ln <- lines cont ]
  where
    breakSemi xs = case break (==';') xs of
      (xs',[]) -> [xs']
      (xs',_:rest) -> xs':breakSemi rest

getLisp :: String -> Lisp
getLisp str = case parse (choice [atom,lisp]) (BS.pack str) of
  Done rest l
    | BS.null rest -> l
  Partial f -> case f BS.empty of
    Done _ l -> l

readPredFile :: String -> IO [Lisp]
readPredFile file = do
  cont <- readFile file
  return $ fmap getLisp (lines cont)

translateLisp :: (SMTValue a)
                 => SMTAnnotation a -> Map String (SMTExpr UntypedValue) -> Lisp -> SMTExpr a
translateLisp ann vars lisp
  = withUndef $
    \u -> case lispToExpr commonFunctions
               (\name -> do
                   v <- Map.lookup (Text.unpack name) vars
                   return $ entypeValue UntypedExpr v)
               emptyDataTypeInfo
               (\expr -> case cast expr of
                 Just r -> r)
               (Just $ getSort u ann) 0 lisp of
           Just r -> r
  where
    withUndef :: (a -> SMTExpr a) -> SMTExpr a
    withUndef f = f undefined

instance TransitionRelation TRGen where
  type State TRGen = Map String (SMTExpr UntypedValue)
  type Input TRGen = Map String (SMTExpr UntypedValue)
  type RevState TRGen = Map Integer String
  type PredicateExtractor TRGen = RSMState Integer String
  type RealizationProgress TRGen = ()
  createStateVars pre trgen
    = sequence $ Map.mapWithKey
      (\name tp -> varNamedAnn (pre++name) tp)
      (trVars trgen)
  createInputVars pre trgen
    = sequence $ Map.mapWithKey
      (\name tp -> varNamedAnn (pre++name) tp)
      (trNondets trgen)
  initialState trgen st = cond
    where
      cond = case conds of
        [c] -> c
        _ -> app and' conds
      conds = fmap (translateLisp () st) (trInit trgen)
  declareAssumptions _ _ _ gts = return ([],gts)
  declareAssertions trgen st inp gts = return (conds,gts)
    where
      conds = fmap (translateLisp () st) (trAsserts trgen)
  declareNextState trgen cur inp grp gts
    | trUseDefines trgen = do
        let mp = Map.union cur inp
        nxt <- buildDefines (trTR trgen) mp Map.empty
        return (nxt,gts)
    | otherwise = do
        nxt <- sequence $ Map.mapWithKey
               (\name tp -> varNamedAnn (name++"_p") tp)
               (trVars trgen)
        let nxt' = Map.mapKeys (\k -> k++"_p") nxt
            mp = Map.unions [cur,inp,nxt']
        mapM_ (\assign -> do
                  let e = ((castUntypedExprValue (cur Map.! ".s"))
                           .==. (constant $ assignState assign)) .=>.
                          (case assignCond assign of
                            Nothing -> translateLisp () mp (assignAssertion assign)
                            Just rcond -> (translateLisp () mp rcond) .=>.
                                          (translateLisp () mp (assignAssertion assign)))
                  case grp of
                   Nothing -> assert e
                   Just grp -> assertInterp e grp
              ) (trTR trgen)
        return (nxt,gts)
  stateInvariant trgen st = let (minSt,maxSt) = minMaxBy assignState (trTR trgen)
                                s = castUntypedExprValue (st Map.! ".s")
                            in (s .>=. (constant $ assignState minSt)) .&&.
                               (s .<=. (constant $ assignState maxSt))
  annotationState trgen = trVars trgen
  annotationInput trgen = trNondets trgen
  defaultPredicateExtractor _ = return emptyRSM
  extractPredicates trgen rsm full lifted = do
    let st = case Map.lookup ".s" full of
          Just (UntypedValue v) -> case cast v of
            Just r -> r
        nrsm = addRSMState st (Map.mapMaybe (\el -> do
                                                rel <- el
                                                cast rel
                                            ) lifted) rsm
    (nrsm',props) <- mineStates (createSMTPipe "z3" ["-smt2","-in"]) nrsm
    return (nrsm',[ \vals -> prop (\instr -> case cast $ vals Map.! instr of
                                    Just r -> r
                                  ) | prop <- props ])
  createRevState pre trgen = do
    vars <- createStateVars pre trgen
    return (vars,Map.fromList [ (idx,name) | (name,Var idx _) <- Map.toList vars ])
  relativizeExpr _ rev trm st
    = snd $ foldExpr (\_ expr
                      -> ((),case expr of
                              Var idx ann -> case Map.lookup idx rev of
                                Just name
                                  -> case entypeValue cast (st Map.! name) of
                                      Just r -> r
                              _ -> expr)
                     ) () trm
  renderPartialState _ st = return $ "["++concat (intersperse "," assgns)++"]"
    where
      assgns = [ var++"="++show val
               | (var,Just val) <- Map.toList st ]
  suggestedPredicates trgen
    = (fmap (\p -> (True,p))
       [ \mp -> (castUntypedExprValue (mp Map.! i1)) .>.
                (castUntypedExprValue (mp Map.! i2)::SMTExpr Integer)
       | (i1,tp1) <- Map.toList (trVars trgen)
       , i1/=".s"
       , tp1==ProxyArgValue (undefined::Integer) ()
       , (i2,tp2) <- Map.toList (trVars trgen)
       , i1/=i2
       , i2/=".s"
       , tp2==ProxyArgValue (undefined::Integer) ()])++
      [(False,\st -> translateLisp () (Map.union st defaultInps) l)
      | l <- trSuggested trgen ]
    where
      defaultInps = fmap (\tp -> case () of
                           _
                             | tp==ProxyArgValue (undefined::Integer) ()
                               -> UntypedExprValue (constant (0::Integer))
                             | tp==ProxyArgValue (undefined::Bool) ()
                               -> UntypedExprValue (constant False)
                         ) (trNondets trgen)
  startingProgress _ = ()

minMaxBy :: Ord b => (a -> b) -> [a] -> (a,a)
minMaxBy f (x:xs) = minMax' x x xs
  where
    minMax' cmin cmax [] = (cmin,cmax)
    minMax' cmin cmax (x:xs)
      | f x < f cmin = minMax' x cmax xs
      | f x > f cmax = minMax' cmin x xs
      | otherwise = minMax' cmin cmax xs

buildDefines :: Monad m => [Assignment]
                -> Map String (SMTExpr UntypedValue)
                -> Map String (SMTExpr UntypedValue)
                -> SMT' m (Map String (SMTExpr UntypedValue))
buildDefines [] _ res = return res
buildDefines (x:xs) cur res = case Map.lookup (assignVar x) cur of
  Just v -> do
    nval <- entypeValue
            (\v' -> do
                res <- defConstNamed ((assignVar x)++"_p") $
                       stateITE (extractAnnotation v') v' modify
                return $ UntypedExprValue res
            ) v
    buildDefines otherVar cur (Map.insert (assignVar x) nval res)
  where
    (sameVar,otherVar) = partition (\y -> assignVar y == assignVar x) xs
    (keep,modify) = partition (\y -> assignRHS y == Symbol (Text.pack (assignVar x)))
                    (x:sameVar)
    stateITE :: (SMTValue a) => SMTAnnotation a -> SMTExpr a -> [Assignment] -> SMTExpr a
    stateITE _ v [] = v
    stateITE ann v (y:ys) = ite cond (translateLisp ann cur (assignRHS y))
                            (stateITE ann v ys)
      where
        cond = case assignCond y of
          Nothing -> stateCond
          Just c -> stateCond .&&. (translateLisp () cur c)
        stateCond = (castUntypedExprValue $ cur Map.! ".s")
                    .==.
                    (constant $ assignState y)
