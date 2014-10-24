{-# LANGUAGE TypeFamilies #-}
module Realization.TRGen where

import Realization
import Realization.Common
import RSM

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe
import qualified Data.Text as Text
import Data.AttoLisp (Lisp,lisp,atom)
import Data.Attoparsec.ByteString (parse,choice,IResult(..))
import qualified Data.ByteString.Char8 as BS
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (sequence)
import Data.Traversable (sequence)
import Data.Typeable (cast)
import Data.List (intersperse)

data TRGen = TRGen { trVars :: Map String ProxyArgValue
                   , trNondets :: Map String ProxyArgValue
                   , trTR :: Map Integer (Map String [(Maybe Lisp,Lisp,Lisp)])
                   , trInit :: [Lisp]
                   , trAsserts :: [Lisp]
                   , trSuggested :: [Lisp]
                   } deriving Show

readTRGen :: String -> IO TRGen
readTRGen cfile = do
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
                 , trSuggested = suggest }

readVarFile :: String -> IO (Map String ProxyArgValue)
readVarFile file = do
  cont <- readFile file
  return $ Map.fromList [ case words ln of
                           [tp,name] -> (name,
                                         case tp of
                                          "int" -> ProxyArgValue (undefined::Integer) ()
                                          "bool" -> ProxyArgValue (undefined::Bool) ())
                        | ln <- lines cont ]

readTRFile :: String -> IO (Map Integer (Map String [(Maybe Lisp,Lisp,Lisp)]))
readTRFile file = do
  cont <- readFile file
  return $ Map.fromListWith (Map.unionWith (++))
    [ case breakSemi ln of
       [st,cond,var,ass,expr] -> (read st,Map.singleton var [(case cond of
                                                               "" -> Nothing
                                                               _ -> Just $ getLisp cond,
                                                              getLisp ass,
                                                              getLisp expr)])
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

translateLisp :: (SMTValue a,SMTAnnotation a ~ ())
                 => Map String (SMTExpr UntypedValue) -> Lisp -> SMTExpr a
translateLisp vars lisp
  = withUndef $
    \u -> case lispToExpr commonFunctions
               (\name -> do
                   v <- Map.lookup (Text.unpack name) vars
                   return $ entypeValue UntypedExpr v)
               emptyDataTypeInfo
               (\expr -> case cast expr of
                 Just r -> r)
               (Just $ getSort u ()) lisp of
           Just r -> r
  where
    withUndef :: (a -> SMTExpr a) -> SMTExpr a
    withUndef f = f undefined

instance TransitionRelation TRGen where
  type State TRGen = Map String (SMTExpr UntypedValue)
  type Input TRGen = Map String (SMTExpr UntypedValue)
  type RevState TRGen = Map Integer String
  type PredicateExtractor TRGen = RSMState Integer String
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
      conds = fmap (translateLisp st) (trInit trgen)
  declareAssumptions _ _ _ gts = return ([],gts)
  declareAssertions trgen st inp gts = return (conds,gts)
    where
      conds = fmap (translateLisp st) (trAsserts trgen)
  declareNextState trgen cur inp grp gts = do
    nxt <- sequence $ Map.mapWithKey
           (\name tp -> varNamedAnn (name++"_p") tp)
           (trVars trgen)
    let nxt' = Map.mapKeys (\k -> k++"_p") nxt
        mp = Map.unions [cur,inp,nxt']
    mapM_ (\(st,nvars)
           -> mapM_ (\(var,asgns)
                     -> mapM_ (\(cond,ass,_)
                               -> let e = ((castUntypedExprValue (cur Map.! ".s"))
                                           .==. (constant st)) .=>.
                                          (case cond of
                                            Nothing -> translateLisp mp ass
                                            Just rcond -> (translateLisp mp rcond) .=>.
                                                          (translateLisp mp ass))
                                  in case grp of
                                      Nothing -> assert e
                                      Just grp -> assertInterp e grp
                              ) asgns
                    ) (Map.toList nvars)
          ) (Map.toList $ trTR trgen)
    return (nxt,gts)
  stateInvariant trgen st = let (minSt,_) = Map.findMin (trTR trgen)
                                (maxSt,_) = Map.findMax (trTR trgen)
                                s = castUntypedExprValue (st Map.! ".s")
                            in (s .>=. (constant minSt)) .&&.
                               (s .<=. (constant maxSt))
  annotationState trgen = trVars trgen
  annotationInput trgen = trNondets trgen
  defaultPredicateExtractor _ = return emptyRSM
  extractPredicates trgen rsm full lifted = do
    let st = case Map.lookup ".s" full of
          Just (UntypedValue v) -> case cast v of
            Just r -> r
        nrsm = addRSMState st (Map.mapMaybe id lifted) rsm
    mineStates (createSMTPipe "z3" ["-smt2","-in"]) nrsm
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
    = cmpPredicates (Map.delete ".s" (trVars trgen))++
      [\st -> translateLisp (Map.union st defaultInps) l
      | l <- trSuggested trgen ]
    where
      defaultInps = fmap (\tp -> case () of
                           _
                             | tp==ProxyArgValue (undefined::Integer) ()
                               -> UntypedExprValue (constant (0::Integer))
                             | tp==ProxyArgValue (undefined::Bool) ()
                               -> UntypedExprValue (constant False)
                         ) (trNondets trgen)
