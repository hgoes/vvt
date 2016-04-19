{-# LANGUAGE PackageImports,FlexibleContexts, DeriveGeneric #-}
module RSM where

import Args

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Language.SMTLib2
import "mtl" Control.Monad.State (runStateT,modify)
import "mtl" Control.Monad.Trans (lift)
import Prelude hiding (mapM,sequence)
import Data.Traversable (mapM,sequence)
import Data.GADT.Show
import Data.GADT.Compare
import qualified Data.Text as T

import GHC.Generics as G
import Data.Aeson as A

newtype CollectedStates =
    CollectedStates
    { unpackCollectedStates :: Map T.Text [[Either Bool Integer]] }
    deriving G.Generic

instance A.ToJSON CollectedStates

data RSMState loc var = RSMState { rsmLocations :: Map loc (RSMLoc var)
                                 , rsmStates :: CollectedStates
                                 }

data RSMLoc var = RSMLoc { rsmClasses :: Map (Set var) (Set (Map var Integer))
                         }

data Coeffs b var = Coeffs { coeffsVar :: Map var (Expr b IntType)
                           , coeffsConst :: Expr b IntType
                           }

emptyRSM :: RSMState loc var
emptyRSM = RSMState Map.empty (CollectedStates Map.empty)

addRSMState :: (Ord loc,Ord var) => loc -> Map var Integer -> (Set T.Text, [Either Bool Integer])
               -> RSMState loc var -> RSMState loc var
addRSMState loc instrs (pc, concr_state) st
  = st { rsmLocations = Map.insertWith
                        joinLoc
                        loc
                        (RSMLoc { rsmClasses = Map.singleton (Map.keysSet instrs) (Set.singleton instrs)})
                        (rsmLocations st)
       , rsmStates = CollectedStates $
                     Map.insertWithKey
                     (\_ new_val old_val -> ((head new_val) : old_val))
                     (head (Set.toList pc))
                     [concr_state]
                     (unpackCollectedStates $ rsmStates st)
       }
  where
    joinLoc :: Ord var => RSMLoc var -> RSMLoc var -> RSMLoc var
    joinLoc l1 l2 = RSMLoc { rsmClasses = Map.unionWith Set.union (rsmClasses l1) (rsmClasses l2)
                           }

createCoeffs :: (Backend b,Ord var) => Set var -> SMT b (Coeffs b var)
createCoeffs instrs = do
  coeffs <- mapM (\instr -> do
                     c <- declareVar int
                     return (instr,c)
                 ) (Set.toAscList instrs)
  c <- declareVar int
  return $ Coeffs { coeffsVar = Map.fromAscList coeffs
                  , coeffsConst = c
                  }

notAllZero :: Backend b => Coeffs b var -> SMT b (Expr b BoolType)
notAllZero coeffs = or' [ not' (c .==. cint 0)
                        | c <- Map.elems (coeffsVar coeffs) ]

createLine :: (Backend b,Ord var) => Coeffs b var -> Map var Integer -> SMT b (Expr b BoolType)
createLine coeffs vars = do
  lhs <- case Map.elems $ Map.intersectionWith (\c i -> c .*. cint i
                                               ) (coeffsVar coeffs) vars of
         [x] -> x
         xs -> plus xs
  let rhs = coeffsConst coeffs
  lhs .==. rhs

createLines :: (Backend b,Ord var) => Coeffs b var -> Set (Map var Integer)
               -> SMT b (Map (ClauseId b) (Map var Integer))
createLines coeffs points = do
  res <- mapM (\point -> do
                  cid <- createLine coeffs point >>= assertId
                  return (cid,point)
              ) (Set.toList points)
  return $ Map.fromList res

newtype RSMVars var e = RSMVars (Map var (e IntType))

data RSMVar :: * -> Type -> * where
  RSMVar :: var -> RSMVar var IntType

deriving instance Show var => Show (RSMVar var tp)

instance Show var => GShow (RSMVar var) where
  gshowsPrec = showsPrec

instance Eq var => GEq (RSMVar var) where
  geq (RSMVar v1) (RSMVar v2) = if v1==v2
                                then Just Refl
                                else Nothing

instance Ord var => GCompare (RSMVar var) where
  gcompare (RSMVar v1) (RSMVar v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT

instance (Show var,Ord var) => Composite (RSMVars var) where
  type CompDescr (RSMVars var) = Map var ()
  type RevComp (RSMVars var) = RSMVar var
  compositeType mp = RSMVars (fmap (const IntRepr) mp)
  foldExprs f (RSMVars mp) = do
    mp' <- sequence $ Map.mapWithKey
           (\var -> f (RSMVar var)) mp
    return (RSMVars mp')
  createComposite f mp = do
    mp' <- sequence $ Map.mapWithKey (\instr _ -> f IntRepr (RSMVar instr)) mp
    return (RSMVars mp')
  accessComposite (RSMVar instr) (RSMVars mp) = mp Map.! instr
  eqComposite (RSMVars mp1) (RSMVars mp2) = do
    res <- sequence $ Map.elems $ Map.intersectionWith
           (\e1 e2 -> e1 .==. e2) mp1 mp2
    case res of
      [] -> true
      [e] -> return e
      _ -> and' res
  revType _ _ (RSMVar _) = IntRepr

instance GetType (RSMVar v) where
  getType (RSMVar _) = IntRepr

extractLine :: (Backend b,Ord var) => Coeffs b var
            -> SMT b (Integer,[(var,Integer)])
extractLine coeffs = do
  rcoeffs <- mapM getValue (coeffsVar coeffs)
  IntValueC rconst <- getValue (coeffsConst coeffs)
  return (rconst,[ (var,val)
                 | (var,IntValueC val) <- Map.toList rcoeffs
                 , val/=0 ])

mineStates :: (Backend b,SMTMonad b ~ IO,Ord var) => IO b -> RSMState loc var
              -> IO (RSMState loc var,[(Integer,[(var,Integer)])])
mineStates backend st
  = runStateT
    (do
        nlocs <- mapM (\loc -> do
                          ncls <- sequence $
                                  Map.mapWithKey
                                  (\vars cls -> do
                                      res <- lift $ mineClass vars cls
                                      case res of
                                        Nothing -> return cls
                                        Just (ncls,nprops) -> do
                                          modify (nprops++)
                                          return ncls)
                                  (rsmClasses loc)
                          return $ RSMLoc ncls
                      ) (rsmLocations st)
        return $ RSMState nlocs (rsmStates st)
    ) []
  where
    mineClass vars cls
      | Set.size cls <= 2 = return Nothing
      | Set.size cls > 6 = return $ Just (Set.empty,[])
    mineClass vars cls = do
      res <- withBackendExitCleanly backend $ do
        setOption (ProduceUnsatCores True)
        setOption (ProduceModels True)
        coeffs <- createCoeffs vars
        notAllZero coeffs >>= assert
        revMp <- createLines coeffs cls
        res <- checkSat
        case res of
          Sat -> do
                   lines <- extractLine coeffs
                   return $ Right lines
          Unsat -> do
                     core <- getUnsatCore
                     let coreMp = Map.fromList [ (cid,()) | cid <- core ]
                         coreLines = Set.fromList $ Map.elems $ Map.intersection revMp coreMp
                     return $ Left coreLines
      case res of
        Right lines -> return (Just (Set.empty,[lines]))
        Left coreLines -> do
          let noCoreLines = Set.difference cls coreLines
              Just (coreLine1,coreLines1) = Set.minView coreLines
              Just (coreLine2,coreLines2) = Set.minView coreLines1
          res1 <- mineClass vars (Set.insert coreLine1 noCoreLines)
          case res1 of
            Just (ncls,lines) -> return (Just (Set.union coreLines1 ncls,lines))
            Nothing -> do
              res2 <- mineClass vars (Set.insert coreLine2 noCoreLines)
              case res2 of
                Just (ncls,lines) -> return (Just (Set.insert coreLine1 $
                                                   Set.union coreLines2 ncls,lines))
                Nothing -> return Nothing
