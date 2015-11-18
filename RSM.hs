{-# LANGUAGE PackageImports,FlexibleContexts #-}
module RSM where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Language.SMTLib2
import Language.SMTLib2.Internals.Backend (SMTMonad)
import "mtl" Control.Monad.State (runStateT,modify)
import "mtl" Control.Monad.Trans (lift,liftIO,MonadIO)
import Prelude hiding (mapM,sequence)
import Data.Traversable (mapM,sequence)

data RSMState loc var = RSMState { rsmLocations :: Map loc (RSMLoc var)
                                 }

data RSMLoc var = RSMLoc { rsmClasses :: Map (Set var) (Set (Map var Integer))
                         }

data Coeffs b var = Coeffs { coeffsVar :: Map var (Expr b IntType)
                           , coeffsConst :: Expr b IntType
                           }

emptyRSM :: RSMState loc var
emptyRSM = RSMState Map.empty

addRSMState :: (Ord loc,Ord var) => loc -> Map var Integer
               -> RSMState loc var -> RSMState loc var
addRSMState loc instrs st
  = st { rsmLocations = Map.insertWith joinLoc loc (RSMLoc { rsmClasses = Map.singleton (Map.keysSet instrs) (Set.singleton instrs)
                                                           })
                        (rsmLocations st)
       }
  where
    joinLoc :: Ord var => RSMLoc var -> RSMLoc var -> RSMLoc var
    joinLoc l1 l2 = RSMLoc { rsmClasses = Map.unionWith Set.union (rsmClasses l1) (rsmClasses l2)
                           }

createCoeffs :: (Backend b,Ord var) => Set var -> SMT b (Coeffs b var)
createCoeffs instrs = do
  coeffs <- mapM (\instr -> do
                     c <- [declare| Int |]
                     return (instr,c)
                 ) (Set.toAscList instrs)
  c <- [declare| Int |]
  return $ Coeffs { coeffsVar = Map.fromAscList coeffs
                  , coeffsConst = c
                  }

notAllZero :: Backend b => Coeffs b var -> Expr b BoolType
notAllZero coeffs = let args = [ [expr| (not (= c 0)) |] | c <- Map.elems (coeffsVar coeffs) ]
                     in [expr| (or # args) |]

createLine :: (Backend b,Ord var) => Coeffs b var -> Map var Integer -> SMT (Expr b BoolType)
createLine coeffs vars
  = [expr| (= lhs rhs) |]
  where
    lhs = case Map.elems $ Map.intersectionWith (\c i -> let i' = constant (IntValueC i)
                                                         in [expr| (* c i') |]
                                                ) (coeffsVar coeffs) vars of
          [x] -> x
          xs -> [expr| (+ # xs) |]
    rhs = coeffsConst coeffs

createLines :: (Backend b,Ord var) => Coeffs b var -> Set (Map var Integer)
               -> SMT b (Map (ClauseId b) (Map var Integer))
createLines coeffs points = do
  res <- mapM (\point -> do
                  cid <- assertId (createLine coeffs point)
                  return (cid,point)
              ) (Set.toList points)
  return $ Map.fromList res

extractLine :: (Backend b,Ord var) => Coeffs b var -> SMT b [(var -> Expr b IntType) -> Expr b BoolType]
extractLine coeffs = do
  rcoeffs <- mapM getValue (coeffsVar coeffs)
  let rcoeffs' = Map.mapMaybe (\c -> if c==0
                                     then Nothing
                                     else Just c
                              ) rcoeffs
      lhs vals = case Map.elems (Map.mapWithKey
                                 (\instr co -> case co of
                                   1 -> vals instr
                                   -1 -> -(vals instr)
                                   _ -> (constant co)*(vals instr)
                                 ) rcoeffs') of
                  [x] -> x
                  xs -> [expr| (+ # xs) |]
  rconst <- getValue (coeffsConst coeffs)
  return [\vals -> (lhs vals)
                   .<=. (constant rconst)
         ,\vals -> (lhs vals)
                   .<. (constant rconst)]

mineStates :: (Backend b,SMTMonad b ~ IO,Ord var) => IO b -> RSMState loc var
              -> IO (RSMState loc var,[(var -> Expr b IntType) -> Expr b BoolType])
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
        return $ RSMState nlocs
    ) []
  where
    mineClass vars cls
      | Set.size cls <= 2 = return Nothing
      | Set.size cls > 6 = return $ Just (Set.empty,[])
    mineClass vars cls = do
      b <- backend
      res <- SMT.withBackendExitCleanly b $ do
        setOption (ProduceUnsatCores True)
        setOption (ProduceModels True)
        coeffs <- createCoeffs vars
        assert $ notAllZero coeffs
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
        Right lines -> return (Just (Set.empty,lines))
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
{-
extractBlock :: Map (Ptr BasicBlock) Bool -> Ptr BasicBlock
extractBlock mp = case blks of
  [x] -> x
  [] -> error "No basic block is active in state."
  _ -> error "More than one basic block is active in state."
  where
    blks = [ blk | (blk,act) <- Map.toList mp
                 , act ]
-}
