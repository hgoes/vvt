{-# LANGUAGE PackageImports,FlexibleContexts #-}
module RSM where

import Realization.Monolithic

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Foreign.Ptr (Ptr)
import LLVM.FFI (BasicBlock,Instruction)
import Language.SMTLib2
import Language.SMTLib2.Internals
import Data.Typeable (cast)
import "mtl" Control.Monad.State (runStateT,modify)
import "mtl" Control.Monad.Trans (lift)
import Prelude hiding (mapM,sequence)
import Data.Traversable (mapM,sequence)

data RSMState = RSMState { rsmLocations :: Map (Ptr BasicBlock) RSMLoc
                         }

data RSMLoc = RSMLoc { rsmClasses :: Map (Set (Ptr Instruction)) (Set (Map (Ptr Instruction) Integer))
                     }

data Coeffs = Coeffs { coeffsVar :: Map (Ptr Instruction) (SMTExpr Integer)
                     , coeffsConst :: SMTExpr Integer
                     }

emptyRSM :: RSMState
emptyRSM = RSMState Map.empty

addRSMState :: Map (Ptr BasicBlock) Bool
               -> Map (Ptr Instruction) UntypedValue
               -> RSMState -> RSMState
addRSMState blks instrs st
  = st { rsmLocations = Map.insertWith joinLoc curBlk (RSMLoc { rsmClasses = Map.singleton (Map.keysSet onlyInts) (Set.singleton onlyInts)
                                                              })
                        (rsmLocations st)
       }
  where
    curBlk = extractBlock blks
    onlyInts = Map.mapMaybe (\(UntypedValue val) -> cast val) instrs
    joinLoc :: RSMLoc -> RSMLoc -> RSMLoc
    joinLoc l1 l2 = RSMLoc { rsmClasses = Map.unionWith Set.union (rsmClasses l1) (rsmClasses l2)
                           }

createCoeffs :: Monad m => Set (Ptr Instruction) -> SMT' m Coeffs
createCoeffs instrs = do
  coeffs <- mapM (\instr -> do
                     c <- varNamed "coeff"
                     return (instr,c)
                 ) (Set.toAscList instrs)
  c <- varNamed "c"
  return $ Coeffs { coeffsVar = Map.fromAscList coeffs
                  , coeffsConst = c
                  }

notAllZero :: Coeffs -> SMTExpr Bool
notAllZero coeffs = app or' [ not' (c .==. 0) | c <- Map.elems (coeffsVar coeffs) ]

createLine :: Coeffs -> Map (Ptr Instruction) Integer -> SMTExpr Bool
createLine coeffs vars
  = (case Map.elems $ Map.intersectionWith (\c i -> c * (constant i)) (coeffsVar coeffs) vars of
      [x] -> x
      xs -> app plus xs)
    .==.
    (coeffsConst coeffs)

createLines :: Monad m => Coeffs -> Set (Map (Ptr Instruction) Integer)
               -> SMT' m (Map ClauseId (Map (Ptr Instruction) Integer))
createLines coeffs points = do
  res <- mapM (\point -> do
                  cid <- assertId (createLine coeffs point)
                  return (cid,point)
              ) (Set.toList points)
  return $ Map.fromList res

extractLine :: Monad m => Coeffs -> SMT' m [(LatchActs,ValueMap) -> SMTExpr Bool]
extractLine coeffs = do
  rcoeffs <- mapM getValue (coeffsVar coeffs)
  let rcoeffs' = Map.mapMaybe (\c -> if c==0
                                     then Nothing
                                     else Just c
                              ) rcoeffs
      lhs vals = case Map.elems (Map.intersectionWith
                                 (\co v -> case co of
                                            1 -> castUntypedExprValue v
                                            -1 -> -(castUntypedExprValue v)
                                            _ -> (constant co)*(castUntypedExprValue v))
                                 rcoeffs' vals) of
                  [x] -> x
                  xs -> app plus xs
  rconst <- getValue (coeffsConst coeffs)
  return [\(_,vals) -> (lhs vals)
                       .<=. (constant rconst)
         ,\(_,vals) -> (lhs vals)
                       .<. (constant rconst)]

mineStates :: SMTBackend b IO => IO b -> RSMState
              -> IO (RSMState,[(LatchActs,ValueMap) -> SMTExpr Bool])
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
      res <- withSMTBackendExitCleanly b $ do
        setOption (ProduceUnsatCores True)
        setOption (ProduceModels True)
        coeffs <- createCoeffs vars
        assert $ notAllZero coeffs
        revMp <- createLines coeffs cls
        res <- checkSat
        if res
          then (do
                   lines <- extractLine coeffs
                   return $ Right lines)
          else (do
                   core <- getUnsatCore
                   let coreMp = Map.fromList [ (cid,()) | cid <- core ]
                       coreLines = Set.fromList $ Map.elems $ Map.intersection revMp coreMp
                   return $ Left coreLines)
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
