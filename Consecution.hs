{-# LANGUAGE FlexibleContexts #-}
module Consecution where

import SMTPool
import Domain

import Language.SMTLib2
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Vector (Vector)
import qualified Data.Vector as Vec

data Consecution inp st = Consecution { consecutionPool :: SMTPool ConsecutionInstance (ConsecutionVars inp st)
                                      , consecutionFrames :: Vector IntSet
                                      , consecutionFrameHash :: Int
                                      , consecutionCubes :: Vector (AbstractState st)
                                      , consecutionInitial :: st -> SMTExpr Bool
                                      }

data ConsecutionInstance
  = ConsecutionInstance { framesLoaded :: Vector (IntSet,SMTExpr Bool)
                        , frameHash :: Int
                        }

data ConsecutionVars inp st
  = ConsecutionVars { consecutionInput :: inp
                    , consecutionNxtInput :: inp
                    , consecutionState :: st
                    , consecutionNxtState :: st
                    , consecutionNxtAsserts :: [SMTExpr Bool]
                    }

consecutionNew :: SMTBackend b IO => IO b
                  -> SMT (ConsecutionVars inp st) -- ^ How to allocate the transition relation
                  -> (st -> SMTExpr Bool) -- ^ The initial condition
                  -> IO (Consecution inp st)
consecutionNew backend alloc init = do
  pool <- createSMTPool' backend
          (ConsecutionInstance { framesLoaded = Vec.empty
                               , frameHash = 0 }) $ do
            setOption (ProduceModels True)
            setOption (ProduceUnsatCores True)
            alloc
  return $ Consecution { consecutionPool = pool
                       , consecutionFrames = Vec.empty
                       , consecutionFrameHash = 0
                       , consecutionCubes = Vec.empty
                       , consecutionInitial = init }

extendFrames :: Consecution inp st -> Consecution inp st
extendFrames cons = cons { consecutionFrames = Vec.snoc (consecutionFrames cons) IntSet.empty }

frontier :: Consecution inp st -> Int
frontier cons = Vec.length (consecutionFrames cons) - 2

consecutionPerform :: Domain st -> Consecution inp st -> Int -> (ConsecutionVars inp st -> SMT a) -> IO a
consecutionPerform dom cons lvl act = do
  Right res <- withSMTPool' (consecutionPool cons) $
               \inst vars -> do
                 ninst <- updateInstance vars inst
                 res <- stack $ do
                   Vec.mapM_ (\(_,act) -> assert act) (Vec.drop lvl $ framesLoaded ninst)
                   act vars
                 return $ Right (res,ninst)
  return res
  where
    updateInstance vars inst = do
      let numFrames = Vec.length (consecutionFrames cons)
          numLoaded = Vec.length (framesLoaded inst)
      loaded <- if numFrames > numLoaded
                then (do
                         nloaded <- Vec.generateM (numFrames-numLoaded) $
                                    \i -> do
                                      act <- varNamed ("frameAct"++show (numLoaded+i))
                                      if numLoaded+i==0
                                        then assert $ act .=>. (consecutionInitial cons (consecutionState vars))
                                        else return ()
                                      return (IntSet.empty,act)
                         return $ (framesLoaded inst) Vec.++ nloaded)
                else return $ framesLoaded inst
      loaded2 <- if frameHash inst < consecutionFrameHash cons
                 then Vec.zipWithM
                      (\cubes (loaded,act) -> do
                          mapM_ (\i -> assert $ act .=>.
                                       (not' $ toDomainTerm ((consecutionCubes cons) Vec.! i) dom
                                        (consecutionState vars))
                                ) (IntSet.toList $ IntSet.difference cubes loaded)
                          return (cubes,act)
                      ) (consecutionFrames cons) loaded
                 else return loaded
      return $ ConsecutionInstance { framesLoaded = loaded2
                                   , frameHash = consecutionFrameHash cons }

getCubeId :: AbstractState st -> Consecution inp st -> (Int,Consecution inp st)
getCubeId st cons = case Vec.findIndex (==st) (consecutionCubes cons) of
  Just i -> (i,cons)
  Nothing -> (Vec.length (consecutionCubes cons),
              cons { consecutionCubes = Vec.snoc (consecutionCubes cons) st })

getCube :: Int -> Consecution inp st -> AbstractState st
getCube st_id cons = (consecutionCubes cons) Vec.! st_id

addCubeAtLevel :: Int -> Int -> Consecution inp st -> Consecution inp st
addCubeAtLevel cube lvl cons
  | IntSet.member cube frame = cons
  | otherwise = cons { consecutionFrames = (consecutionFrames cons) Vec.//
                                           [(lvl,IntSet.insert cube frame)]
                     , consecutionFrameHash = succ (consecutionFrameHash cons)
                     }
  where
    frame = (consecutionFrames cons) Vec.! lvl

{-
modifyFrames :: (Vector IntSet -> m (a,Maybe (Vector IntSet))) -> Consecution inp st -> m (a,Consecution inp st)
modifyFrames change cons = do
  (result,res) <- change (consecutionFrames cons)
  case res of
   Nothing -> return (result,cons)
   Just nframes -> return (result,cons { consecutionFrames = nframes
                                       , consecutionFrameHash = succ (consecutionFrameHash cons)
                                       })-}
