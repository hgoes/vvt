{-# LANGUAGE FlexibleContexts #-}
module Consecution where

import SMTPool
import Domain
import Args

import Language.SMTLib2
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Vector (Vector)
import qualified Data.Vector as Vec

data Consecution inp st
  = Consecution { consecutionPool :: SMTPool (ConsecutionInstance inp st)
                , consecutionFrames :: Vector IntSet
                , consecutionFrameHash :: Int
                , consecutionCubes :: Vector (AbstractState st)
                , consecutionInitial :: CompositeExpr st BoolType
                }

data ConsecutionInstance inp st b
  = ConsecutionInstance { consecutionVars :: ConsecutionVars inp st (Expr b)
                        , framesLoaded :: Vector (IntSet,Expr b BoolType)
                        , frameHash :: Int
                        }

data ConsecutionVars inp st e
  = ConsecutionVars { consecutionInput :: inp e
                    , consecutionNxtInput :: inp e
                    , consecutionState :: st e
                    , consecutionNxtState :: st e
                    , consecutionNxtAsserts :: [e BoolType]
                    }

consecutionNew :: (Backend b,SMTMonad b ~ IO) => IO b
               -> SMT b (ConsecutionVars inp st (Expr b)) -- ^ How to allocate the transition relation
               -> CompositeExpr st BoolType  -- ^ The initial condition
               -> IO (Consecution inp st)
consecutionNew backend alloc init = do
  pool <- createSMTPool backend $ do
    setOption (ProduceModels True)
    setOption (ProduceUnsatCores True)
    vars <- alloc
    return ConsecutionInstance { consecutionVars = vars
                               , framesLoaded = Vec.empty
                               , frameHash = 0 }
  return $ Consecution { consecutionPool = pool
                       , consecutionFrames = Vec.empty
                       , consecutionFrameHash = 0
                       , consecutionCubes = Vec.empty
                       , consecutionInitial = init }

extendFrames :: Consecution inp st -> Consecution inp st
extendFrames cons = cons { consecutionFrames = Vec.snoc (consecutionFrames cons) IntSet.empty }

frontier :: Consecution inp st -> Int
frontier cons = Vec.length (consecutionFrames cons) - 2

consecutionPerform :: Composite st
                   => Domain st
                   -> Consecution inp st -> Int
                   -> (forall b. Backend b => ConsecutionVars inp st (Expr b) -> SMT b a)
                   -> IO a
consecutionPerform dom cons lvl act = do
  Right res <- case cons of
    Consecution { consecutionPool = pool }
      -> withSMTPool' pool $
         \inst -> do
           ninst <- updateInstance cons dom inst
           res <- stack $ do
             Vec.mapM_ (\(_,act) -> assert act) (Vec.drop lvl $ framesLoaded ninst)
             act (consecutionVars ninst)
           return $ Right (res,ninst)
  return res
  where
    updateInstance :: (Backend b,Composite st)
                   => Consecution inp st
                   -> Domain st
                   -> ConsecutionInstance inp st b
                   -> SMT b (ConsecutionInstance inp st b)
    updateInstance cons dom inst = do
      let vars = consecutionVars inst
          numFrames = Vec.length (consecutionFrames cons)
          numLoaded = Vec.length (framesLoaded inst)
      loaded <- if numFrames > numLoaded
                then (do
                         nloaded <- Vec.generateM (numFrames-numLoaded) $
                                    \i -> do
                                      actVar <- declareVarNamed bool ("frameAct"++show (numLoaded+i))
                                      if numLoaded+i==0
                                        then do
                                        init <- concretizeExpr
                                                (consecutionState vars)
                                                (consecutionInitial cons)
                                        impl <- actVar .=>. init
                                        assert impl
                                        --assert $ act .=>. (consecutionInitial cons (consecutionState vars))
                                        else return ()
                                      return (IntSet.empty,actVar)
                         return $ (framesLoaded inst) Vec.++ nloaded)
                else return $ framesLoaded inst
      loaded2 <- if frameHash inst < consecutionFrameHash cons
                 then Vec.zipWithM
                      (\cubes (loaded,act) -> do
                          mapM_ (\i -> do
                                    trm <- toDomainTerm ((consecutionCubes cons) Vec.! i) dom (consecutionState vars)
                                    act .=>. (not' trm) >>= assert
                                ) (IntSet.toList $ IntSet.difference cubes loaded)
                          return (cubes,act)
                      ) (consecutionFrames cons) loaded
                 else return loaded
      return inst { framesLoaded = loaded2
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
