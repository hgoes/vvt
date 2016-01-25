{-# LANGUAGE ScopedTypeVariables,TypeFamilies,ViewPatterns #-}
module Realization.Threaded.ThreadFinder where

import LLVM.FFI
import Foreign.Ptr (Ptr,nullPtr)
import Foreign.Storable (peek)

data Quantity = Finite Integer
              | Infinite
              deriving (Show,Eq)

data ThreadLocation = ThreadSpawnLocation { spawningInstruction :: Ptr CallInst
                                          , spawnedFunction :: Ptr Function
                                          , quantity :: Quantity
                                          }
                    | AllocationLocation { allocInstruction :: Ptr Instruction
                                         , quantity :: Quantity
                                         , allocType' :: AllocKind
                                         , allocSize' :: Maybe (Ptr Value)
                                         }
                    | ReturnLocation { returningFunction :: Ptr Function
                                     , returnedType :: Ptr Type
                                     }
                    deriving (Show,Eq,Ord)

data AllocKind = NormalAlloc (Ptr Type)
               | ThreadIdAlloc [Ptr CallInst]
               deriving (Show,Eq,Ord)

updateQuantity :: (Quantity -> Quantity) -> ThreadLocation -> ThreadLocation
updateQuantity f l@(ThreadSpawnLocation { quantity = q })
  = l { quantity = f q }
updateQuantity f l@(AllocationLocation { quantity = q })
  = l { quantity = f q }
updateQuantity f l = l

getThreadSpawns' :: Ptr Module -> Ptr Function -> IO [ThreadLocation]
getThreadSpawns' mod fun = do
  loopInfo <- newLoopInfo
  manager <- newFunctionPassManager mod
  functionPassManagerAdd manager loopInfo
  errors <- functionPassManagerRun manager fun
  if not errors
    then do
    base <- loopInfoGetBase loopInfo
    getThreadSpawns fun base
    else error "Failed to run loop info pass."

getThreadSpawns :: Ptr Function -> Ptr (LoopInfoBase BasicBlock Loop) -> IO [ThreadLocation]
getThreadSpawns fun loopInfo = do
  blks <- getBasicBlockList fun >>= ipListToList
  analyzeBlocks blks
  where
    analyzeBlocks [] = return []
    analyzeBlocks (blk:blks) = do
      instrs <- getInstList blk >>= ipListToList
      analyzeInstructions instrs blk blks
    analyzeInstructions [] _ blks = analyzeBlocks blks
    analyzeInstructions (i:is) blk blks = case castDown i of
      Just call -> do
        cv <- callInstGetCalledValue call
        case castDown cv of
         Just (call_fun::Ptr Function) -> do
           name <- getNameString call_fun
           case name of
            "__thread_spawn" -> do
              threadVal <- callInstGetArgOperand call 1
              case castDown threadVal of
               Just threadFun -> do
                 loop <- loopInfoBaseGetLoopFor loopInfo blk
                 rest <- analyzeInstructions is blk blks
                 return $ (ThreadSpawnLocation { spawningInstruction = call
                                               , spawnedFunction = threadFun
                                               , quantity = if loop==nullPtr
                                                            then Finite 1
                                                            else Infinite
                                               }):rest
               Nothing -> error "Spawning dynamic functions not supported."
            "malloc" -> do
              sz <- callInstGetArgOperand call 0
              tp <- usedType i
              rtp <- case tp of
                Just (Left r) -> return r
                Nothing -> do
                  ctp <- getType i
                  case castDown ctp of
                    Just (ptp::Ptr PointerType) -> sequentialTypeGetElementType ptp
              rsz <- case castDown sz of
                Just isz -> do
                  APInt _ val <- constantIntGetValue isz >>= peek
                  byteSize <- simpleTypeByteSize rtp
                  return (Just (val `div` byteSize))
                Nothing -> return Nothing
              loop <- loopInfoBaseGetLoopFor loopInfo blk
              rest <- analyzeInstructions is blk blks
              let quant = case (loop==nullPtr,rsz) of
                            (True,Just n) -> Finite n
                            (False,Just 1) -> Infinite
                            (True,Nothing) -> Infinite
              return $ AllocationLocation { allocInstruction = i
                                          , quantity = quant
                                          , allocType' = NormalAlloc rtp
                                          , allocSize' = case quant of
                                                           Infinite -> Just sz
                                                           _ -> Nothing }:rest
            "calloc" -> do
              -- XXX: Ignore the member size parameter for now...
              num <- callInstGetArgOperand call 0
              tp <- usedType i
              case tp of
               Nothing -> error $ "Callocs that aren't casted aren't supported yet."
               Just (Left rtp) -> do
                 loop <- loopInfoBaseGetLoopFor loopInfo blk
                 rest <- analyzeInstructions is blk blks
                 return $ AllocationLocation { allocInstruction = i
                                             , quantity = if loop==nullPtr
                                                          then Finite 1
                                                          else Infinite
                                             , allocType' = NormalAlloc rtp
                                             , allocSize' = Just num }:rest
            "pthread_exit" -> do
              arg <- callInstGetArgOperand call 0
              tp <- realReturnType arg
              rest <- analyzeInstructions is blk blks
              return $ ReturnLocation { returningFunction = fun
                                      , returnedType = tp }:rest
            _ -> analyzeInstructions is blk blks
      Nothing -> case castDown i of
        Just alloc -> do
          loop <- loopInfoBaseGetLoopFor loopInfo blk
          sz <- allocaInstGetArraySize alloc
          {-tp <- do
            spawns <- getThreadSpawns alloc
            case spawns of
              [] -> do
                tp <- getType (alloc :: Ptr AllocaInst) >>= sequentialTypeGetElementType
                return $ NormalAlloc tp
              _ -> return $ ThreadIdAlloc spawns-}
          tp <- fmap NormalAlloc $ getType (alloc :: Ptr AllocaInst) >>= sequentialTypeGetElementType
          rest <- analyzeInstructions is blk blks
          return $ (AllocationLocation { allocInstruction = i
                                       , quantity = if loop==nullPtr
                                                    then Finite 1
                                                    else Infinite
                                       , allocType' = tp
                                       , allocSize' = if loop==nullPtr
                                                      then Nothing
                                                      else Just sz
                                       }):rest
        Nothing -> case castDown i of
          Just ret -> do
            rval <- returnInstGetReturnValue ret
            tp <- realReturnType rval
            rest <- analyzeInstructions is blk blks
            return (ReturnLocation { returningFunction = fun
                                   , returnedType = tp }:rest)
          Nothing -> analyzeInstructions is blk blks
    getThreadSpawns :: ValueC v => Ptr v -> IO [Ptr CallInst]
    getThreadSpawns val = do
      begin <- valueUseBegin val
      end <- valueUseEnd val
      get begin end
      where
        get cur end = do
          finished <- valueUseIteratorEq cur end
          if finished
            then return []
            else do
            use <- valueUseIteratorDeref cur
            nxt <- valueUseIteratorNext cur
            user <- useGetUser use
            case castDown user of
              Just cast -> do
                x <- getThreadSpawns (cast::Ptr CastInst)
                xs <- get nxt end
                return (x++xs)
              Nothing -> case castDown user of
                Just call -> do
                  cv <- callInstGetCalledValue call
                  name <- getNameString cv
                  case name of
                    "__thread_spawn" -> do
                      rest <- get nxt end
                      return (call:rest)
                    _ -> get nxt end
                Nothing -> get nxt end

realReturnType :: Ptr Value -> IO (Ptr Type)
realReturnType (castDown -> Just (bc::Ptr BitCastInst))
  = getOperand bc 0 >>= realReturnType
realReturnType (castDown -> Just (i2p::Ptr IntToPtrInst))
  = getOperand i2p 0 >>= realReturnType
realReturnType (castDown -> Just (c::Ptr ConstantExpr))
  = fmap castUp (constantExprAsInstruction c) >>= realReturnType
realReturnType (castDown -> Just phi)
  = phiNodeGetIncomingValue phi 0 >>= realReturnType
realReturnType val = getType val

getThreadArgument :: Ptr Function
                  -> IO (Maybe (Ptr Argument,Either (Ptr Type) (Ptr IntegerType)))
getThreadArgument fun = do
  args <- functionGetArgumentList fun >>= ipListToList
  case args of
   [] -> return Nothing
   arg:_ -> do
     tp <- usedType arg
     case tp of
      Nothing -> return Nothing
      Just tp -> return (Just (arg,tp))

usedType :: ValueC v => Ptr v -> IO (Maybe (Either (Ptr Type) (Ptr IntegerType)))
usedType val = do
  begin <- valueUseBegin val
  end <- valueUseEnd val
  getUses begin end
  where
    getUses cur end = do
      isEnd <- valueUseIteratorEq cur end
      if isEnd
        then return Nothing
        else do
        user <- valueUseIteratorDeref cur >>= useGetUser
        valueUseIteratorNext cur
        case user of
          (castDown -> Just bitcast) -> do
            tp <- getType (bitcast :: Ptr BitCastInst)
            case castDown tp of
              Just ptp -> do
                rtp <- sequentialTypeGetElementType (ptp :: Ptr PointerType)
                getUses' (Left rtp) cur end
              Nothing -> error "Bitcast is not a pointer."
          (castDown -> Just p2i) -> do
            tp <- getType (p2i::Ptr PtrToIntInst)
            case castDown tp of
              Just itp -> getUses' (Right (itp::Ptr IntegerType)) cur end
          _ -> getUses cur end
    getUses' tp cur end = do
      isEnd <- valueUseIteratorEq cur end
      if isEnd
        then return (Just tp)
        else do
        user <- valueUseIteratorDeref cur >>= useGetUser
        valueUseIteratorNext cur
        case user of
          (castDown -> Just bitcast) -> do
            tp' <- getType (bitcast :: Ptr BitCastInst)
            case castDown tp' of
              Just ptp -> do
                rtp <- sequentialTypeGetElementType (ptp :: Ptr PointerType)
                if Left rtp==tp
                  then getUses' tp cur end
                  else error "Pointer is bitcast to multiple different types."
              Nothing -> error "Bitcast is not a pointer."
          (castDown -> Just p2i) -> do
            tp' <- getType (p2i::Ptr PtrToIntInst)
            case castDown tp' of
              Just itp -> if Right (itp::Ptr IntegerType)==tp
                          then getUses' tp cur end
                          else error "Pointer is bitcast to multiple different types."
          _ -> getUses' tp cur end

simpleTypeByteSize :: Ptr Type -> IO Integer
simpleTypeByteSize (castDown -> Just itp) = do
  sz <- getBitWidth itp
  return (sz `div` 8)
simpleTypeByteSize (castDown -> Just (_::Ptr PointerType)) = return 8
simpleTypeByteSize (castDown -> Just str) = do
  num <- structTypeGetNumElements str
  szs <- mapM (\i -> structTypeGetElementType str i >>= simpleTypeByteSize
              ) (if num==0
                 then []
                 else [0..num-1])
  return $ sum szs
simpleTypeByteSize (castDown -> Just vec) = do
  num <- vectorTypeGetNumElements vec
  sz <- sequentialTypeGetElementType vec >>= simpleTypeByteSize
  return $ num*sz
simpleTypeByteSize (castDown -> Just arr) = do
  num <- arrayTypeGetNumElements arr
  sz <- sequentialTypeGetElementType arr >>= simpleTypeByteSize
  return $ num*sz
simpleTypeByteSize tp = do
  typeDump tp
  error $ "simpleTypeByteSize not implemented"

instance Num Quantity where
  (+) Infinite _ = Infinite
  (+) _ Infinite = Infinite
  (+) (Finite n) (Finite m) = Finite (n*m)
  (-) Infinite _ = Infinite
  (-) _ Infinite = Infinite
  (-) (Finite n) (Finite m) = Finite (n-m)
  (*) (Finite n) (Finite m) = Finite (n*m)
  (*) _ _ = Infinite
  abs Infinite = Infinite
  abs (Finite n) = Finite (abs n)
  signum Infinite = Infinite
  signum (Finite n) = Finite (signum n)
  fromInteger n = Finite n

instance Ord Quantity where
  compare Infinite Infinite = EQ
  compare Infinite _ = GT
  compare _ Infinite = LT
  compare (Finite n) (Finite m) = compare n m
