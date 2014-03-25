{-# LANGUAGE DeriveDataTypeable,TypeFamilies,PackageImports,GADTs #-}
module LLVMLoader where

import Model

import LLVM.General.AST
import LLVM.General.AST.Instruction as I
import LLVM.General.AST.Constant as C

import LLVM.General
import LLVM.General.Context
import LLVM.General.PrettyPrint
import LLVM.General.Transforms
import LLVM.General.PassManager
import LLVM.General.AST.IntegerPredicate

import "mtl" Control.Monad.Error

import Data.Typeable
import Data.Fix
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (mapAccumL)
import Prelude hiding (EQ,foldl)
import Data.Foldable (foldl)
import Data.Proxy
import System.Environment (getArgs)
import Data.Maybe (catMaybes)

import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Value(..))
import Language.SMTLib2.Pipe (renderExpr')

import Data.Graph.Inductive

-- Right now we only want to support integers and bools, so our value type
-- looks like this:
data Value = BoolVal { asBoolVal :: SMTExpr Bool }
           | IntVal { asIntVal :: SMTExpr Integer }
           deriving (Typeable,Eq,Ord)

instance Show Value where
  show (BoolVal x) = show x
  show (IntVal x) = show x

data ValueType = BoolType
               | IntType
               deriving (Typeable,Eq,Ord,Show)

instance Args Value where
  type ArgAnnotation Value = ValueType
  foldExprs f s x BoolType = do
    (ns,nx) <- f s (asBoolVal x) ()
    return (ns,BoolVal nx)
  foldExprs f s x IntType = do
    (ns,nx) <- f s (asIntVal x) ()
    return (ns,IntVal nx)
  foldsExprs f s xs BoolType = do
    (ns,nxs,nx) <- foldsExprs f s [ (x,y) | (BoolVal x,y) <- xs ] ()
    return (ns,fmap BoolVal nxs,BoolVal nx)
  foldsExprs f s xs IntType = do
    (ns,nxs,nx) <- foldsExprs f s [ (x,y) | (IntVal x,y) <- xs ] ()
    return (ns,fmap IntVal nxs,IntVal nx)
  extractArgAnnotation (BoolVal _) = BoolType
  extractArgAnnotation (IntVal _) = IntType
  toArgs BoolType xs = do
    (res,xs') <- toArgs () xs
    return (BoolVal res,xs')
  toArgs IntType xs = do
    (res,xs') <- toArgs () xs
    return (IntVal res,xs')
  fromArgs (BoolVal x) = [UntypedExpr x]
  fromArgs (IntVal x) = [UntypedExpr x]
  getSorts ~(BoolVal x) BoolType = getSorts x ()
  getSorts ~(IntVal x) IntType = getSorts x ()
  getArgAnnotation _ ((Fix BoolSort):xs) = (BoolType,xs)
  getArgAnnotation _ ((Fix IntSort):xs) = (IntType,xs)
  showsArgs i p (BoolVal x) = let (showX,ni) = showExpr i 11 x
                              in (showParen (p>10) (showString "BoolVal " .
                                                    showX),ni)
  showsArgs i p (IntVal x) = let (showX,ni) = showExpr i 11 x
                             in (showParen (p>10) (showString "IntVal " .
                                                   showX),ni)
  

type ValueMap = Map Name Value
type TypeMap = Map Name ValueType

newtype Str = Str String

instance Show Str where
  show (Str x) = x

instance Typeable Name where
  typeOf _ = mkTyConApp
             (mkTyCon3 "llvm-general-pure" "LLVM.General.AST.Name" "Name")
             []

--renderCfg :: (Args inp,Args st) => CFGModel inp st -> Gr Str Str
renderCfg :: CFGModel ValueMap ValueMap -> Gr Str Str
renderCfg mdl = let (rest,inps) = foldExprsId (\(i:is) _ ann -> (is,Var i ann)
                                              ) [0..] (error "A") (cfgInpAnnotation mdl)
                    (rest',st) = foldExprsId (\(i:is) _ ann -> (is,Var i ann)
                                             ) rest (error "B") (cfgStAnnotation mdl)
                    smtSt = SMTState { nextVar = head rest'
                                     , nextInterpolationGroup = 0
                                     , allVars = Map.fromList
                                                 [ case val of
                                                      BoolVal (Var i ann)
                                                        -> (i,FunInfo { funInfoId = i
                                                                      , funInfoProxy = Proxy::Proxy ((),Bool)
                                                                      , funInfoArgAnn = ()
                                                                      , funInfoResAnn = ann
                                                                      , funInfoName = Just (nameToString name,0) })
                                                      IntVal (Var i ann)
                                                        -> (i,FunInfo { funInfoId = i
                                                                      , funInfoProxy = Proxy::Proxy ((),Integer)
                                                                      , funInfoArgAnn = ()
                                                                      , funInfoResAnn = ()
                                                                      , funInfoName = Just (nameToString name,0) })
                                                 | (name,val) <- Map.toList inps ]
                                     , namedVars = Map.empty
                                     , nameCount = Map.empty
                                     , declaredDataTypes = emptyDataTypeInfo }
                in gmap (\(inc,nd,node,outg)
                         -> ([ (Str $ show $ f inps st,nd') | (CondJump f,nd') <- inc],
                             nd,
                             Str $ (if nodeAssertion node inps st == constant True
                                    then ""
                                    else "assert "++renderExpr' smtSt (nodeAssertion node inps st)++"\\n")++
                             (unlines' $ [ show nd ++ "~> "++ass
                                         | (nd,ass) <- Map.toList $ fmap (\f -> renderValueMap "#" smtSt st $ f inps st) (nodePhi node) ])++
                             (renderValueMap "" smtSt st (nodeTransformation node inps st)),
                             [ (Str $ show $ f inps st,nd') | (CondJump f,nd') <- outg])
                        ) (cfgGraph mdl)

renderValueMap :: String -> SMTState -> ValueMap -> ValueMap -> String
renderValueMap pre st mp mp'
  = unlines'
    [ pre++nameToString name ++ ":="++(renderValue st val)
    | (name,val) <- Map.toList $
                    Map.differenceWith (\x y -> if x==y
                                                then Nothing
                                                else Just x)
                    mp' mp
    ]

renderValue :: SMTState -> Value -> String
renderValue st (IntVal val) = renderExpr' st val
renderValue st (BoolVal val) = renderExpr' st val

addEndNode :: CFGModel inp st -> CFGModel inp st
addEndNode mdl = mdl { cfgGraph = gr2 }
  where
    [endNode] = newNodes 1 (cfgGraph mdl)
    gr0 = insNode (endNode,CFGNode { nodeAssertion = \_ _ -> constant True
                                   , nodePhi = Map.empty
                                   , nodeTransformation = \_ -> id })
         (cfgGraph mdl)
    gr1 = insEdge (endNode,endNode,CondJump $ \_ _ -> constant True) gr0
    gr2 = foldl (\cgr nd -> case suc cgr nd of
                    [] -> insEdge (nd,endNode,CondJump $ \_ _ -> constant True) cgr
                    _ -> cgr) gr1 (nodes gr1)

extractTR :: [BasicBlock] -> CFGModel ValueMap ValueMap
extractTR blks
  = CFGModel { cfgStAnnotation = tps
             , cfgInpAnnotation = inp_tps
             , cfgGraph = mkGraph [ (n,CFGNode { nodeAssertion = \inps vals -> case assert inps vals of
                                                    [] -> constant True
                                                    [x] -> x
                                                    xs -> app and' xs
                                               , nodePhi = Map.mapKeys
                                                           (\k -> case Map.lookup k nameMp of
                                                               Just (n,_,_,_,_) -> n)
                                                           phis
                                               , nodeTransformation = trans
                                               })
                                  | (n,trans,assert,phis,jumps) <- Map.elems nameMp ]
                          [ (n,n',CondJump f)
                          | (n,trans,assert,phis,jumps) <- Map.elems nameMp,
                            (trg,f) <- jumps,
                            let Just (n',_,_,_,_) = Map.lookup trg nameMp ]
             , cfgInit = 0
             }
  where
    ((inp_tps,tps),blks')
      = mapAccumL (\(inp_tps,tps) blk
                   -> let (name,trans,assert,phis,jumps,inp_tps',tps')
                            = handleBasicBlock blk inp_tps tps
                      in ((inp_tps',tps'),(name,trans,assert,phis,jumps))
                  ) (Map.empty,Map.empty) blks
    nameMp = Map.fromList [ (name,(n,trans,assert,phis,jumps))
                          | (n,(name,trans,assert,phis,jumps)) <- zip [0..] blks' ]

nameToString :: Name -> String
nameToString (Name x) = x
nameToString (UnName w) = "."++show w

toInt' :: Show a => a -> Value -> SMTExpr Integer
toInt' _ (IntVal x) = x
toInt' loc _ = error $ "Value of "++show loc++" is not int."

translateOperand :: ValueMap -> ValueMap -> Operand -> Value
translateOperand inps mp (LocalReference name) = case Map.lookup name mp of
  Just val -> val
  Nothing -> case Map.lookup name inps of
    Just val -> val
translateOperand _ _ (ConstantOperand c) = translateConstant c

translateConstant :: Constant -> Value
translateConstant (Int { integerBits = 1
                       , integerValue = v }) = BoolVal (constant $ v/=0)
translateConstant (Int { integerBits = b
                       , integerValue = v })
  = if 2^(b-1) - 1 <= v
    then IntVal (constant $ - (2^b - v))
    else IntVal (constant v)
translateConstant (C.Add { C.operand0 = lhs
                         , C.operand1 = rhs })
  = IntVal (asIntVal (translateConstant lhs) +
            asIntVal (translateConstant rhs))

handleBasicBlock :: BasicBlock -> TypeMap -> TypeMap
                    -> (Name
                       ,ValueMap -> ValueMap -> ValueMap
                       ,ValueMap -> ValueMap -> [SMTExpr Bool]
                       ,Map Name (ValueMap -> ValueMap -> ValueMap)
                       ,[(Name,ValueMap -> ValueMap -> SMTExpr Bool)]
                       ,TypeMap
                       ,TypeMap)
handleBasicBlock (BasicBlock name instrs term) inp_tps tps
  = let (trans,assert,phis,inp_tps',tps')
          = foldl (\(ctrans,cassert,cphi,cinp_tps,ctps) instr
                   -> let (f,ass,phi,t1,t2) = handleInstruction instr cinp_tps ctps
                      in (\inps vals -> f inps (ctrans inps vals),
                          \inps vals -> ass inps vals ++ cassert inps vals,
                          Map.unionWith (\f1 f2 inps vals
                                         -> f1 inps (f2 inps vals)
                                        ) phi cphi,
                          t1,t2)
                  ) (\_ -> id,\_ _ -> [],Map.empty,inp_tps,tps) instrs
        succs = case term of
          Do (CondBr { condition = op
                     , trueDest = t
                     , falseDest = f }) -> [(t,\inps vals -> case translateOperand inps vals op of
                                                BoolVal x -> x)
                                           ,(f,\inps vals -> case translateOperand inps vals op of
                                                BoolVal x -> not' x)]
          Do (Br { dest = n }) -> [(n,\_ _ -> constant True)]
          _ -> []
    in (name,trans,assert,phis,succs,inp_tps',tps')

handleInstruction :: Named Instruction -> TypeMap -> TypeMap
                     -> (ValueMap -> ValueMap -> ValueMap
                        ,ValueMap -> ValueMap -> [SMTExpr Bool]
                        ,Map Name (ValueMap -> ValueMap -> ValueMap)
                        ,TypeMap
                        ,TypeMap)
handleInstruction (name := (Phi { incomingValues = inc
                                , I.type' = tp })) inp_tps tps
  = (\_ vals -> vals,
     \_ _ -> [],
     Map.fromList [ (src,\inp vals -> Map.insert name (translateOperand inp vals op) vals)
                  | (op,src) <- inc ],
     inp_tps,
     Map.insert name (case tp of
                         IntegerType 1 -> BoolType
                         IntegerType _ -> IntType) tps)
handleInstruction (name := (I.Add { I.operand0 = lhs
                                  , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       val = IntVal (toInt' lhs lval + toInt' rhs rval)
                in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name IntType tps)
handleInstruction (name := (I.Sub { I.operand0 = lhs
                                  , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       val = IntVal (toInt' lhs lval - toInt' rhs rval)
                in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name IntType tps)
handleInstruction (name := (I.Mul { I.operand0 = lhs
                                  , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       val = IntVal (toInt' lhs lval * toInt' rhs rval)
                in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name IntType tps)
handleInstruction (name := (I.Or { I.operand0 = lhs
                                 , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       val = BoolVal (asBoolVal lval .||. asBoolVal rval)
                   in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name BoolType tps)
handleInstruction (name := (I.And { I.operand0 = lhs
                                  , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       val = BoolVal (asBoolVal lval .&&. asBoolVal rval)
                   in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name BoolType tps)
handleInstruction (name := (I.Xor { I.operand0 = lhs
                                  , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       val = BoolVal (app xor [asBoolVal lval,asBoolVal rval])
                   in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name BoolType tps)
handleInstruction (name := (I.ICmp { I.iPredicate = pred
                                   , I.operand0 = lhs
                                   , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = translateOperand inps vals rhs
                       op = case pred of
                         EQ -> (.==.)
                         NE -> \x y -> not' (x .==. y)
                         UGT -> (.>.)
                         UGE -> (.>=.)
                         ULT -> (.<.)
                         ULE -> (.<=.)
                         SGT -> (.>.)
                         SGE -> (.>=.)
                         SLT -> (.<.)
                         SLE -> (.<=.)
                       val = BoolVal (op (toInt' lhs lval) (toInt' rhs rval))
                   in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name BoolType tps)
handleInstruction (name := (I.Shl { I.operand0 = lhs
                                  , I.operand1 = rhs })) inp_tps tps
  = (\inps vals -> let lval = translateOperand inps vals lhs
                       rval = case rhs of
                         ConstantOperand (Int { integerValue = n }) -> constant (2^n)
                       val = IntVal (asIntVal lval * rval)
                in Map.insert name val vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name IntType tps)
handleInstruction (name := (I.Select { I.condition' = cond
                                     , I.trueValue = tval
                                     , I.falseValue = fval })) inp_tps tps
  = (\inps vals -> let cond' = translateOperand inps vals cond
                       tval' = translateOperand inps vals tval
                       fval' = translateOperand inps vals fval
                       res = case tval' of
                         IntVal p -> IntVal (ite (asBoolVal cond') p (asIntVal fval'))
                         BoolVal p -> BoolVal (ite (asBoolVal cond') p (asBoolVal fval'))
                   in Map.insert name res vals,
     \_ _ -> [],
     Map.empty,
     inp_tps,
     Map.insert name IntType tps)
handleInstruction (name := (Call { function = Right (ConstantOperand op)
                                 , arguments = args })) inp_tps tps
  = handleCall (Just name) op args inp_tps tps
handleInstruction (Do (Call { function = Right (ConstantOperand op)
                            , arguments = args })) inp_tps tps
  = handleCall Nothing op args inp_tps tps
handleInstruction instr _ _ = error $ "Can't handle "++show instr

handleCall :: Maybe Name -> Constant -> [(Operand,a)]
              -> TypeMap -> TypeMap
              -> (ValueMap -> ValueMap -> ValueMap
                 ,ValueMap -> ValueMap -> [SMTExpr Bool]
                 ,Map Name (ValueMap -> ValueMap -> ValueMap)
                 ,TypeMap
                 ,TypeMap)
handleCall (Just name) (GlobalReference (Name "__undef_int")) [] inp_tps tps
  = (\inps vals -> vals,
     \_ _ -> [],
     Map.empty,
     Map.insert name IntType inp_tps,
     tps)
handleCall (Just name) (GlobalReference (Name "__undef_bool")) [] inp_tps tps
  = (\inps vals -> vals,
     \_ _ -> [],
     Map.empty,
     Map.insert name BoolType inp_tps,
     tps)
handleCall _ (GlobalReference (Name "assert")) [(op,_)] inp_tps tps
  = (\inps vals -> vals,
     \inps vals -> [case translateOperand inps vals op of
                       BoolVal x -> x],
     Map.empty,
     inp_tps,
     tps)
handleCall name (C.BitCast { C.operand0 = call }) args inp_tps tps
  = handleCall name call args inp_tps tps

translateModule :: String -> IO (CFGModel ValueMap ValueMap)
translateModule f = withContext $ \ctx -> do
  res <- runErrorT $ withModuleFromBitcode ctx (File f)
    (\mod -> do
        withPassManager (PassSetSpec [PromoteMemoryToRegister
                                     ,InstructionCombining
                                     ,ConstantPropagation
                                     ,CorrelatedValuePropagation
                                     ,ConstantMerge
                                     ,DeadCodeElimination
                                     ,DeadInstructionElimination
                                     ,Sinking
                                     ,SimplifyControlFlowGraph
                                     ] Nothing Nothing Nothing) $ \pm -> do
          runPassManager pm mod
          mod' <- moduleAST mod
          let fun = case [ blks
                         | GlobalDefinition (Function _ _ _ _ _ (Name "main") _ _ _ _ _ blks) <- moduleDefinitions mod' ] of
                [x] -> x
              fun' = inlineBools fun
          --putStrLn $ showPretty fun'
          --putStrLn $ graphviz' $ renderCfg $ extractTR fun
          writeCTIGAR f $ mkInfo $ addEndNode $ extractTR fun'
          --runErrorT $ withModuleFromAST ctx mod (\mod'' -> runErrorT $ writeBitcodeToFile (File $ f++".bc") mod'')
          return (extractTR fun')
    )
  case res of
    Right mdl -> return mdl

main = do
  [arg] <- getArgs
  translateModule arg

unlines' :: [String] -> String
unlines' [] = ""
unlines' (x:xs) = x++"\\n"++unlines' xs

-- Trace file generation

data CTIGARInfo = CTIGARInfo { ctigarTR :: TR
                             , ctigarInit :: String
                             , ctigarVars :: [String]
                             , ctigarNondets :: [String]
                             , ctigarAsserts :: [String]
                             }

writeCTIGAR :: String -> CTIGARInfo -> IO ()
writeCTIGAR pref info = do
  writeFile (pref++".tr") (renderTR $ ctigarTR info)
  writeFile (pref++".vars") (unlines $ ctigarVars info)
  writeFile (pref++".asrts") (unlines $ ctigarAsserts info)
  writeFile (pref++".nondet") (unlines $ ctigarNondets info)
  writeFile (pref++".init") (ctigarInit info)

type TR = [(Int,String,String,String)]

renderTR :: TR -> String
renderTR tr = unlines [ show pc ++ ";"++cond++";"++var++";"++val
                      | (pc,cond,var,val) <- tr ]

mkInfo :: CFGModel ValueMap ValueMap -> CTIGARInfo
mkInfo mdl = CTIGARInfo { ctigarTR = jumps++assigns
                        , ctigarInit = renderExpr' smtSt ((Var 0 ()) .==. (constant $ toInteger $ cfgInit mdl))
                        , ctigarVars = "int .s":[ (case tp of
                                                      BoolType -> "bool "
                                                      IntType -> "int ")++nameToString name
                                                | (name,tp) <- Map.toList (cfgStAnnotation mdl) ]
                        , ctigarNondets = [ (case tp of
                                                BoolType -> "bool "
                                                IntType -> "int ")++nameToString name
                                          | (name,tp) <- Map.toList (cfgInpAnnotation mdl) ]
                        , ctigarAsserts = asserts }
  where
    asserts = [ renderExpr' smtSt (((Var 0 ()) .==. (constant $ toInteger nd)) .=>. cond)
              | (nd,cont) <- labNodes (cfgGraph mdl)
              , let cond = nodeAssertion cont inps st
              , cond /= constant True ]
    jumps = [ case cond of
                 CondJump c -> (from,renderExpr' smtSt (c inps st),".s",show to)
            | (from,to,cond) <- labEdges (cfgGraph mdl) ]
    assigns = concat [ [ (nd,renderExpr' smtSt ((Var 0 ()) .==.
                                                (constant $ toInteger from)),
                          nameToString name,
                          renderValue smtSt val)
                       | (from,mp) <- Map.toList phi_ts'
                       , (name,val) <- Map.toList mp ] ++
                       [ (nd,renderExpr' smtSt cond,
                          nameToString name,
                          renderValue smtSt val')
                       | (name,val) <- Map.toList normal_t'
                       , (cond,val') <- unravelITE' val ]
                     | (nd,cont) <- labNodes (cfgGraph mdl)
                     , let normal_t = nodeTransformation cont inps st
                           phi_ts = fmap (\t -> t inps st) (nodePhi cont)
                           normal_t' = foldl (Map.differenceWith (\x y -> if x==y
                                                                          then Just x
                                                                          else Nothing)
                                             ) normal_t phi_ts
                           phi_ts' = fmap (\t -> Map.difference t normal_t'
                                          ) phi_ts
                     ]
    (rest,inps) = foldExprsId (\(i:is) _ ann -> (is,Var i ann)
                              ) [1..] (error "A") (cfgInpAnnotation mdl)
    (rest',st) = foldExprsId (\(i:is) _ ann -> (is,Var i ann)
                             ) rest (error "B") (cfgStAnnotation mdl)
    smtSt = SMTState { nextVar = head rest'
                     , nextInterpolationGroup = 0
                     , allVars = Map.fromList $
                                 [ (0,FunInfo { funInfoId = 0
                                              , funInfoProxy = Proxy::Proxy ((),Integer)
                                              , funInfoArgAnn = ()
                                              , funInfoResAnn = ()
                                              , funInfoName = Just (".s",0)})]++
                                 [ case val of
                                      BoolVal (Var i ann)
                                        -> (i,FunInfo { funInfoId = i
                                                      , funInfoProxy = Proxy::Proxy ((),Bool)
                                                      , funInfoArgAnn = ()
                                                      , funInfoResAnn = ann
                                                      , funInfoName = Just (nameToString name,0) })
                                      IntVal (Var i ann)
                                        -> (i,FunInfo { funInfoId = i
                                                      , funInfoProxy = Proxy::Proxy ((),Integer)
                                                      , funInfoArgAnn = ()
                                                      , funInfoResAnn = ()
                                                      , funInfoName = Just (nameToString name,0) })
                                 | (name,val) <- Map.toList (Map.union inps st) ]
                     , namedVars = Map.empty
                     , nameCount = Map.empty
                     , declaredDataTypes = emptyDataTypeInfo }

unravelITE' :: Value -> [(SMTExpr Bool,Value)]
unravelITE' (BoolVal x) = [ (case c of
                                [] -> constant True
                                [x] -> x
                                _ -> app and' c,BoolVal v)
                            | (c,v) <- unravelITE x ]
unravelITE' (IntVal x) = [ (case c of
                               [] -> constant True
                               [x] -> x
                               _ -> app and' c,IntVal v)
                         | (c,v) <- unravelITE x ]

unravelITE :: SMTExpr a -> [([SMTExpr Bool],SMTExpr a)]
unravelITE (App SMTITE (c,t,f))
  = [ (c:c',expr) | (c',expr) <- unravelITE t ]++
    [ (not' c:c',expr) | (c',expr) <- unravelITE f ]
unravelITE (App (SMTIntArith op) (x,y))
  = [ (c1 ++ c2,App (SMTIntArith op) (x',y'))
    | (c1,x') <- unravelITE x
    , (c2,y') <- unravelITE y ]
unravelITE (App (SMTArith op) args)
  = [ (c,App (SMTArith op) args')
    | (c,args') <- unravelITEs args ]
unravelITE (App SMTMinus (x,y))
  = [ (c1 ++ c2,App SMTMinus (x',y'))
    | (c1,x') <- unravelITE x
    , (c2,y') <- unravelITE y ]
unravelITE x = [([],x)]

unravelITEs :: [SMTExpr a] -> [([SMTExpr Bool],[SMTExpr a])]
unravelITEs [] = [([],[])]
unravelITEs (x:xs) = [ (c++c',x':xs') | (c,x') <- unravelITE x
                                      , (c',xs') <- unravelITEs xs ]

inlineBools :: [BasicBlock] -> [BasicBlock]
inlineBools blks
  = snd $ mapAccumL (\bool_mp (BasicBlock name instrs term)
                     -> let (mp',instrs') = mapAccumL inlineInstr bool_mp instrs
                        in (mp',BasicBlock name (catMaybes instrs') term)
                    ) Map.empty blks
  where
    operandToConstant bool_mp (LocalReference name) = Map.lookup name bool_mp
    operandToConstant _ (ConstantOperand op) = Just op
    inlineInstr bool_mp i@(name := I.And { I.operand0 = lhs
                                         , I.operand1 = rhs })
      = case (do
                 clhs <- operandToConstant bool_mp lhs
                 crhs <- operandToConstant bool_mp rhs
                 return (clhs,crhs)) of
          Just (clhs,crhs)
            -> (Map.insert name (C.And clhs crhs) bool_mp,
                Nothing)
          Nothing -> (bool_mp,Just i)
    inlineInstr bool_mp i@(name := I.Select { I.condition' = cond
                                            , I.trueValue = tval
                                            , I.falseValue = fval
                                            , I.metadata = m})
      = case operandToConstant bool_mp cond of
      Just c -> case (do
                         t <- operandToConstant bool_mp tval
                         f <- operandToConstant bool_mp fval
                         return (t,f)) of
                  Just (t,f) -> (Map.insert name (C.Select c t f) bool_mp,
                                 Nothing)
                  Nothing -> (bool_mp,
                              Just (name := I.Select { I.condition' = ConstantOperand c
                                                     , I.trueValue = tval
                                                     , I.falseValue = fval
                                                     , I.metadata = m }))
      Nothing -> (bool_mp,Just i)
    inlineInstr bool_mp (Do (call@Call { arguments = args }))
      = let nargs = fmap (\(op,par) -> case operandToConstant bool_mp op of
                             Just c -> (ConstantOperand c,par)
                             Nothing -> (op,par)
                         ) args
        in (bool_mp,Just $ Do (call { arguments = nargs }))
    inlineInstr bool_mp i@(name := I.ICmp { I.iPredicate = pred
                                          , I.operand0 = lhs
                                          , I.operand1 = rhs })
      = case (do
                 clhs <- operandToConstant bool_mp lhs
                 crhs <- operandToConstant bool_mp rhs
                 return (clhs,crhs)) of
          Just (clhs,crhs)
            -> (Map.insert name (C.ICmp pred clhs crhs) bool_mp,
                Nothing)
          Nothing -> (bool_mp,Just i)
    inlineInstr bool_mp i = (bool_mp,Just i)
                 
