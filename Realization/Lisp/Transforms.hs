module Realization.Lisp.Transforms where

import Realization.Lisp
import Realization.Lisp.Value
import Realization.Lisp.Array

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Struct (Struct(..),Tree(..))
import qualified Language.SMTLib2.Internals.Type.Struct as Struct

import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare
import Data.Functor.Identity
import Control.Monad.State

replaceVarWith :: LispRev tp -> LispExpr tp -> LispProgram -> LispProgram
replaceVarWith (LispRev rname@(LispName sz tps name) val) nexpr prog = case val of
  RevVar ridx
    -> let nname = LispName sz (removeType ridx tps) name
       in LispProgram { programAnnotation = programAnnotation prog
                      , programState = adjustMap rname nname (programState prog)
                      , programInput = adjustMap rname nname (programInput prog)
                      , programGates = adjustGateMap rname ridx nname nexpr (programGates prog)
                      , programNext = adjustNextMap rname ridx nname nexpr (programNext prog)
                      , programProperty = fmap (replaceInExpr rname ridx nname nexpr)
                                          (programProperty prog)
                      , programInit = adjustInitMap rname ridx nname nexpr (programInit prog)
                      , programInvariant = fmap (replaceInExpr rname ridx nname nexpr)
                                           (programInvariant prog)
                      , programAssumption = fmap (replaceInExpr rname ridx nname nexpr)
                                            (programAssumption prog)
                      , programPredicates = fmap (replaceInExpr rname ridx nname nexpr)
                                            (programPredicates prog)
                      }
  where
    adjustMap :: LispName '(lvl,tps) -> LispName '(lvl,tps')
              -> DMap LispName Annotation
              -> DMap LispName Annotation
    adjustMap from to mp
      = DMap.fromList
        [ case geq from name of
          Nothing -> entry
          Just Refl -> to :=> (Annotation ann)
        | entry@(name :=> (Annotation ann)) <- DMap.toList mp ]

    adjustGateMap :: LispName '(sz,tps) -> List Natural idx
                  -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                  -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                  -> DMap LispName LispGate
                  -> DMap LispName LispGate
    adjustGateMap rname ridx nname nexpr mp
      = DMap.fromList
        [ case geq rname name of
          Nothing -> name :=> (LispGate (replaceInOtherVar rname ridx nname nexpr def) ann)
          Just Refl -> nname :=> (LispGate (replaceInOtherVar rname ridx nname nexpr $ removeFromVar ridx def) (Annotation ann'))
        | (name@(LispName _ _ _) :=> (LispGate def ann@(Annotation ann'))) <- DMap.toList mp ]

    adjustNextMap :: LispName '(sz,tps) -> List Natural idx
                  -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                  -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                  -> DMap LispName (LispVar LispExpr)
                  -> DMap LispName (LispVar LispExpr)
    adjustNextMap rname ridx nname nexpr mp
      = DMap.fromList
        [ case geq rname name of
          Nothing -> name :=> (replaceInOtherVar rname ridx nname nexpr nxt)
          Just Refl -> nname :=> (replaceInOtherVar rname ridx nname nexpr (removeFromVar ridx nxt))
        | (name@(LispName _ _ _) :=> nxt) <- DMap.toList mp ]

    adjustInitMap :: LispName '(sz,tps) -> List Natural idx
                  -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                  -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                  -> DMap LispName LispInit
                  -> DMap LispName LispInit
    adjustInitMap rname ridx nname nexpr mp
      = DMap.fromList
        [ case geq rname name of
          Nothing -> name :=> LispInit lv
          Just Refl -> nname :=> LispInit (LispValue sz (removeType ridx val))
        | (name@(LispName _ _ _) :=> (LispInit lv@(LispValue sz val))) <- DMap.toList mp ]
    
    removeType :: LispIndex idx -> Struct el tps
               -> Struct el (Struct.Insert tps idx (Node '[]))
    removeType idx tps = Struct.insert tps idx (Struct Nil)

    removeFromVar :: LispIndex idx
                  -> LispVar LispExpr '(lvl,tps)
                  -> LispVar LispExpr '(lvl,Struct.Insert tps idx (Node '[]))
    removeFromVar idx (NamedVar (LispName lvl tp name) cat)
      = NamedVar (LispName lvl (removeType idx tp) name) cat
    removeFromVar idx (LispStore var idx' arr el) = case geq idx idx' of
      Just Refl -> removeFromVar idx var
      -- To avoid the runtime check, we would need to have disequality in the type-system
      Nothing -> let tp = getType el
                     (sz,tps) = lispVarType var
                     tps' = Struct.insert tps idx (Struct Nil)
                     tp' = Struct.elementIndex tps' idx'
                 in case geq tp tp' of
                 Just Refl -> LispStore (removeFromVar idx var) idx' arr el
    removeFromVar idx (LispConstr (LispValue sz val))
      = LispConstr (LispValue sz (removeType idx val))
    removeFromVar idx (LispITE cond ifT ifF)
      = LispITE cond (removeFromVar idx ifT) (removeFromVar idx ifF)

    replaceInOtherVar :: forall sz tps idx sz' tps'.
                         LispName '(sz,tps)
                      -> List Natural idx
                      -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                      -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                      -> LispVar LispExpr '(sz',tps')
                      -> LispVar LispExpr '(sz',tps')
    replaceInOtherVar rname ridx nname nexpr var
      = case replaceInVar rname ridx nname nexpr var of
      Left nvar -> nvar
      Right (Refl,Refl,nvar)
        -> let mkSized :: LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                       -> Sized LispExpr sz (Struct.ElementIndex tps idx)
               mkSized = Sized
               rval = case varToValue nvar of
                 LispValue sz val -> refixValue (snd $ lispVarType var) ridx
                                     (LispValue sz (Struct.insert val
                                                    ridx (Singleton (mkSized nexpr))))
           in LispConstr rval

    replaceInVar :: forall sz tps idx sz' tps'.
                    LispName '(sz,tps)
                 -> List Natural idx
                 -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                 -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                 -> LispVar LispExpr '(sz',tps')
                 -> Either (LispVar LispExpr '(sz',tps'))
                           (sz' :~: sz,tps :~: tps',
                            LispVar LispExpr '(sz,Struct.Insert tps idx (Node '[])))
    replaceInVar rname ridx nname nexpr (NamedVar name cat) = case geq rname name of
      Nothing -> Left (NamedVar name cat)
      Just Refl -> Right (Refl,Refl,NamedVar nname cat)
    replaceInVar rname ridx nname nexpr (LispStore var idx arr el)
      = case replaceInVar rname ridx nname nexpr var of
      Left nvar -> Left (LispStore nvar idx narr nel)
      Right (Refl,Refl,nvar) -> case geq ridx idx of
        Just Refl -> Right (Refl,Refl,nvar)
        Nothing -> let tp = getType el
                       (sz,tps) = lispVarType var
                       tps' = Struct.insert tps ridx (Struct Nil)
                       tp' = Struct.elementIndex tps' idx
                   in case geq tp tp' of
                   Just Refl -> Right (Refl,Refl,LispStore nvar idx narr nel)
      where
        narr = replaceInExprs rname ridx nname nexpr arr
        nel = replaceInExpr rname ridx nname nexpr el
    replaceInVar rname ridx nname nexpr (LispConstr (LispValue sz val))
      = Left $ LispConstr $
        LispValue (replaceInSize rname ridx nname nexpr sz)
        (runIdentity $ Struct.mapM
         (\(Sized e) -> return $ Sized $ replaceInExpr rname ridx nname nexpr e) val)
    replaceInVar rname ridx nname nexpr (LispITE cond v1 v2) = case rv1 of
      Left nv1 -> case rv2 of
        Left nv2 -> Left (LispITE ncond nv1 nv2)
        Right (Refl,Refl,nv2)
          -> let (_,tp1) = lispVarType nv1
                 mkSized :: LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                         -> Sized LispExpr sz (Struct.ElementIndex tps idx)
                 mkSized = Sized
                 --nv2'' :: LispValue '(sz,Struct.Insert tps idx (Leaf (Struct.ElementIndex tps idx))) LispExpr
             in case varToValue nv2 of
             LispValue sz nv2'
               -> let (_,tp2) = lispValueType nv2''
                      nv2'' = LispValue sz (Struct.insert nv2' ridx
                                            (Singleton (mkSized nexpr)))
                  in case geq tp1 tp2 of
                  Just Refl -> Left (LispITE ncond nv1
                                     (LispConstr nv2''))
      where
        ncond = replaceInExpr rname ridx nname nexpr cond
        rv1 = replaceInVar rname ridx nname nexpr v1
        rv2 = replaceInVar rname ridx nname nexpr v2

    replaceInExpr :: forall sz tps idx tp.
                     LispName '(sz,tps)
                  -> List Natural idx
                  -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                  -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                  -> LispExpr tp
                  -> LispExpr tp
    replaceInExpr rname ridx nname nexpr (LispExpr e)
      = LispExpr (runIdentity $ mapExpr return return return return return return return
                  (return.replaceInExpr rname ridx nname nexpr) e)
    replaceInExpr rname ridx nname nexpr e@(LispRef var idx)
      = case replaceInVar rname ridx nname nexpr var of
      Left nvar -> LispRef nvar idx
      Right (Refl,Refl,nvar) -> case geq idx ridx of
        Just Refl -> nexpr
        Nothing -> let ne = LispRef nvar idx
                       tp1 = getType e
                       tp2 = getType ne
                   in case geq tp1 tp2 of
                   Just Refl -> ne
    replaceInExpr rname ridx nname nexpr (LispSize var idx)
      = case replaceInVar rname ridx nname nexpr var of
      Left nvar -> LispSize nvar idx
      Right (Refl,Refl,nvar) -> LispSize nvar idx
    replaceInExpr rname ridx nname nexpr (LispEq v1 v2) = case nv1 of
      Left nvar1 -> case nv2 of
        Left nvar2 -> LispEq nvar1 nvar2
        Right (Refl,Refl,nvar2)
          -> let mkSized :: LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                         -> Sized LispExpr sz (Struct.ElementIndex tps idx)
                 mkSized = Sized
                 rval2 = case varToValue nvar2 of
                   LispValue nsz2 nval2 -> refixValue (snd $ lispVarType nvar1) ridx
                                           (LispValue nsz2 (Struct.insert nval2
                                                            ridx (Singleton (mkSized nexpr))))
             in LispEq (LispConstr (varToValue nvar1)) (LispConstr rval2)
      Right (Refl,Refl,nvar1) -> case nv2 of
        Right (Refl,Refl,nvar2) -> LispEq nvar1 nvar2
        Left nvar2 -> let mkSized :: LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                                  -> Sized LispExpr sz (Struct.ElementIndex tps idx)
                          mkSized = Sized
                          rval1 = case varToValue nvar1 of
                            LispValue nsz1 nval1
                              -> refixValue (snd $ lispVarType nvar2) ridx
                                 (LispValue nsz1 (Struct.insert nval1
                                                  ridx (Singleton (mkSized nexpr))))
                      in LispEq (LispConstr rval1) (LispConstr (varToValue nvar2))
      where
        nv1 = replaceInVar rname ridx nname nexpr v1
        nv2 = replaceInVar rname ridx nname nexpr v2
    replaceInExpr rname ridx nname nexpr (ExactlyOne xs)
      = ExactlyOne $ fmap (replaceInExpr rname ridx nname nexpr) xs
    replaceInExpr rname ridx nname nexpr (AtMostOne xs)
      = AtMostOne $ fmap (replaceInExpr rname ridx nname nexpr) xs      

    refixValue :: GetType e
               => Struct Repr tps
               -> List Natural idx
               -> LispValue '(sz,Struct.Insert
                                 (Struct.Insert tps idx (Node '[]))
                                 idx (Leaf (Struct.ElementIndex tps idx))) e
               -> LispValue '(sz,tps) e
    refixValue tps idx val = case geq tps (snd $ lispValueType val) of
      Just Refl -> val

    replaceInExprs :: LispName '(sz,tps)
                   -> List Natural idx
                   -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                   -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                   -> List LispExpr tp
                   -> List LispExpr tp
    replaceInExprs rname ridx nname nexpr Nil = Nil
    replaceInExprs rname ridx nname nexpr (e ::: es)
      = (replaceInExpr rname ridx nname nexpr e) :::
        (replaceInExprs rname ridx nname nexpr es)

    replaceInSize :: LispName '(sz,tps)
                  -> List Natural idx
                  -> LispName '(sz,Struct.Insert tps idx (Node '[]))
                  -> LispExpr (Arrayed sz (Struct.ElementIndex tps idx))
                  -> Size LispExpr sz'
                  -> Size LispExpr sz'
    replaceInSize rname ridx nname nexpr (Size tps szs)
      = Size tps (replaceInExprs rname ridx nname nexpr szs)

    varToValue :: forall sz tps.
                  LispVar LispExpr '(sz,tps)
               -> LispValue '(sz,tps) LispExpr
    varToValue v@(NamedVar (LispName sz tps name) cat)
      = LispValue (Size sz (mkSize sz))
        (runIdentity $ Struct.mapIndexM
         (\idx tp -> return (Sized $ LispRef v idx)) tps)
      where
        mkSize :: List Repr sz -> List LispExpr (SizeList sz)
        mkSize sz = runIdentity $ List.mapIndexM
                    (\idx tp -> return (LispSize v idx))
                    (sizeListType sz)
    varToValue (LispStore v idx dyn el)
      = case varToValue v of
      LispValue sz nv -> LispValue sz (snd $ runIdentity $ Struct.access nv idx $
                                       \arr -> accessArrayElement dyn arr $
                                               \_ -> return ((),el))
    varToValue (LispConstr val) = val
    varToValue (LispITE c v1 v2) = runIdentity $ iteValue c (varToValue v1) (varToValue v2)

fsck :: LispProgram -> [String]
fsck prog = [ "In gate definition of "++show gtName++"("++show def++"): "++defError
            | gtName@(LispName _ _ _) :=> LispGate def _ <- DMap.toList (programGates prog)
            , defError <- fsckVar def ] ++
            [ "In next definition of "++show nxtName++"("++show var++"): "++nxtError
            | nxtName@(LispName _ _ _) :=> var <- DMap.toList (programNext prog)
            , nxtError <- fsckVar var ]
  where
    fsckExpr :: LispExpr tp -> [String]
    fsckExpr (LispExpr e) = execState
                            (mapExpr return return return return return return return
                             (\e' -> do
                                 errs <- get
                                 let nerrs = fsckExpr e'
                                 put (errs++nerrs)
                                 return e') e) []
    fsckExpr (LispRef var idx) = fsckVar var
    fsckExpr (LispSize var idx) = fsckVar var
    fsckExpr (LispEq v1 v2) = fsckVar v1 ++ fsckVar v2
    fsckExpr (ExactlyOne xs) = concat $ fmap fsckExpr xs
    fsckExpr (AtMostOne xs) = concat $ fmap fsckExpr xs

    fsckVar :: LispVar LispExpr '(sz,tps) -> [String]
    fsckVar (NamedVar name@(LispName sz tp _) State)
      = case findName (\sz tps _ -> show (sz,tps))
             name (programState prog) of
        Right _ -> []
        Left alts -> ["state variable "++show name++" of type "++show (sz,tp)++" not found."++
                      (case alts of
                        [] -> ""
                        _ -> " Variables with the same name but different types: "++
                             unwords alts)]
    fsckVar (NamedVar name@(LispName sz tp _) Input)
      = case findName (\sz tps _ -> show (sz,tps))
             name (programInput prog) of
        Right _ -> []
        Left alts -> ["input variable "++show name++" of type "++show (sz,tp)++" not found."++
                      (case alts of
                        [] -> ""
                        _ -> " Variables with the same name but different types: "++
                             unwords alts)]
    fsckVar (NamedVar name@(LispName sz tp _) Gate)
      = case findName (\sz tps _ -> show (sz,tps))
             name (programGates prog) of
        Right _ -> []
        Left alts -> ["gate variable "++show name++" of type "++show (sz,tp)++" not found."++
                      (case alts of
                        [] -> ""
                        _ -> " Variables with the same name but different types: "++
                             unwords alts)]
    fsckVar (LispStore var _ dyn e)
      = fsckVar var ++
        execState (List.mapM (\d -> do
                                 errs <- get
                                 put $ errs++(fsckExpr d)
                                 return d
                             ) dyn) []++
        fsckExpr e
    fsckVar (LispConstr (LispValue (Size _ sz) vals))
      = execState (do
                      List.mapM (\d -> do
                                    modify (++(fsckExpr d))
                                    return d) sz
                      Struct.mapM (\(Sized e) -> do
                                      modify (++(fsckExpr e))
                                      return undefined) vals
                      return ()) []
    fsckVar (LispITE c v1 v2)
      = fsckExpr c ++ fsckVar v1 ++ fsckVar v2

    findName :: (forall sz' tps' . List Repr sz' -> Struct Repr tps' -> a '( sz',tps') -> b)
             -> LispName '(sz,tps) -> DMap LispName a
             -> Either [b] (a '(sz,tps))
    findName sim name@(LispName _ _ rname) mp = case DMap.lookup name mp of
      Just res -> Right res
      Nothing -> case [ ()
                      | oname :=> cont <- DMap.toList mp
                      , case gcompare name oname of
                        GEQ -> True
                        _ -> False ] of
                 [] -> Left [ sim sz tps cont
                            | (LispName sz tps oname) :=> cont <- DMap.toList mp
                            , oname==rname ]
                 _ -> if DMap.valid mp
                      then error "unknown BUG in dependent map implementation."
                      else error $ "REAL BUG in dependent map:\n"++
                           DMap.showTreeWith
                           (\name@(LispName sz tp rname) _ -> show rname++show (sz,tp))
                           True False mp
