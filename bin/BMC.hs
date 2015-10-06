module Main where

import Realization
import Realization.Lisp
import Realization.Lisp.Value
import System.IO
import System.Console.GetOpt hiding (NoArg)
import qualified System.Console.GetOpt as Opt
import System.Environment
import Language.SMTLib2.LowLevel
import Language.SMTLib2.Debug
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Z3
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
--import Language.SMTLib2.DatatypeEmulator
import Args
import PartialArgs
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans (MonadIO,liftIO)
import qualified Data.Text as T
import Data.Proxy
import Data.GADT.Show

data Options = Options { showHelp :: Bool
                       , solver :: String
                       , solverArgs :: [String]
                       , bmcDepth :: Integer
                       , incremental :: Bool
                       , debug :: Bool }

defaultOptions :: Options
defaultOptions = Options { showHelp = False
                         , solver = "z3"
                         , solverArgs = ["-in","-smt2"]
                         , bmcDepth = 10
                         , incremental = False
                         , debug = False }

optDescr :: [OptDescr (Options -> Options)]
optDescr = [Option ['h'] ["help"] (Opt.NoArg $ \opt -> opt { showHelp = True }) "Show this help"
           ,Option ['d'] ["depth"] (ReqArg (\str opt -> opt { bmcDepth = read str }) "n") "The BMC depth"
           ,Option ['s'] ["solver"] (ReqArg (\str opt -> let solv:args = words str
                                                         in opt { solver = solv
                                                                , solverArgs = args }) "bin") "The SMT solver executable"
           ,Option ['i'] ["incremental"] (Opt.NoArg $ \opt -> opt { incremental = True }) "Run in incremental mode"
           ,Option [] ["debug"] (Opt.NoArg $ \opt -> opt { debug = True }) "Output the SMT stream"]

main = do
  args <- getArgs
  let (xs,extra,errs) = getOpt Permute optDescr args
  case extra of
   [] -> return ()
   _ -> error $ "Unknown arguments: "++show extra
  case errs of
   [] -> return ()
   _ -> error $ "Error while parsing arguments: "++unlines errs
  let opts = foldl (flip id) defaultOptions xs
  if showHelp opts
    then putStrLn $ usageInfo "Usage:\n\n    vvt-bmc [OPTIONS]\n\nAvailable options:" optDescr
    else (do
             prog <- fmap parseProgram $ readLispFile stdin
             pipe <- createPipe (solver opts) (solverArgs opts)
             --let pipe = z3Solver
             let act :: forall b. (Backend b,MonadIO (B.SMTMonad b))
                     => SMT b (Maybe [Unpacked (State LispProgram) (B.Constr b)])
                 act = do
                   st0 <- createComposite (\(LispRev (LispName name) _)
                                           -> updateBackend $ \b -> do
                                              (v,b1) <- B.declareVar b (Just $ T.unpack name)
                                              B.toBackend b1 (Var v)
                                          ) (programState prog)
                   inp0 <- createComposite (\(LispRev (LispName name) _)
                                            -> updateBackend $ \b -> do
                                               (v,b1) <- B.declareVar b (Just $ T.unpack name)
                                               B.toBackend b1 (Var v)
                                           ) (programInput prog)
                   init <- initialState (\e -> updateBackend $ \b -> B.toBackend b e) prog st0
                   updateBackend' $ \b -> B.assert b init
                   bmc prog (incremental opts) (bmcDepth opts) 0 st0 inp0 []
             res <- if debug opts
                    then (withBackend (namedDebugBackend "bmc" $ pipe) act)
                    else (withBackend pipe act)
             case res of
              Nothing -> putStrLn "No bug found."
              Just bug -> do
                mapM_ (\p -> putStrLn $ showsPrec 0 p "") bug)
  where
    bmc :: (TransitionRelation t,Backend b,MonadIO (B.SMTMonad b))
        => t -> Bool -> Integer -> Integer
        -> State t (B.Expr b) -> Input t (B.Expr b)
        -> [(State t (B.Expr b),B.Expr b BoolType)]
        -> SMT b (Maybe [Unpacked (State t) (B.Constr b)])
    bmc prog inc l n st inp sts
      | n>=l = do
          if inc
            then do
              cond <- toBackend $ App Not $ Arg (snd $ head sts) NoArg
              updateBackend' $ \b -> B.assert b cond
            else do
              cond <- allEqFromList (fmap snd sts) $ \arg -> toBackend $ App (Logic Or) arg
              cond' <- toBackend $ App Not (Arg cond NoArg)
              updateBackend' $ \b -> B.assert b cond'
          res <- checkSat
          case res of
            Sat -> fmap Just $
                   mapM (\(st,_) -> unliftComp (\e -> updateBackend $ \b -> B.getValue b e)
                                               (defLifting id) st
                        ) sts
            Unsat -> return Nothing
    bmc prog inc l n st inp sts = do
      invar <- stateInvariant (\e -> updateBackend $ \b -> B.toBackend b e) prog st inp
      updateBackend' $ \b -> B.assert b invar
      let gts0 = startingProgress prog
      (assumps,gts1) <- declareAssumptions
                        (\e -> updateBackend $ \b -> B.toBackend b e)
                        (\name e -> updateBackend $ \b -> do
                           (v,b1) <- B.defineVar b name e
                           B.toBackend b1 (Var v))
                        prog st inp gts0
      mapM_ (\e -> updateBackend' $ \b -> B.assert b e) assumps
      (asserts,gts2) <- declareAssertions
                        (\e -> updateBackend $ \b -> B.toBackend b e)
                        (\name e -> updateBackend $ \b -> do
                           (v,b1) <- B.defineVar b name e
                           B.toBackend b1 (Var v))
                        prog st inp gts1
      res <- if inc
             then stack $ do
               liftIO $ putStrLn $ "Level "++show n
               negProp <- mapM (\e -> toBackend $ App Not (Arg e NoArg)) asserts
                          >>= \lst -> allEqFromList lst $
                                      \arg -> toBackend $ App (Logic Or) arg
               updateBackend' $ \b -> B.assert b negProp
               r <- checkSat
               case r of
                 Sat -> do
                          vals <- mapM (\st -> unliftComp (\e -> updateBackend $
                                                                 \b -> B.getValue b e)
                                               (defLifting id) st
                                       ) (st:(fmap fst sts))
                          return $ Just vals
                 Unsat -> return Nothing
             else return Nothing
      case res of
       Just bug -> return $ Just bug
       Nothing -> do
         (nxt,gts3) <- declareNextState
                       (\e -> updateBackend $ \b -> B.toBackend b e)
                       (\name e -> updateBackend $ \b -> do
                          (v,b1) <- B.defineVar b name e
                          B.toBackend b1 (Var v))
                       prog st inp gts2
         ninp <- createComposite (\_ --(LispRev (LispName name) _)
                                  -> updateBackend $ \b -> do
                                       (v,b1) <- B.declareVar b Nothing --(Just $ T.unpack name)
                                       B.toBackend b1 (Var v)
                                 ) (inputAnnotation prog)
         conjAss <- allEqFromList asserts $ \arg -> toBackend $ App (Logic And) arg
         bmc prog inc l (n+1) nxt ninp ((st,conjAss):sts)
