module Main where

import Realization
import Realization.Lisp
import Realization.Lisp.Value
import System.IO
import System.Console.GetOpt hiding (NoArg)
import qualified System.Console.GetOpt as Opt
import System.Environment
import Language.SMTLib2
import Language.SMTLib2.Debug
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Z3
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Embed
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
             let pipe = createPipe (solver opts) (solverArgs opts)
             --let pipe = z3Solver
             let act :: forall b. (Backend b,MonadIO (B.SMTMonad b))
                     => SMT b (Maybe [Unpacked (State LispProgram)])
                 act = do
                   st0 <- createComposite (\_ -> declareVar) (programState prog)
                   inp0 <- createComposite (\_ -> declareVar) (programInput prog)
                   init <- initialState prog st0
                   assert init
                   bmc prog (incremental opts) (bmcDepth opts) 0 st0 inp0 []
             res <- if debug opts
                    then (withBackend (fmap (namedDebugBackend "bmc") pipe) act)
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
        -> SMT b (Maybe [Unpacked (State t)])
    bmc prog inc l n st inp sts
      | n>=l = do
          if inc
            then let (_,cond):_ = sts
                 in [expr| (not cond) |] >>= assert
            else let conds = fmap snd sts
                 in [expr| (not (or # conds)) |] >>= assert
          res <- checkSat
          case res of
            Sat -> fmap Just $
                   mapM (\(st,_) -> unliftComp getValue st
                        ) sts
            Unsat -> return Nothing
    bmc prog inc l n st inp sts = do
      invar <- stateInvariant prog st inp
      assert invar
      let gts0 = startingProgress prog
      (assumps,gts1) <- declareAssumptions
                        (\name e -> [define| e |])
                        prog st inp gts0
      mapM_ assert assumps
      (asserts,gts2) <- declareAssertions
                        (\name e -> [define| e |])
                        prog st inp gts1
      res <- if inc
             then stack $ do
               liftIO $ putStrLn $ "Level "++show n
               negProp <- [expr| (not (or # asserts)) |]
               assert negProp
               r <- checkSat
               case r of
                 Sat -> do
                          vals <- mapM (\st -> unliftComp getValue st
                                       ) (st:(fmap fst sts))
                          return $ Just vals
                 Unsat -> return Nothing
             else return Nothing
      case res of
       Just bug -> return $ Just bug
       Nothing -> do
         (nxt,gts3) <- declareNextState
                       (\name e -> [define| e |])
                       prog st inp gts2
         ninp <- createComposite (\_ --(LispRev (LispName name) _)
                                  -> declareVar
                                 ) (inputAnnotation prog)
         conjAss <- [expr| (and # asserts) |]
         bmc prog inc l (n+1) nxt ninp ((st,conjAss):sts)
