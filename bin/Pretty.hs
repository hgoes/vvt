{-# LANGUAGE ViewPatterns,OverloadedStrings #-}
module Main where

import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Text.PrettyPrint
import qualified Data.Text as T
import Data.Attoparsec
import System.IO
import qualified Data.ByteString as BS

main = do
  lisp <- readLisp
  print $ ppLisp lisp

readLisp :: IO L.Lisp
readLisp = do
  str <- BS.hGet stdin 1024
  let parseAll (Done _ r) = return r
      parseAll (Partial f) = do
        str <- BS.hGet stdin 1024
        parseAll (f str)
      parseAll (Fail _ _ err) = error $ "Couldn't parse lisp program: "++err
  parseAll $ parse L.lisp str
  
ppLisp :: L.Lisp -> Doc
ppLisp (L.Symbol name) = text $ T.unpack name
ppLisp (L.String str) = doubleQuotes $ text $ T.unpack str
ppLisp (L.Number num) = ppNumber num
ppLisp (L.List []) = parens empty
ppLisp (L.List (x:xs))
  | hOp x = parens (ppLisp x <+> ppList xs)
  | length xs < 4 = parens (hsep (fmap ppLisp (x:xs)))
  | otherwise = parens (ppLisp x <+> ppList xs)
  where
    hOp (L.Symbol "and") = True
    hOp (L.Symbol "or") = True
    hOp _ = False
ppNumber :: L.Number -> Doc
ppNumber (L.I num) = integer num
ppNumber (L.D num) = double num

ppList :: [L.Lisp] -> Doc
ppList [] = empty
ppList (x@(L.Symbol (T.uncons -> Just (':',_))):y:z)
  = (ppLisp x <+> ppLisp y) $+$
    (ppList z)
ppList (x:xs) = ppLisp x $+$ ppList xs
