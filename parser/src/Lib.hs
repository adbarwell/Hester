module Lib where

import System.Environment
import System.IO

import Data.List
import qualified Data.Text as T

import Language.Haskell.Parser

-- test :: String ParseResult HsModule
test x = parseModule "module Sum where\n\nimport Prelude hiding (sum)\n\nsum []    = 0\nsum (h:t) = (+) h (sum t)\n\nmain = sum [1..4]"

removeStrayClosingBraces :: String -> String
removeStrayClosingBraces ast =
  T.unpack $ T.replace (T.pack "}") (T.pack ")") $ T.pack ast

rewriteRecordHsImportDecl :: String -> String
rewriteRecordHsImportDecl ast =
  if isInfixOf "HsImportDecl" ast
    then T.unpack $
          T.replace (T.pack ", importSpecs = ") (T.pack " ) ( ") $
          T.replace (T.pack ", importAs = ") (T.pack " ) ( ") $
          T.replace (T.pack ", importQualified = ") (T.pack " ) ( ") $
          T.replace (T.pack ", importModule = ") (T.pack " ) ( ") $
          T.replace (T.pack "HsImportDecl {importLoc = ") (T.pack "HsImportDecl (") $ T.pack ast
    else ast

rewriteRecordSrcLoc :: String -> String
rewriteRecordSrcLoc ast =
  if isInfixOf "SrcLoc" ast
    then T.unpack $
          T.replace (T.pack ", srcColumn =") (T.pack "") $
          T.replace (T.pack ", srcLine =") (T.pack "") $
          T.replace (T.pack "SrcLoc {srcFilename =") (T.pack "(SrcLoc") $ T.pack ast
    else ast

prettyprint :: String -> String
prettyprint = removeStrayClosingBraces . rewriteRecordHsImportDecl . rewriteRecordSrcLoc

run :: String -> IO ()
run arg = do
  fd <- openFile arg ReadMode
  contents <- hGetContents fd
  putStrLn $ show contents
  case parseModule contents of
    ParseFailed l err -> do hClose fd ; error err
    ParseOk ast -> do
      hClose fd
      putStrLn ""
      let ast_str = prettyprint (show ast)
      putStrLn $ ast_str
      writeFile "../Idris/AST.idr" ("module AST\n\nimport public Haskell98\n\npublic export\nast : HsModuleTy\nast = " ++ ast_str ++ "\n")
  putStrLn "End"

someFunc :: IO ()
someFunc = do
  args <- getArgs
  case args of
    [] -> error "No Filename Given"
    (arg : _) -> run arg
  -- fd <- openFile "../HsExamples/Sum.hs" ReadMode
  -- putStrLn $ show fd
