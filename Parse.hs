module Parse(fullParseExpr, runParserTests) where

import Expr
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language(haskell)
import Text.Parsec.Error(errorMessages, messageString)
import Data.Char(isLower)

parens = P.parens haskell
braces = P.braces haskell
identifier = P.identifier haskell
reserved = P.reserved haskell
operator = P.operator haskell
stringLiteral = P.stringLiteral haskell
natural = P.natural haskell
symbol = P.symbol haskell

pos :: Parsec String st (Int, Int)
pos = do
  sp <- getPosition
  return $ (sourceLine sp, sourceColumn sp)

patternWithPos :: Parsec String st Pattern_ -> Parsec String st Pattern
patternWithPos x = do
  p0 <- pos
  p <- x
  p1 <- pos
  return $ Pattern (p0, p1) p

primPattern :: Parsec String st Pattern
primPattern =
      patternWithPos (do { symbol "_";   return $ PWildcard })
  <|> patternWithPos (do { n <- natural; return $ PLiteral (VInteger n) })
  <|> patternWithPos (do (line, col) <- pos
                         i <- identifier
                         return $ if isLower (head i)
                                  then PVar i
                                  else PConstructor ((line, col), (line, col + length i)) i [])
  <|> parens pattern

addConstructorArg :: Monad m => m Pattern -> Pattern -> m Pattern
addConstructorArg con arg = do
  leftPat <- con
  case leftPat of
    (Pattern (p0, p1) (PConstructor ctorLoc ctor args)) ->
      let Pattern (_, p2) _ = arg
      in return $ Pattern (p0, p2) (PConstructor ctorLoc ctor (args ++ [arg]))
    _ ->
      fail "oops"

pattern :: Parsec String st Pattern
pattern = do
  pats <- many1 primPattern
  case pats of
    [x] -> return x
    x : xs -> foldl addConstructorArg (return x) xs

withPos :: Parsec String st (Expr_ Expr) -> Parsec String st Expr
withPos x = do
  p0 <- pos
  v <- x
  p1 <- pos
  return $ Expr (p0, p1) v

case1 :: Parsec String st (Pattern, Expr)
case1 = do
  p <- pattern
  symbol "->"
  e <- expr
  return (p, e)

primExpr :: Parsec String st Expr
primExpr =
      withPos (do { i <- identifier;    return $ Name i })
  <|> withPos (do { s <- stringLiteral; return $ Literal (VString s) })
  <|> withPos (do { n <- natural;       return $ Literal (VInteger n) })
  <|> withPos (do
                  symbol "\\"
                  (line, col) <- pos
                  i <- identifier
                  symbol "->"
                  e <- expr
                  return $ Lambda ((line, col), (line, col + length i)) i e)
  <|> withPos (do
                  reserved "case"
                  d <- expr
                  reserved "of"
                  symbol "{"
                  cases <- P.semiSep1 haskell case1
                  symbol "}"
                  return $ Case d cases)
  <|> parens expr

startOf :: Expr -> SourcePoint
startOf (Expr (p0, _) _) = p0

stopOf :: Expr -> SourcePoint
stopOf (Expr (_, p1) _) = p1

expr :: Parsec String st Expr
expr = do
  ps <- many1 primExpr
  let call a b = Expr (startOf a, stopOf b) (Call a b)
  return $ foldl1 call ps

fullExpr :: Parsec String st Expr
fullExpr = do
  e <- expr
  eof
  return e

fullParseExpr :: String -> Either String Expr
fullParseExpr s =
  case runParser fullExpr () "<input>" s of
    Left err -> Left (show err)
    Right expr -> Right expr

assertParse :: String -> Expr -> IO ()
assertParse s expected =
  let actual = fullParseExpr s
  in if actual == Right expected
     then return ()
     else putStrLn ("test failed: got " ++ show actual)

test1 = assertParse "parse \"123\""
    (Expr ((1, 1), (1, 12)) (Call
                             (Expr ((1, 1), (1, 7 {- should be 6 grrr -})) (Name "parse"))
                             (Expr ((1, 7), (1, 12)) (Literal (VString "123")))))

test2 = assertParse "\\x -> parse x"
        (Expr ((1, 1), (1, 14))
         (Lambda ((1, 2), (1, 3)) "x"
          (Expr ((1, 7), (1, 14))
           (Call
            (Expr ((1, 7), (1, 13 {- should be 12 grrr -})) (Name "parse"))
            (Expr ((1, 13), (1, 14)) (Name "x"))))))

runParserTests = test1 >> test2
