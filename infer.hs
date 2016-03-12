-- # infer.hs - A simple implementation of type inference
--
-- The point of type inference is to take a program and assign a type to every
-- variable and every expression in the program.
--
-- To do this, we'll need ways of representing programs and types in memory.
-- We'll need some way to represent all the type signatures of the functions that
-- make up a language's standard library.
--
-- Then, using those parts, we'll write code that takes a program and a standard
-- library as arguments, and returns a type-annotated copy of that program.
--
--
-- ## Using the `ST` monad
--
-- The only sensible algorithm I know for type inference is stateful,
-- so we'll be writing stateful Haskell code today, using the `ST` monad.

import Control.Monad.ST
import Data.STRef

-- I'm a big fan of `ST`. You can write Python code in Haskell!
-- But the best thing about it is that *statefulness doesn't leak*
-- to the rest of your program. Variables that you create in `ST` code
-- can only be read or written from within the same execution of that `ST` code.
-- All inputs and outputs are immutable values.


-- ## Types
--
-- I said we'd need a way to represent types and programs in memory. Here goes:

data Type = TInt
          | TString
          | TFun Type Type
          deriving (Eq, Show)

-- A type is either `Int`, `String`, or a function type `(a -> b)` where a and b
-- are two types. This is pretty bare-bones and we could elaborate on it a great deal.
-- But the big problem here is: this `Type` type is stateless, and we will need
-- mutable type values (!) to run the inference algorithm.
--
-- Therefore we have the `IType` type (`I` for inference). This is what we'll use
-- during the process of inferring types.

data IType s = ITInt
             | ITString
             | ITFun (IType s) (IType s)
             | ITVar (STRef s (Maybe (IType s)))
             deriving Eq

-- For testing, I'd like to use the simpler `Type` (which doesn't have that
-- weird `s` parameter floating around), so I need a function to translate:
toType :: IType s -> ST s Type
toType ITInt = return TInt
toType ITString = return TString
toType (ITFun a b) = do
  a' <- toType a
  b' <- toType b
  return $ TFun a' b'
toType (ITVar cell) = do
  c <- readSTRef cell
  case c of
    Nothing -> error "unresolved type variable"
    Just t -> toType t

-- Like `Type`, `IType` has `Int`, `String`, and `Fun` types.
-- But then we also have `TVar`, which represents *unknown types*,
-- what we'll call "type variables".
-- Each `TVar` contains a mutable cell
-- so that we can add more information about the type as we learn more.
--
-- *   `ITVar (newSTRef Nothing)` is an unknown type.
--
-- *   `ITVar (newSTRef (Just ITInt))` is the type Int - this is an initially
--     unknown type that we later inferred.
--
-- *   `ITVar (newSTRef (Just v))`, where v is also an `ITVar`, is a type that has
--     been *unified* with another type variable. v might already be known, or it
--     may still be unknown; but we do know that this type and v are the same.

-- Now we have a few simple functions on types.

-- Convert a type to a string, for display.
formatType :: IType s -> ST s String
formatType ITInt = return "Int"
formatType ITString = return "String"
formatType (ITFun a r) = do
  astr <- formatType a
  rstr <- formatType r
  return $ "(" ++ astr ++ " -> " ++ rstr ++ ")"
formatType v = do
  u <- unwrap v
  case u of
    ITVar _ -> return "_"
    other -> formatType other

-- Unwrap type variables.
--
-- If the argument is a type variable that has already been unified with
-- another type, return that type (after unwrapping it as well, since there can
-- be chains of unifications).  Otherwise, return the argument unchanged.
--
-- There's one other sneaky thing going on here. If we *do* encounter a chain of
-- type variables that point to other type variables etc., this function quietly
-- eliminates the chain by changing *every* mutable cell in the chain to point
-- directly to the type at the end of the chain. (This isn't necessary for
-- correctness; it's just a speed hack.)
unwrap :: IType s -> ST s (IType s)
unwrap (ITVar v) = do
  t <- readSTRef v
  case t of
    Nothing -> return $ ITVar v
    Just u -> do
      u' <- unwrap u
      writeSTRef v (Just u')
      return u'
unwrap other = return other


-- ## Expressions
--
-- We also need a way to represent programs in memory, and that's the `Expr` type.
-- The way this is defined is a little wonky, because I want to be able to
-- store location information alongside every node.

data Expr_ e = Name String
           | Literal Value
           | Lambda Location String e
           | Call e e
           | Case e [(Pattern, e)]

type Location = (Int, Int)

data Expr = Expr Location (Expr_ Expr)

exprLocation (Expr loc _) = loc

-- Case expressions contain *patterns,* so we'll need a definition for that:

data Pattern_ = PWildcard
              | PLiteral Value
              | PVar String
              | PConstructor Location String [Pattern]

data Pattern = Pattern Location Pattern_

patternLocation (Pattern loc _) = loc


-- ## Constructors
--
-- A constructor, like Just or Nothing or True or False,
-- is a little different from other bindings.
-- It can be used in case-expressions. We have to know the type of each field.
--
-- (An alternative here would be:
--
--     data TypeOrConstructor s = TypeOrConstructor {
--         type :: IType s, isConstructor :: Bool }
--
-- but then when analyzing case expressions, we'd have to reverse-engineer the
-- field types from the constructor type.)

data TypeOrConstructor s = TocType (IType s)
                         | TocConstructor [IType s] (IType s)

-- When it's not used in a pattern, a constructor has a type just like
-- any other binding. A no-argument constructor has a data type;
-- constructors with arguments have a function type.
tocToType (TocType t) = t
tocToType (TocConstructor args rtype) = foldr ITFun rtype args

-- Values that can be represented as literals in programs.
data Value = VInt Int | VString String

typeOf (VInt _) = ITInt
typeOf (VString _) = ITString


-- ## Type environments

data TypeEnv s = TypeEnv {
  envScopes :: STRef s [[(String, TypeOrConstructor s)]],
  envErrors :: STRef s [String]
}

newTypeEnv :: ST s (TypeEnv s)
newTypeEnv = do
  scopes <- newSTRef []
  errors <- newSTRef []
  return $ TypeEnv { envScopes = scopes,
                     envErrors = errors }

lookupToc :: TypeEnv s -> String -> ST s (Maybe (TypeOrConstructor s))
lookupToc env name = do
  scopes <- readSTRef (envScopes env)
  return $ multiLookup name scopes

multiLookup _ [] = Nothing
multiLookup key (alist:etc) = case lookup key alist of
  Nothing -> multiLookup key etc
  Just v -> Just v

lookupType :: TypeEnv s -> String -> ST s (Maybe (IType s))
lookupType env name = do
  result <- lookupToc env name
  return $ case result of
    Nothing -> Nothing
    Just toc -> Just (tocToType toc)

lookupConstructorTypes :: TypeEnv s -> Location -> String -> ST s (Maybe ([IType s], IType s))
lookupConstructorTypes env loc name = do
  mtoc <- lookupToc env name
  return $ case mtoc of
    Nothing -> Nothing
    Just (TocType _) -> Nothing
    Just (TocConstructor argTypes rtype) -> Just (argTypes, rtype)

unify :: TypeEnv s -> Location -> IType s -> IType s -> ST s ()
unify env loc expectedType actualType = do
  e <- unwrap expectedType
  a <- unwrap actualType
  case (e, a) of
    (ITVar v1, _) -> writeSTRef v1 (Just a)
    (_, ITVar v2) -> writeSTRef v2 (Just e)
    (ITInt, ITInt) -> return ()
    (ITString, ITString) -> return ()
    (ITFun a1 r1, ITFun a2 r2) -> do
      unify env loc a1 a2
      unify env loc r1 r2
    (_, _) -> do
      estr <- formatType e
      astr <- formatType a
      reportError env loc ("mismatched types (expected " ++ estr ++ ", got " ++ astr ++ ")")

pushScope :: TypeEnv s -> ST s ()
pushScope env =
  modifySTRef (envScopes env) ([] :)

popScope :: TypeEnv s -> ST s ()
popScope env =
  modifySTRef (envScopes env) tail

bind :: TypeEnv s -> Location -> String -> IType s -> ST s ()
bind env loc name bindingType = do
  (scope : outer) <- readSTRef (envScopes env)
  case lookup name scope of
    Nothing -> return ()
    Just _ -> reportError env loc ("conflicting definitions for '" ++ name ++ "'")
  let scope' = (name, TocType bindingType) : scope
  writeSTRef (envScopes env) (scope' : outer)

newTypeVariable :: TypeEnv s -> Location -> ST s (IType s)
newTypeVariable env loc = do
  r <- newSTRef Nothing
  return $ ITVar r

reportError :: TypeEnv s -> Location -> String -> ST s ()
reportError env loc message =
  modifySTRef (envErrors env) (message :)


-- ## Type inference

inferExprType :: TypeEnv s -> Expr -> IType s -> ST s ()

inferExprType env (Expr loc (Name s)) expectedType = do
  result <- lookupType env s
  case result of
    Nothing -> reportError env loc ("undefined variable `" ++ s ++ "`")
    Just actualType -> unify env loc expectedType actualType

inferExprType env (Expr loc (Literal v)) expectedType =
  unify env loc expectedType (typeOf v)

inferExprType env (Expr loc (Lambda argLocation arg body)) expectedType = do
  pushScope env
  argType <- newTypeVariable env argLocation
  bodyType <- newTypeVariable env (exprLocation body)
  bind env argLocation arg argType
  inferExprType env body bodyType
  popScope env
  unify env loc (ITFun argType bodyType) expectedType

inferExprType env (Expr _ (Call fn arg)) expectedType = do
  argType <- newTypeVariable env (exprLocation arg)
  inferExprType env fn (ITFun argType expectedType)
  inferExprType env arg argType

inferExprType env (Expr _ (Case d cases)) expectedType = do
  dType <- newTypeVariable env (exprLocation d)
  inferExprType env d dType
  let inferCase (pattern, result) = do
        pushScope env
        inferPatternType env pattern dType
        inferExprType env result expectedType
        popScope env
  sequence_ $ map inferCase cases

-- Patterns, too, have types which must be inferred.
-- They can also have sub-patterns whose types must be inferred recursively.
inferPatternType :: TypeEnv s -> Pattern -> IType s -> ST s ()

inferPatternType env (Pattern _ PWildcard) expectedType = return ()

inferPatternType env (Pattern loc (PLiteral value)) expectedType =
  unify env loc (typeOf value) expectedType

inferPatternType env (Pattern loc (PVar name)) expectedType =
  bind env loc name expectedType

inferPatternType env (Pattern loc (PConstructor nameLocation name argPatterns)) expectedType = do
  m <- lookupConstructorTypes env nameLocation name
  case m of
    Nothing -> reportError env nameLocation ("no such constructor '" ++ name ++ "'")
    Just (argTypes, returnType) -> do
      unify env loc returnType expectedType
      if length argTypes /= length argPatterns
        then reportError env loc ("wrong number of constructor arguments in pattern (" ++
                                  "expected " ++ show (length argTypes) ++ ", " ++
                                  "got " ++ show (length argPatterns) ++ ")")
        else let inferArgPattern (pattern, expectedType) =
                   inferPatternType env pattern expectedType
             in sequence_ $ map inferArgPattern (zip argPatterns argTypes)


-- ## A simple test

infer :: Expr -> Either [String] Type
infer expr = runST $ do
  env <- newTypeEnv
  pushScope env
  bind env (0, 0) "parse" (ITFun ITString ITInt)
  t <- newTypeVariable env (0, 11)
  inferExprType env expr t
  popScope env
  errors <- readSTRef (envErrors env)
  if errors /= []
    then return $ Left errors
    else do t' <- toType t
            return $ Right t'

assertInfersType expr t =
  case infer expr of
    Left errors -> errors
    Right answer -> if answer == t
                    then ["passed"]
                    else ["test failed: inferred type was " ++ show answer ++ ", expected " ++ show t]

test1 = assertInfersType
    (Expr (0, 11) (Call
                   (Expr (0, 5) (Name "parse"))
                   (Expr (6, 11) (Literal (VString "123")))))
    TInt

test2 = assertInfersType
        (Expr (0, 15) (Lambda (1, 2) "x"
                       (Expr (7, 15) (Call
                                      (Expr (7, 12) (Name "parse"))
                                      (Expr (14, 15) (Name "x"))))))
        (TFun TString TInt)

main = sequence_ $ map putStrLn $ (test1 ++ test2)
