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
import System.IO


-- ## Programs as values
--
-- `Expr`, short for "expression", is the type of programs in this
-- mini-language.  The definition is in a separate module, but to summarize, an
-- expression is one of these:
--
-- *   an identifier, like `map`, `filter`, `True`, etc.
-- *   a string, like `"hello world"`
-- *   a number, like `42`
-- *   a lambda-expression, like `\ f -> f 0`
-- *   a case-expression, like `case x of { True -> 1; False -> 0 }`
-- *   a function call, like `f x`

import Expr
import Parse

-- I'm a fan of `ST`. You can write Python code in Haskell!  But the best thing
-- about it is that *statefulness doesn't leak* to the rest of your program.
-- Variables that you create in `ST` code can only be read or written from
-- within the same execution of that `ST` code.  All inputs and outputs are
-- immutable values.


-- ## Types
--
-- I said we'd need a way to represent types in memory. Here goes:

data Type = TInt
          | TString
          | TFun Type Type
          deriving Eq

-- A type is either `Int`, `String`, or a function type `(a -> b)` where a and b
-- are two types. This is pretty bare-bones and we could elaborate on it a great deal.
-- But the big problem here is: this `Type` type is stateless, and we will need
-- mutable type variables (!) to run the inference algorithm.
--
-- Therefore we have the `MType` type (`M` for mutability). This is what we'll use
-- during the process of inferring types.

data MType s = MTInt
             | MTString
             | MTFun (MType s) (MType s)
             | MTVar (STRef s (Maybe (MType s)))
             deriving Eq

-- Types should be printable.
instance Show Type where
  show TInt = "Int"
  show TString = "String"
  show (TFun a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"

-- Like `Type`, `MType` has `Int`, `String`, and `Fun` types.
-- But then we also have `TVar`, which represents *unknown types*,
-- what we'll call "type variables".
-- Each `TVar` contains a mutable cell
-- so that we can add more information about the type as we learn more.
--
-- *   `MTVar (newSTRef Nothing)` is an unknown type.
--
-- *   `MTVar (newSTRef (Just MTInt))` is the type Int - this is an initially
--     unknown type that we later inferred.
--
-- *   `MTVar (newSTRef (Just v))`, where v is also an `MTVar`, is a type that has
--     been *unified* with another type variable. v might already be known, or it
--     may still be unknown; but we do know that this type and v are the same.

-- Now we have a few simple functions on types.

-- For testing, I'd like to use the simpler `Type` (which doesn't have that
-- weird `s` parameter floating around), so I need a function to translate:
toType :: MType s -> ST s (Maybe Type)
toType MTInt = return $ Just TInt
toType MTString = return $ Just TString
toType (MTFun a b) = do
  a' <- toType a
  b' <- toType b
  case (a', b') of
    (Just ta, Just tb) -> return $ Just (TFun ta tb)
    _ -> return Nothing
toType (MTVar cell) = do
  c <- readSTRef cell
  case c of
    Nothing -> return Nothing
    Just t -> toType t

-- Convert a type to a string, for display.
formatType :: MType s -> ST s String
formatType MTInt = return "Int"
formatType MTString = return "String"
formatType (MTFun a r) = do
  astr <- formatType a
  rstr <- formatType r
  return $ "(" ++ astr ++ " -> " ++ rstr ++ ")"
formatType v = do
  u <- unwrap v
  case u of
    MTVar _ -> return "_"
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
unwrap :: MType s -> ST s (MType s)
unwrap (MTVar v) = do
  t <- readSTRef v
  case t of
    Nothing -> return $ MTVar v
    Just u -> do
      u' <- unwrap u
      writeSTRef v (Just u')
      return u'
unwrap other = return other


-- ## Constructors
--
-- A constructor, like Just or Nothing or True or False,
-- is a little different from other bindings.
-- It can be used in case-expressions. We have to know the type of each field.
--
-- (An alternative here would be:
--
--     data TypeOrConstructor s = TypeOrConstructor {
--         type :: MType s, isConstructor :: Bool }
--
-- but then when analyzing case expressions, we'd have to re-derive the
-- field types from the constructor type.)

data TypeOrConstructor s = TocType (MType s)
                         | TocConstructor [MType s] (MType s)

-- When it's not used in a pattern, a constructor has a type just like
-- any other binding. A no-argument constructor has a data type;
-- constructors with arguments have a function type.
tocToType (TocType t) = t
tocToType (TocConstructor args rtype) = foldr MTFun rtype args

typeOf (VInteger _) = MTInt
typeOf (VString _) = MTString


-- ## Type environments
--
-- A type environment is everything you know so far about the types in a program.
--
-- Actually, in my program, the `TypeEnv` is two pieces of mutable state that
-- we carry around through the whole algorithm: the types of all bindings
-- currently in scope; and the accumulated type errors we've found so far.
--
-- There's more mutation here than I would like, but once you go down the road
-- of writing a Python program in Haskell, it's hard to know when to apply the
-- brakes. :-\

data TypeEnv s = TypeEnv {
  envScopes :: STRef s [[(String, TypeOrConstructor s)]],
  envErrors :: STRef s [String]
}

-- Create an empty type environment. Initially it doesn't even have a global
-- scope, so before creating any global variables you'll have to use
-- `pushScope` to create one.
newTypeEnv :: ST s (TypeEnv s)
newTypeEnv = do
  scopes <- newSTRef []
  errors <- newSTRef []
  return $ TypeEnv { envScopes = scopes,
                     envErrors = errors }

-- Look up a name. The result is a `Maybe TypeOrConstructor`: a `TocType` if
-- the name is a binding, a `TocConstructor` if it's a constructor, and
-- `Nothing` if the name is undefined.
lookupToc :: TypeEnv s -> String -> ST s (Maybe (TypeOrConstructor s))
lookupToc env name = do
  scopes <- readSTRef (envScopes env)
  return $ multiLookup name scopes

-- Helper function for lookupToc: look up a key in a list of alists.
multiLookup _ [] = Nothing
multiLookup key (alist:etc) = case lookup key alist of
  Nothing -> multiLookup key etc
  Just v -> Just v

-- Lookup the type of a name. Like `lookupToc`, but if the name happens to be a
-- constructor, we just return the type of that constructor.
lookupType :: TypeEnv s -> String -> ST s (Maybe (MType s))
lookupType env name = do
  result <- lookupToc env name
  return $ case result of
    Nothing -> Nothing
    Just toc -> Just (tocToType toc)

lookupConstructorTypes :: TypeEnv s -> Location -> String -> ST s (Maybe ([MType s], MType s))
lookupConstructorTypes env loc name = do
  mtoc <- lookupToc env name
  return $ case mtoc of
    Nothing -> Nothing
    Just (TocType _) -> Nothing
    Just (TocConstructor argTypes rtype) -> Just (argTypes, rtype)

-- Add a scope to the environment, nested inside all other scopes.
pushScope :: TypeEnv s -> ST s ()
pushScope env =
  modifySTRef (envScopes env) ([] :)

-- Remove the innermost scope from the environment.
popScope :: TypeEnv s -> ST s ()
popScope env =
  modifySTRef (envScopes env) tail

-- Add a binding to the innermost scope.
bind :: TypeEnv s -> Location -> String -> MType s -> ST s ()
bind env loc name bindingType = do
  (scope : outer) <- readSTRef (envScopes env)
  case lookup name scope of
    Nothing -> return ()
    Just _ -> reportError env loc ("conflicting definitions for '" ++ name ++ "'")
  let scope' = (name, TocType bindingType) : scope
  writeSTRef (envScopes env) (scope' : outer)

-- Create a new type variable, initially unassigned.
newTypeVariable :: TypeEnv s -> Location -> ST s (MType s)
newTypeVariable env loc = do
  r <- newSTRef Nothing
  return $ MTVar r

-- Add an error the the environment's list of errors.
reportError :: TypeEnv s -> Location -> String -> ST s ()
reportError env loc message =
  modifySTRef (envErrors env) (message :)


-- ## Type unification
--
-- The main trick in type inference is called *unification*, and it's used to
-- cross-check and combine pieces of information figured out while examining
-- different parts of the program.
--
-- At every node in the tree, we can compute an *actual type*, which is
-- everything we can guess from looking at that subtree only, and an *expected
-- type*, which is everything we can guess from looking at the rest of the tree
-- (the context only). Unification simply takes these two partially-figured-out
-- types and (a) checks that they agree; (b) refines each type with information
-- that only the other had before.
--
-- For example, in the expression `sum (map (\f -> f 0) fns)`,
-- suppose we're looking at the lambda.
--
-- *   The actual type of `\f -> f 0` is something like `(Int -> ?1) -> ?1`.
--     Without peeking at the context, we can't guess the return type.
--
-- *   The expected type is what we'd guess by looking only at `sum (map ___ fns)`.
--     This depends on the types of `sum`, `map`, and `fns`. Suppose we know `sum`
--     adds up a list of `Int`s, and `map` is the usual, but we don't yet know `fns`.
--     The type we would infer here is `?2 -> Int`.
--
-- All of this is input to the unification algorithm.
--
-- In this case, unification will succeed, because the two types are compatible,
-- and it will fill in the type variables: `?1` is `Int`, and `?2` is `(Int -> Int)`.
--
-- Unification turns out to be about half of type inference, and yet it's
-- easy to read and understand. I'll leave the rest of the explaining to the code:

unify :: TypeEnv s -> Location -> MType s -> MType s -> ST s ()
unify env loc expectedType actualType = do
  e <- unwrap expectedType
  a <- unwrap actualType
  case (e, a) of
    -- If either the "expected" or the "actual" type is an empty type variable,
    -- populate it with whatever we discovered on the other side.  (The
    -- `writeSTRef` call below is what an assignment to a mutable variable
    -- looks like in Haskell.)
    --
    -- For example, maybe "expected" is empty because we had no context clues
    -- that told us what to expect here, but the actual type is Int. Great!
    -- Then that type variable must be `Int`; populate it.
    --
    -- Or maybe both "expected" and "actual" are empty type variables. In that
    -- case, the assignment changes one type variable to point at the other,
    -- storing the discovery that the the two variables must be the same type.
    (MTVar v1, _) -> writeSTRef v1 (Just a)
    (_, MTVar v2) -> writeSTRef v2 (Just e)

    -- If the expected type and the actual type are identical, we're in great shape!
    -- There's nothing to do.
    (MTInt, MTInt) -> return ()
    (MTString, MTString) -> return ()

    -- To unify two function types, simply unify the argument types and the return types.
    (MTFun a1 r1, MTFun a2 r2) -> do
      unify env loc a1 a2
      unify env loc r1 r2

    -- In our type system, everything else is an error.
    (_, _) -> do
      estr <- formatType e
      astr <- formatType a
      reportError env loc ("mismatched types (expected " ++ estr ++ ", got " ++ astr ++ ")")



-- ## Type inference

inferExprType :: TypeEnv s -> Expr -> MType s -> ST s ()

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
  unify env loc (MTFun argType bodyType) expectedType

inferExprType env (Expr _ (Call fn arg)) expectedType = do
  argType <- newTypeVariable env (exprLocation arg)
  inferExprType env fn (MTFun argType expectedType)
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
inferPatternType :: TypeEnv s -> Pattern -> MType s -> ST s ()

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
  bind env ((1, 0), (1, 0)) "parse" (MTFun MTString MTInt)
  t <- newTypeVariable env ((1, 0), (1, 11))
  inferExprType env expr t
  popScope env
  errors <- readSTRef (envErrors env)
  if errors /= []
    then return $ Left errors
    else do t' <- toType t
            case t' of
              Nothing -> return $ Left ["unresolved type variable"]
              Just t'' -> return $ Right t''

assertInfersType s t =
  case fullParseExpr s of
    Left err -> putStrLn (show err)
    Right expr ->
      case infer expr of
        Left errors -> mapM_ putStrLn errors
        Right answer ->
          if answer == t
          then return ()
          else putStrLn $ "test failed: inferred type was " ++ show answer ++ ", expected " ++ show t

test1 = assertInfersType "parse \"123\"" TInt

test2 = assertInfersType "\\x -> parse x" (TFun TString TInt)

main = do
  runParserTests
  test1
  test2
  interact1

interact1 = do
  putStr "infer> "
  hFlush stdout
  line <- getLine
  case fullParseExpr line of
    Left err -> putStrLn (show err)
    Right expr ->
      case infer expr of
        Left errors -> mapM_ putStrLn errors
        Right answer -> putStrLn $ show answer
  interact1
