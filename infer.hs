import Control.Monad.ST
import Data.STRef

------------------------------------------------------------------------

-- A type is either Int, String, (a -> b) where a and b are two types,
-- or a type variable.
--
-- Type variables are the interesting bit. Each one contains a mutable cell so
-- that the variable can be *unified* with another type during type inference.
--
--     TVar (newSTRef Nothing) is an unknown type.
--
--     TVar (newSTRef (Just TInt)) is the type Int - this is an initially
--     unknown type that we later inferred.
--
--     TVar (newSTRef (Just v)), where v is also a TVar, is a type that has
--     been unified with another type variable. v might already be known, or it
--     may still be unknown; but we do know that this type and v are the same.
--     
data Type s = TInt
            | TString
            | TFun (Type s) (Type s)
            | TVar (STRef s (Maybe (Type s)))
            deriving Eq

formatType :: Type s -> ST s String
formatType TInt = return "Int"
formatType TString = return "String"
formatType (TFun a r) = do
  astr <- formatType a
  rstr <- formatType r
  return $ "(" ++ astr ++ " -> " ++ rstr ++ ")"
formatType v = do
  u <- unwrap v
  case u of
    TVar _ -> return "_"
    other -> formatType other

unwrap :: Type s -> ST s (Type s)
unwrap (TVar v) = do
  t <- readSTRef v
  case t of
    Nothing -> return $ TVar v
    Just u -> do
      u' <- unwrap u
      writeSTRef v (Just u')
      return u'
unwrap other = return other

-- A constructor, like Just or Nothing or True or False,
-- is a little different from other bindings.
-- It can be used in case-expressions. We have to know the type of each field.
--
-- (An alternative here would be `data TypeOrConstructor s = TypeOrConstructor {
-- type :: Type s, isConstructor :: Bool }`, but then case expressions would have
-- to figure out the field types from the constructor type.)

data TypeOrConstructor s = TocType (Type s) 
                         | TocConstructor [Type s] (Type s)

-- When it's not used in a pattern, a constructor has a type just like
-- any other binding. A no-argument constructor has a data type;
-- constructors with arguments have a function type.
toType (TocType t) = t
toType (TocConstructor args rtype) = foldr TFun rtype args

-- Values that can be represented as literals in programs.
data Value = VInt Int | VString String

typeOf (VInt _) = TInt
typeOf (VString _) = TString

-- Expressions.
data Expr_ = Name String
           | Literal Value
           | Lambda Location String Expr
           | Call Expr Expr
           | Case Expr [(Pattern, Expr)]

type Location = (Int, Int)

data Expr = Expr Location Expr_

exprLocation (Expr loc _) = loc

-- Patterns (used in case expressions)
data Pattern_ = PWildcard
              | PLiteral Value
              | PVar String
              | PConstructor Location String [Pattern]

data Pattern = Pattern Location Pattern_

patternLocation (Pattern loc _) = loc

------------------------------------------------------------------------

infer :: TypeEnv s -> Expr -> Type s -> ST s ()

infer env (Expr loc (Name s)) expectedType = do
  result <- lookupType env s
  case result of
    Nothing -> reportError env loc ("undefined variable `" ++ s ++ "`")
    Just actualType -> unify env loc expectedType actualType

infer env (Expr loc (Literal v)) expectedType =
  unify env loc expectedType (typeOf v)

infer env (Expr loc (Lambda argLocation arg body)) expectedType = do
  pushScope env
  argType <- newTypeVariable env argLocation
  bodyType <- newTypeVariable env (exprLocation body)
  bind env argLocation arg argType
  infer env body bodyType
  popScope env
  unify env loc (TFun argType bodyType) expectedType

infer env (Expr _ (Call fn arg)) expectedType = do
  argType <- newTypeVariable env (exprLocation arg)
  infer env fn (TFun argType expectedType)
  infer env arg argType

infer env (Expr _ (Case d cases)) expectedType = do
  dType <- newTypeVariable env (exprLocation d)
  infer env d dType
  let inferCase (pattern, result) = do
        pushScope env
        inferPattern env pattern dType
        infer env result expectedType
        popScope env
  sequence_ $ map inferCase cases

-- Patterns, too, have types which must be inferred.
-- They can also have sub-patterns whose types must be inferred recursively.
inferPattern :: TypeEnv s -> Pattern -> Type s -> ST s ()

inferPattern env (Pattern _ PWildcard) expectedType = return ()

inferPattern env (Pattern loc (PLiteral value)) expectedType =
  unify env loc (typeOf value) expectedType

inferPattern env (Pattern loc (PVar name)) expectedType =
  bind env loc name expectedType

inferPattern env (Pattern loc (PConstructor nameLocation name argPatterns)) expectedType = do
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
                   inferPattern env pattern expectedType
             in sequence_ $ map inferArgPattern (zip argPatterns argTypes)

------------------------------------------------------------------------

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

lookupType :: TypeEnv s -> String -> ST s (Maybe (Type s))
lookupType env name = do
  result <- lookupToc env name
  return $ case result of
    Nothing -> Nothing
    Just toc -> Just (toType toc)

lookupConstructorTypes :: TypeEnv s -> Location -> String -> ST s (Maybe ([Type s], Type s))
lookupConstructorTypes env loc name = do
  mtoc <- lookupToc env name
  return $ case mtoc of
    Nothing -> Nothing
    Just (TocType _) -> Nothing
    Just (TocConstructor argTypes rtype) -> Just (argTypes, rtype)

unify :: TypeEnv s -> Location -> Type s -> Type s -> ST s ()
unify env loc expectedType actualType = do
  e <- unwrap expectedType
  a <- unwrap actualType
  case (e, a) of
    (TVar v1, _) -> writeSTRef v1 (Just a)
    (_, TVar v2) -> writeSTRef v2 (Just e)
    (TInt, TInt) -> return ()
    (TString, TString) -> return ()
    (TFun a1 r1, TFun a2 r2) -> do
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

bind :: TypeEnv s -> Location -> String -> Type s -> ST s ()
bind env loc name bindingType = do
  (scope : outer) <- readSTRef (envScopes env)
  case lookup name scope of
    Nothing -> return ()
    Just _ -> reportError env loc ("conflicting definitions for '" ++ name ++ "'")
  let scope' = (name, TocType bindingType) : scope
  writeSTRef (envScopes env) (scope' : outer)

newTypeVariable :: TypeEnv s -> Location -> ST s (Type s)
newTypeVariable env loc = do
  r <- newSTRef Nothing
  return $ TVar r

reportError :: TypeEnv s -> Location -> String -> ST s ()
reportError env loc message =
  modifySTRef (envErrors env) (message :)

------------------------------------------------------------------------

test1 = runST $ do
  env <- newTypeEnv
  pushScope env
  bind env (0, 0) "parse" (TFun TString TInt)
  t <- newTypeVariable env (0, 11)
  infer env (Expr (0, 11) (Call
                           (Expr (0, 5) (Name "parse"))
                           (Expr (6, 11) (Literal (VString "123"))))) t
  popScope env
  errors <- readSTRef (envErrors env)
  t' <- unwrap t
  tstr <- formatType t'
  if errors /= []
    then return errors
    else if t' /= TInt
         then return ["test failed: inferred type was " ++ tstr ++ ", expected Int"]
         else return ["passed"]


------------------------------------------------------------------------

main = sequence_ $ map putStrLn $ test1

