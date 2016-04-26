module Expr(Expr_(..), SourcePoint, Location, Expr(..), exprLocation,
            Value(..),
            Pattern_(..), Pattern(..), patternLocation)
where

-- ## Expressions
--
-- We need a way to represent programs in memory, and that's the `Expr` type.
-- The way this is defined is a little wonky, because I want to be able to
-- store location information alongside every node.

data Expr_ e = Name String
           | Literal Value
           | Lambda Location String e
           | Call e e
           | Case e [(Pattern, e)]
  deriving (Eq, Show)

type SourcePoint = (Int, Int)  -- line and column
type Location = (SourcePoint, SourcePoint)  -- start and end

data Expr = Expr Location (Expr_ Expr)
  deriving (Eq, Show)

-- Find out where an expression appeared within the program.
exprLocation (Expr loc _) = loc

-- A few values can be represented as literals in programs.
data Value = VInteger Integer | VString String
  deriving (Eq, Show)

-- Case expressions contain *patterns,* so we'll need a definition for that:
data Pattern_ = PWildcard
              | PLiteral Value
              | PVar String
              | PConstructor Location String [Pattern]
  deriving (Eq, Show)

data Pattern = Pattern Location Pattern_
  deriving (Eq, Show)

patternLocation (Pattern loc _) = loc
