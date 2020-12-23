{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Shows how to do typechecking of an expression language
-- with Liquid Haskell.
module TypedLanguageLH where

import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map


-- | Expressions with variables named with a type @a@.
data Expr a
  = Var Type a   -- A variable has a type and a name
  | Lit Literal  -- Constants
  | Plus (Expr a) (Expr a) -- Adds two expressions
  | And (Expr a) (Expr a)  -- Logical and of two expressions
  deriving Show

data Literal
  = LitBool Bool
  | LitInt Int
  deriving Show

-- | Types of expressions
data Type = TypeBool | TypeInt
  deriving (Eq, Show)

-- GHC doesn't keep track of the type of expressions,
-- we use Liquid Haskell for that purpose, in order
-- to keep the implementation straight forward.
{-@
  type ExprOf a T = { x : Expr a | exprType x = T }

  data Expr a
    = Var Type a
    | Lit Literal
    | Plus (ExprOf a TypeInt) (ExprOf a TypeInt)
    | And (ExprOf a TypeBool) (ExprOf a TypeBool)
 @-}

-- | Infers the type of an expression.
--
-- It doesn't ensure that the expression is well-typed, since
-- LiquidHaskell is supposed to do that.
{-@ measure exprType @-}
exprType :: Expr a -> Type
exprType (Var t a) = t
exprType (Lit l) = litType l
exprType Plus{} = TypeInt
exprType And{} = TypeBool

-- | Infers the type of a literal.
{-@ measure litType @-}
litType :: Literal -> Type
litType LitBool{} = TypeBool
litType LitInt{} = TypeInt

-- | Infers the type of a list of expressions.
{-@ measure exprTypes @-}
exprTypes :: [Expr a] -> [Type]
exprTypes [] = []
exprTypes (x:xs) = exprType x : exprTypes xs

-- | Evaluates an expression.
--
-- Liquid Haskell ensures that the type of the returned literal
-- mathes the type of the input expression.
--
-- No effort is done to ensure that the variables are present in
-- the environment, or that they have the right types.
--
{-@ eval :: Ord a => Map a Literal -> e : Expr a -> LiteralOf (exprType e) @-}
eval :: Ord a => Map a Literal -> Expr a -> Literal
eval env (Var t a) = envLookup t a env
eval env (Lit l) = l
eval env (Plus a b) = plusLits (eval env a) (eval env b)
eval env (And a b) = andLits (eval env a) (eval env b)

{-@ type LiteralOf T = { x : Literal | litType x = T } @-}

{-@ plusLits :: LiteralOf TypeInt -> LiteralOf TypeInt -> LiteralOf TypeInt @-}
plusLits :: Literal -> Literal -> Literal
plusLits (LitInt a) (LitInt b) = LitInt (a + b)

{-@ andLits :: LiteralOf TypeBool -> LiteralOf TypeBool -> LiteralOf TypeBool @-}
andLits :: Literal -> Literal -> Literal
andLits (LitBool a) (LitBool b) = LitBool (a && b)

test = eval (Map.singleton 0 (LitBool True)) (Var TypeBool 0)

-- | envLookup is a wrapper over Map.lookup that assures to
-- Liquid Haskell that the type of the returned literal is the
-- expected one.
--
-- It throws an error if the types don't match, or if the name
-- is missing.
--
{-@ ignore envLookup
    assume envLookup
      :: t : Type
      -> k
      -> Map k Literal
      -> { z : Literal | t = litType z }
  @-}
envLookup :: Ord k => Type -> k -> Map k Literal -> Literal
envLookup t k = maybe (error "envLookup failed") checkLiteral . Map.lookup k
  where
    checkLiteral lit =
      if t == litType lit then lit else error "envLookup mismatched type"


-- | Takes two lists of expressions of equal lenght and types, and
-- combines them into a final list.
--
-- This is an example of a function that would require DataKinds
-- and heterogenous lists to be expressed in traditional
-- type-level programming.
--
{-@ combineExprs
      :: xs : [Expr a]
      -> { ys : [Expr a] | exprTypes ys = exprTypes xs }
      -> { zs : [Expr a] | exprTypes ys = exprTypes zs }
  @-}
combineExprs :: [Expr a] -> [Expr a] -> [Expr a]
combineExprs = zipWithCombine combine
  where
    combine e0 e1 = case exprType e0 of
      TypeBool -> And e0 e1
      TypeInt -> Plus e0 e1

-- | A wrapper over 'zipWith' that ensures that if the corresponding
-- expressions have matching types, then the output list will have
-- matching types.
{-@ ignore zipWithCombine
    assume zipWithCombine
      :: (x : Expr a
          -> { y : Expr a | exprType x = exprType y }
          -> { z : Expr a | exprType z = exprType y }
         )
      -> xs : [Expr a]
      -> { ys : [Expr a] | exprTypes ys = exprTypes xs }
      -> { zs : [Expr a] | exprTypes ys = exprTypes zs }
  @-}
zipWithCombine
  :: (Expr a -> Expr a -> Expr a) -> [Expr a] -> [Expr a] -> [Expr a]
zipWithCombine = zipWith
