
module TypedLanguageLH2 where

import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map


data Expr a
  = Var Type a
  | Lit Literal
  | Plus (Expr a) (Expr a)
  | And (Expr a) (Expr a)

data Literal
  = LitBool Bool
  | LitInt Int

data Type = TypeBool | TypeInt

{-@
  type Typed e a T = { x : e a | exprType x = T }

  data Expr a <p :: Type -> a -> Bool>
    = Var (t :: Type) a<p t>
    | Lit Literal
    | Plus (Typed Expr<p> a TypeInt) (Typed Expr<p> a TypeInt)
    | And (Typed Expr<p> a TypeBool) (Typed Expr <p> a TypeBool)
 @-}

{-@ measure exprType @-}
exprType :: Expr a -> Type
exprType (Var t a) = t
exprType (Lit l) = litType l
exprType Plus{} = TypeInt
exprType And{} = TypeBool

{-@ measure litType @-}
litType :: Literal -> Type
litType LitBool{} = TypeBool
litType LitInt{} = TypeInt

{-@ measure exprTypes @-}
exprTypes :: [Expr a] -> [Type]
exprTypes [] = []
exprTypes (x:xs) = exprType x : exprTypes xs

{-@ type ExprClosed a E = Expr<{\t v -> litType (mapLookup v E) = t }> a @-}

{-@ eval
      :: Ord a
      => env : Map a Literal
      -> e : ExprClosed a env
      -> LiteralOf (exprType e) @-}
eval :: Ord a => Map a Literal -> Expr a -> Literal
eval env e@(Var t a) = env Map.! a
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

{-@ assume Map.! :: m : Map k v -> x : k -> { z:v | mapLookup x m = z }
    assume Map.singleton :: x : k -> y : v -> { m : Map k v | mapLookup x m = y }
  @-}

{-@ reflect mapLookup @-}
mapLookup :: k -> Map k v -> v
mapLookup = mapLookup
