{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

-- | Shows how to do typechecking of an expression language
-- with GADTs.
module TypedLanguageGADTs where

import qualified Data.Kind
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Typeable (Typeable, cast)


-- | Expressions with variables named with a type @a@.
data Expr a t where
  Var :: Typeable t => Type t -> a -> Expr a t
  Lit :: Literal t -> Expr a t
  Plus :: Expr a Int -> Expr a Int -> Expr a Int
  And :: Expr a Bool -> Expr a Bool -> Expr a Bool

data Literal t where
  LitBool :: Bool -> Literal Bool
  LitInt :: Int -> Literal Int

-- | Types of expressions
data Type t where
  TypeBool :: Type Bool
  TypeInt :: Type Int

deriving instance Eq (Type t)
deriving instance Show (Type t)

-- | Infers the type of an expression.
exprType :: Expr a t -> Type t
exprType (Var t a) = t
exprType (Lit l) = litType l
exprType Plus{} = TypeInt
exprType And{} = TypeBool

-- | Infers the type of a literal.
litType :: Literal t -> Type t
litType LitBool{} = TypeBool
litType LitInt{} = TypeInt

data Some f where
  Some :: Typeable a => f a -> Some f

-- | Evaluates an expression.
eval :: Ord a => Map a (Some Literal) -> Expr a t -> Literal t
eval env (Var t a) = envLookup t a env
eval env (Lit l) = l
eval env (Plus a b) = plusLits (eval env a) (eval env b)
eval env (And a b) = andLits (eval env a) (eval env b)

plusLits :: Literal Int -> Literal Int -> Literal Int
plusLits (LitInt a) (LitInt b) = LitInt (a + b)

andLits :: Literal Bool -> Literal Bool -> Literal Bool
andLits (LitBool a) (LitBool b) = LitBool (a && b)

test = eval (Map.singleton 0 (Some (LitBool True))) (Var TypeBool 0)

-- | envLookup is a wrapper over Map.lookup that assures
-- that the type of the returned literal is the expected one.
--
-- It throws an error if the types don't match, or if the name
-- is missing.
--
envLookup
  :: (Typeable t, Ord k) => Type t -> k -> Map k (Some Literal) -> Literal t
envLookup t k = maybe (error "envLookup failed") checkLiteral . Map.lookup k
  where
    checkLiteral (Some lit) = case cast lit of
      Nothing -> error "envLookup mismatched type"
      Just checkedLit -> checkedLit

-- | Takes two lists of expressions of equal lenght and types, and
-- combines them into a final list.
combineExprs :: HList (Expr a) xs -> HList (Expr a) xs -> HList (Expr a) xs
combineExprs = hzipWith combine
  where
    combine :: Expr a t -> Expr a t -> Expr a t
    combine e0 e1 = case exprType e0 of
      TypeBool -> And e0 e1
      TypeInt -> Plus e0 e1

data HList f (xs :: [Data.Kind.Type]) where
  HNil :: HList f '[]
  HCons :: f x -> HList f xs -> HList f (x ': xs)

-- | A wrapper over 'zipWith' that ensures that if the corresponding
-- expressions have matching types, then the output list will have
-- matching types.
hzipWith
  :: (forall t. f t -> f t -> f t)
  -> HList f xs
  -> HList f xs
  -> HList f xs
hzipWith f HNil HNil = HNil
hzipWith f (HCons x xs) (HCons y ys) = HCons (f x y) (hzipWith f xs ys)

hmapUntyped :: (forall t. f t -> c) -> HList f xs -> [c]
hmapUntyped f HNil = []
hmapUntyped f (HCons x xs) = f x : hmapUntyped f xs

showHList :: (forall a. Show (f a)) => HList f xs -> String
showHList = show . hmapUntyped show
