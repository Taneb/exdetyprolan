{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
module Exdetyprolan.Normalization where

import Bound
import Bound.Var
import Control.Lens hiding ((:<))
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad
import Data.Distributive
import Data.Void

import Exdetyprolan.Expression

--------------------------------------------------------------------------------
-- Normalization of expressions
--------------------------------------------------------------------------------

type Mealy a b = Cofree ((->) a) b

-- Carries both the normalized form of an expression, and recipes for keeping
-- it normalized as more variables are applied. This lets us normalize
-- applications of functions (both primitive functions given to us as free
-- variables and lambdas).
type Normalization a = Mealy (Exp a) (Exp a)

-- A recipe for normalizing a free variable, even in bound contexts.
-- Given a way to extract the expected variable type from the actual variable
-- type, and a way to put them back, in the form of a Prism, compute the
-- normalization of the variable.
type VariableNormalization a = forall b. Prism' b a -> a -> Normalization b

-- | Compute a normal form of an expression.
-- The normal form is returned in a 'Cofree' structure with subsequent
-- unwrappings applying arguments to the expression. This allows for easier
-- definitions of normal forms of function-like expressions, such as
-- constructors and induction principles.
--
-- The first argument is a way of calculating normal forms of free variables.
--
-- The normal form of an ill-typed expression is undefined.
--
-- This function should obey the following law:
--
-- @
--   normalize norm . extract . normalize norm === normalize norm
-- @
--
-- Maybe this should use Cofree (Compose Maybe ((->) (Exp b)))?
normalize :: VariableNormalization a -> Exp a -> Normalization a
normalize norm (V a) = norm id a
normalize norm (f :$ a) = unwrap (normalize norm f) $ extract (normalize norm a)
normalize norm (Fun e (Scope r)) = Fun e' (Scope r') :< error "Too many arguments applied to Fun"
  where
    e' :< _ = normalize norm e
    r' :< _ = normalize (extendNorm norm) r
normalize norm (Lam e (Scope r)) = Lam e' (Scope r') :< \a -> normalize norm (instantiate1 a (Scope r))
  where
    e' :< _ = normalize norm e
    r' :< _ = normalize (extendNorm norm) r
normalize _ Set = Set :< \l -> (Set :$ l) :< error "Too many arguments applied to Set"
normalize _ Level = Level :< error "Too many arguments applied to Level"
normalize _ ZeroL = ZeroL :< error "Too many arguments applied to ZeroL"
normalize _ SuccL = SuccL :< \l -> (SuccL :$ l) :< error "Too many arguments applied to SuccL"
normalize norm UnionL = UnionL :< \l1 -> (UnionL :$ l1) :< \l2 -> case (l1, l2) of
  (ZeroL, _) -> l2 :< error "Too many arguments applied to UnionL 1"
  (_, ZeroL) -> l1 :< error "Too many arguments applied to UnionL 2"
  (SuccL :$ l1', SuccL :$ l2') -> fmap (SuccL :$) $ normalize norm (UnionL :$ l1' :$ l2')
  _ -> (UnionL :$ l1 :$ l2) :< error "Too many arguments applied to UnionL 3"
normalize _ OmegaL = OmegaL :< error "Too many arguments applied to OmegaL"

-- | Extend a normalization of free variables by a single bound variable.
-- Bound variables cannot be normalized further.
extendNorm :: VariableNormalization a -> VariableNormalization (Var () (Exp a))
extendNorm _ p (B ()) = coiter (:$) (V (p # B ()))
-- This case is WRONG! It does weird things with lambdas, and the fact it's using Cofree's distributive instance is weird
extendNorm norm p (F a) = fmap join (collect (norm (p . _F . _V)) a)

voidNorm :: VariableNormalization Void
voidNorm _ = absurd

eitherNorm :: VariableNormalization a -> VariableNormalization b -> VariableNormalization (Either a b)
eitherNorm l r p (Left a) = l (p . _Left) a
eitherNorm l r p (Right b) = r (p . _Right) b
