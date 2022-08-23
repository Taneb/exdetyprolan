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

import Exdetyprolan.Expression

--------------------------------------------------------------------------------
-- Normalization of expressions
--------------------------------------------------------------------------------

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
normalize :: (forall b. Prism' b a -> a -> Cofree ((->) (Exp b)) (Exp b)) -> Exp a -> Cofree ((->) (Exp a)) (Exp a)
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
extendNorm :: (forall b. Prism' b a -> a -> Cofree ((->) (Exp b)) (Exp b)) -> Prism' b (Var () (Exp a)) -> Var () (Exp a) -> Cofree ((->) (Exp b)) (Exp b)
extendNorm _ p (B ()) = coiter (:$) (V (p # B ()))
-- This line is WRONG! It does weird things with lambdas, and the fact it's using Cofree's distributive instance is weird
extendNorm norm p (F a) = fmap join (collect (norm (p . _F . _V)) a)

-- Trivial normalization of no free variables
emptyNorm :: a -> Cofree ((->) (Exp a)) (Exp a)
emptyNorm _ = error "Unbound variable"
