{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Exdetyprolan.Expression where

import Bound
import Control.Lens
import Data.Eq.Deriving
import Text.Show.Deriving

--------------------------------------------------------------------------------
-- The type of expressions
--------------------------------------------------------------------------------

-- | The type of expressions. Parameterized by a type of free variables, in the
-- style of the bound library. I expect this to normally be something like
-- 'String'.
data Exp a
  -- | A variable.
  = V a
  -- | Function application, function on the left, argument on the right.
  | Exp a :$ Exp a
  -- | The function *type*. Acts as a binder to allow dependent functions.
  | Fun (Exp a) (Scope () Exp a)
  -- | A lambda. Carries with it the type of its domain.
  | Lam (Exp a) (Scope () Exp a)
  -- set primitives
  -- | The type of types. Takes a Level parameter.
  | Set
  -- universe level primitives
  -- | The type of universe levels. These aren't internally inspectable,
  -- despite being fairly similar to natural numbers.
  | Level
  -- | The lowest level.
  | ZeroL
  -- | Successor function for levels. The type of Set :$ l is Set :$ (SuccL :$ l).
  | SuccL
  -- | Union (maximum) of two levels.
  | UnionL
  -- | The "ultimate" level. Used for e.g. functions whose codomain's level 
  -- depends on a level argument.
  | OmegaL
  deriving (Functor, Foldable, Traversable)

makeBound ''Exp

deriveEq1 ''Exp

deriving instance Eq a => Eq (Exp a)

deriveShow1 ''Exp

deriving instance Show a => Show (Exp a)

makePrisms ''Exp
