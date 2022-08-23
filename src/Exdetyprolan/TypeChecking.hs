{-# LANGUAGE RankNTypes #-}
module Exdetyprolan.TypeChecking where

import Bound
import Control.Comonad
import Control.Comonad.Cofree
import Control.Lens
import Debug.Trace

import Exdetyprolan.Expression
import Exdetyprolan.Normalization

--------------------------------------------------------------------------------
-- Typechecking of expressions
--------------------------------------------------------------------------------

-- if input is well-typed, so is output
-- type of successful output is always Set :$ something
-- output is not necessarily normalized

-- | Given a normalization function for free variables, and a way to determine
-- a free variable's type, determine the type of an expression.
--
-- The type of an expression, if it exists, will always be well-typed, the type
-- of an expression's type will always be of the form 'Set :$ l' for some l.
--
-- The output of this function will not in general be normalized.
findType :: (Show a, Eq a) => (forall b. Prism' b a -> a -> Cofree ((->) (Exp b)) (Exp b)) -> (a -> Either String (Exp a)) -> Exp a -> Either String (Exp a)
findType _ resolve (V a) = resolve a
findType norm resolve (f :$ a) = do
  ft <- findType norm resolve f
  case ft of
    Fun et rt -> do
      at <- findType norm resolve a
      if extract (normalize norm et) == extract (normalize norm at)
      then pure $ instantiate1 a rt
      else Left $ "Types don't match: " ++ show et ++ ", " ++ show at
    _ -> Left "Expected function"
findType norm resolve (Fun e (Scope r)) = do
  et <- findType norm resolve e
  case et of
    Set :$ el -> do
      rt <- findType (extendNorm norm) resolve' r
      case rt of
        Set :$ rl -> case traverse explore rl of
          Nothing  -> pure $ Set :$ OmegaL
          Just rl' -> pure $ Set :$ (UnionL :$ el :$ rl')
        _ -> Left "Return type of a function must be a set"
    _ -> Left "Argument type of a function must be a set"
  where
    resolve' (B ()) = pure $ fmap (F . V) e
    resolve' (F a) = fmap (fmap (F . V)) $ findType norm resolve a
    explore (B ()) = Nothing
    explore (F (V a)) = Just a
    explore (F _) = error "findType.explore: can this be reached?" -- not convinced this case is correct or if it can happen
findType norm resolve (Lam e (Scope r)) = do
  rt <- findType (extendNorm norm) resolve' r
  pure $ Fun e (Scope rt)
  where
    resolve' (B ()) = pure $ fmap (F . V) e
    resolve' (F a) = fmap (fmap (F . V)) $ findType norm resolve a
findType _ _ Set = pure (Fun Level (Scope (Set :$ (SuccL :$ V (B ())))))
findType _ _ Level = pure (Set :$ ZeroL)
findType _ _ ZeroL = pure Level
findType _ _ SuccL = pure (Fun Level (Scope Level))
findType _ _ UnionL = pure (Fun Level (Scope (Fun Level (Scope Level))))
findType _ _ OmegaL = pure Level

emptyScope :: a -> Either String (Exp a)
emptyScope _ = Left "Unbound variable"

-- an example expression: polymorphic identity function forall. (l : Level) (A : Set l) -> A -> A
idFunction :: Exp a
idFunction = Lam Level $ Scope $ Lam (Set :$ V (B ())) $ Scope $ Lam (V (B ())) $ Scope $ V (B ())
