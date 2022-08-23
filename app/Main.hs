{-# LANGUAGE RankNTypes #-}
module Main where

import Bound
import Control.Comonad
import Control.Comonad.Cofree
import Control.Lens hiding ((:<))

import Exdetyprolan.Expression
import Exdetyprolan.Normalization
import Exdetyprolan.TypeChecking

data NatPrim
  = Nat
  | NatZero
  | NatSucc
  | NatRec
  deriving (Eq, Show)

normWithNats :: Prism' b NatPrim -> NatPrim -> Cofree ((->) (Exp b)) (Exp b)
normWithNats e Nat = V (e # Nat) :< error "Too many arguments applied to Nat"
normWithNats e NatZero = V (e # NatZero) :< error "Too many arguments applied to NatZero"
normWithNats e NatSucc = V (e # NatSucc) :< \n -> V (e # NatSucc) :$ n :< error "Too many arguments applied to NatSucc"
normWithNats e NatRec
  = V (e # NatRec)
  :< \l -> V (e # NatRec) :$ l
  :< \p -> V (e # NatRec) :$ l :$ p
  :< \z -> V (e # NatRec) :$ l :$ p :$ z
  :< \s -> V (e # NatRec) :$ l :$ p :$ z :$ s
  :< \n -> coiter (:$) $ case n of
    V v | Right NatZero <- matching e v -> V (e # NatZero)
    V v :$ n' | Right NatSucc <- matching e v -> s :$ (V (e # NatRec) :$ l :$ p :$ z :$ s :$ n')
    _ -> V (e # NatRec) :$ l :$ p :$ z :$ s :$ n

scopeWithNats :: NatPrim -> Either String (Exp NatPrim)
scopeWithNats Nat = Right (Set :$ ZeroL)
scopeWithNats NatZero = Right (V Nat)
scopeWithNats NatSucc = Right (Fun (V Nat) (Scope (V (F (V Nat)))))
scopeWithNats NatRec = Right $
  -- l : Level
  Fun Level $ Scope $
  -- P : Nat -> Set l
  Fun (Fun (V (F (V Nat))) (Scope (Set :$ V (F (V (B ())))))) $ Scope $
  -- z : P NatZero
  Fun (V (B ()) :$ V (F (V (F (V NatZero))))) $ Scope $
  -- s : (k : nat) -> P k -> P (natSucc k)
  Fun (Fun (V (F (V (F (V (F (V Nat))))))) $ Scope $ Fun (V (F (V (F (V (B ()))))) :$ V (B ())) $ Scope $ V (F (V (F (V (F (V (B ()))))))) :$ (V (F (V (F (V (F (V (F (V (F (V NatSucc)))))))))) :$ V (F (V (B ()))))) $ Scope $
  -- n : nat
  Fun (V (F (V (F (V (F (V (F (V Nat))))))))) $ Scope $
  -- P n
  V (F (V (F (V (F (V (B ()))))))) :$ V (B ())

two :: Exp NatPrim
two = V NatSucc :$ (V NatSucc :$ V NatZero)


-- plus :: Exp String
-- plus = Lam (V "nat") $ Scope $ Lam (V (F (V "nat"))) $ Scope $ 

tc :: Exp NatPrim -> Either String (Exp NatPrim)
tc = fmap (extract . normalize normWithNats) . findType normWithNats scopeWithNats
-- tc = findType normWithNats scopeWithNats

k :: Exp a
k
  = Lam Level $ Scope
    $ Lam (Set :$ V (B ())) $ Scope
    $ Lam Level $ Scope
    $ Lam (Set :$ V (B ())) $ Scope
    $ Lam (V (F (V (F (V (B ())))))) $ Scope
    $ Lam (V (F (V (B ())))) $ Scope
    $ V (B ())

main :: IO ()
main = do
  putStrLn "two"
  print $ tc two
  putStrLn "NatRec"
  print $ tc (V NatRec)
  putStrLn "NatRec 0l"
  print $ tc (V NatRec :$ ZeroL)
  putStrLn "\\_ -> nat"
  print $ tc (Lam (V Nat) (Scope (V (F (V Nat)))))
  putStrLn "const"
  print $ tc k
  putStrLn "const 0l Nat 0l Nat 0 1"
  print $ tc (k :$ ZeroL :$ V Nat :$ ZeroL :$ V Nat :$ V NatZero :$ (V NatSucc :$ V NatZero))
  putStrLn "(\\_ -> Nat) 0"
  print $ tc (Lam (V Nat) (Scope (V (F (V Nat)))) :$ V NatZero)
  putStrLn "NatRec 0l (\\_ -> Nat)"
  print $ tc (V NatRec :$ ZeroL :$ (Lam (V Nat) (Scope (V (F (V Nat))))))
