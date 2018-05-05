module Ord where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data _≤_ : Nat → Nat → Set where
  zero≤ : (y : Nat) → zero ≤ y
  suc≤suc : (x y : Nat) → x ≤ y → suc x ≤ suc y

data Ord (x y : Nat) : Set where
  lte : x ≤ y -> Ord x y
  gte : y ≤ x -> Ord x y

ord : (x y : Nat) -> Ord x y
ord zero y = lte (zero≤ y)
ord (suc x) zero = gte (zero≤ (suc x))
ord (suc x) (suc y) with ord x y
... | lte xy = lte (suc≤suc x y xy)
... | gte yx = gte (suc≤suc y x yx)

x≤x : (x : Nat) -> x ≤ x
x≤x zero = zero≤ zero
x≤x (suc x) = suc≤suc x x (x≤x x)

ordToEq : (x y : Nat) -> x ≤ y -> y ≤ x -> x ≡ y
ordToEq .0 .0 (zero≤ .0) (zero≤ .0) = refl
ordToEq .(suc x) .(suc y) (suc≤suc x y p) (suc≤suc .y .x q) rewrite ordToEq x y p q = refl

eqToOrd : (x y : Nat) -> x ≡ y -> x ≤ y
eqToOrd x .x refl = x≤x x


-- value rr ≡ value (mergeT lt rr) -> Item.value .ri ≤ value (mergeT lt rr) -> Item.value .ri ≤ value rr
substitution : ∀ {a b c} -> b ≡ a -> c ≤ b -> c ≤ a
substitution refl q = q
