module Ord where
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data _≤_ : Nat → Nat → Set where
  zero≤ : (y : Nat) → zero ≤ y
  suc≤suc : (x y : Nat) → x ≤ y → suc x ≤ suc y

-- _≤?_ : Nat → Nat → Bool
-- zero ≤? y = true
-- suc x ≤? zero = false
-- suc x ≤? suc y = x ≤? y
--
-- data Total≤ (x y : Nat) : Set where
--   x≤y : x ≤ y → Total≤ x y
--   y≤x : y ≤ x → Total≤ x y
--
-- totality : (x y : Nat) → Total≤ x y
-- totality zero y = x≤y (zero≤ y)
-- totality (suc x) zero = y≤x (zero≤ (suc x))
-- totality (suc x) (suc y) with totality x y
-- totality (suc x) (suc y) | x≤y p = x≤y (suc≤suc x y p)
-- totality (suc x) (suc y) | y≤x p = y≤x (suc≤suc y x p)

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
