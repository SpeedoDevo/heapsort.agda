module NatExt where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Ord

-- extend the natural numbers with infinity
postulate ∞ : Nat
postulate _≤∞ : (n : Nat) -> n ≤ ∞

infGteInf : (n : Nat) -> ∞ ≤ n -> ∞ ≡ n
infGteInf n p = ordToEq ∞ n p (n ≤∞)
