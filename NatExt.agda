module NatExt where

open import Agda.Builtin.Nat
open import Ord

postulate ∞ : Nat
postulate _≤∞ : (n : Nat) -> n ≤ ∞
