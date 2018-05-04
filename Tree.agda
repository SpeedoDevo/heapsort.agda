module Tree where

open import Agda.Builtin.Nat
open import Agda.Builtin.Size

data Tree : {i : Size} (A : Set) -> Set where
  leaf : ∀ {A} -> {i : Size} -> Tree {↑ i} A
  branch : ∀ {A} -> {i : Size} -> (l : Tree {i} A) -> (e : A) -> (r : Tree {i} A) -> Tree {↑ i} A

⊥ : ∀ {A} -> Tree A
⊥ = leaf

singleton : Nat -> Tree Nat
singleton n = branch ⊥ n ⊥
