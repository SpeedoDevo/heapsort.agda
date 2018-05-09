module Tree where

open import Agda.Builtin.Nat

data Tree : (A : Set) -> Set where
  leaf : ∀ {A} -> Tree A
  branch : ∀ {A} -> (l : Tree A) -> (e : A) -> (r : Tree A) -> Tree A

⊥ : ∀ {A} -> Tree A
⊥ = leaf

singletonTree : Nat -> Tree Nat
singletonTree n = branch ⊥ n ⊥
