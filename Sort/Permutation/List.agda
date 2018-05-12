module Sort.Permutation.List where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Heap
open import Heap.HTree
open import Heap.Item
open import Ord
open import Sort.Sort
open import Sort.Permutation.Tree
open import Tree

data LContains (x : Nat) : List Nat -> Set where
  here : ∀ {xs} -> LContains x (x ∷ xs)
  there : ∀ {y ys} -> LContains x ys -> LContains x (y ∷ ys)

rest : ∀ {x} xs -> LContains x xs -> List Nat
rest .(_ ∷ xs) (here {xs}) = xs
rest .(y ∷ ys) (there {y} {ys} p) = y ∷ rest ys p

-- if list xs contains x then insertAll xs tree contains x too
insertAllContains : ∀ {x xs} -> LContains x xs -> TContains x (insertAll xs)
insertAllContains {x} {.x ∷ xs} here = mergeContainsLeft {x} {singletonHTree x} {insertAll xs} (singletonContains {x})
insertAllContains {x} {y ∷ ys} (there p) = mergeContainsRight {x} {singletonHTree y} {insertAll ys} (insertAllContains {x} {ys} p)
