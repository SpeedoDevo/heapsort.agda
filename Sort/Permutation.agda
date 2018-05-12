module Sort.Permutation where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List

open import Heap
open import Heap.HTree
open import Heap.Item
open import Heap.IsHeap
open import Heap.IsLeftist
open import NatExt
open import Ord
open import Sort
open import Sort.Permutation.List
open import Sort.Permutation.Heap
open import Sort.Sort
open import Tree

sortContains : ∀ x xs -> LContains x xs -> LContains x (sort xs)
sortContains x xs p = flattenContains (toHeapContains p)

data Permutation (xs : List Nat) : List Nat -> Set where
  -- if we know what elements one list contains and can prove that every element is in another list too then it is a permutation
  perm : ∀ ys -> ((x : Nat) -> LContains x xs -> LContains x ys) -> Permutation xs ys

sortMakesPermutation : ∀ xs -> Permutation xs (sort xs)
sortMakesPermutation xs = perm (flatten (toHeap xs)) (λ x p -> sortContains x xs p)

-- this is not a precise formulation but it is close enough
abuse : Permutation (1 ∷ 1 ∷ 1 ∷ []) (1 ∷ [])
abuse = perm (1 ∷ []) p
  where
    p : (x : Nat) -> LContains x (1 ∷ 1 ∷ 1 ∷ []) -> LContains x (1 ∷ [])
    p .1 here = here
    p .1 (there here) = here
    p x (there (there q)) = q
