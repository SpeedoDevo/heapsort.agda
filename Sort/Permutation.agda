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
open import Sort.Permutation.Tree renaming (mergeContainsLeft to mergeTreeContainsLeft ; mergeContainsRight to mergeTreeContainsRight)
open import Sort.Permutation.Heap
open import Sort.Sort
open import Tree

data SContains (x : Nat) : List Nat -> Set where
  contains : ∀ xs -> (p : LContains x xs) -> (q : LContains x (sort xs)) -> SContains x xs

sortContains : ∀ x xs -> LContains x xs -> SContains x xs
sortContains x xs p = contains xs p (flattenContains (toHeapContains p))

data Permutation : List Nat -> List Nat -> Set where
  [] : Permutation [] []
  _∷_ : ∀ {x xs ys} -> (p : LContains x xs) -> Permutation ys (rest xs p) -> Permutation (x ∷ ys) xs

-- TODO prove this, dunno how
postulate
  restSortPermutation : ∀ x xs q -> Permutation xs (rest {x} (sort (x ∷ xs)) q)

sortIsPermutation : ∀ xs -> Permutation xs (sort xs)
sortIsPermutation [] = []
sortIsPermutation (x ∷ xs) with sortContains x (x ∷ xs) here
... | contains _ p q = q ∷ restSortPermutation x xs q
