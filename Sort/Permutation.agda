module Sort.Permutation where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List

open import Heap
open import Heap.HTree
open import Heap.Item
open import Heap.IsHeap
open import Heap.IsLeftist
open import Ord
open import Sort
open import Sort.Permutation.List
open import Sort.Permutation.Tree renaming (mergeContainsLeft to mergeTreeContainsLeft ; mergeContainsRight to mergeTreeContainsRight)
open import Sort.Permutation.Heap
open import Sort.Sort
open import Tree

sortContains : ∀ {x xs} -> LContains x xs -> LContains x (sort xs)
sortContains {x} {xs} p = flattenContains (toHeapContains p)

data Permutation : List Nat -> List Nat -> Set where
  [] : Permutation [] []
  _∷_ : ∀ {x xs ys} -> (c : LContains x xs) -> Permutation ys (rest c) -> Permutation (x ∷ ys) xs

test : ∀ x y -> Permutation (x ∷ y ∷ []) (y ∷ x ∷ [])
test x y = (there here) ∷ (here ∷ [])

test2 : ∀ x y z -> Permutation (x ∷ y ∷ z ∷ []) (y ∷ z ∷ x ∷ [])
test2 x y z = (there (there here)) ∷ (here ∷ (here ∷ []))
