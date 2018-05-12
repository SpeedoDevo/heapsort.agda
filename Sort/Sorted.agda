module Sort.Sorted where

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
open import Sort.Ordered
open import Sort.Permutation
open import Sort.Sort
open import Tree

record Sorted (xs : List Nat) : Set where
  constructor sorted
  field
    sxs : List Nat
    ordered : Ordered sxs
    permutation : Permutation xs sxs

sortedProof : ∀ xs -> Sorted xs
sortedProof xs = sorted (sort xs) (sortMakesOrdered {xs}) (sortIsPermutation xs)
