module Sort.Sort where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Heap
open import Heap.HTree
open import Heap.IsHeap
open import Heap.IsLeftist
open import Tree

-- creates a tree containing all elements from the list
insertAll : List Nat -> HTree
insertAll [] = leaf
insertAll (x ∷ xs) = mergeTree (singletonHTree x) (insertAll xs)

-- creates a heap containing all elements from the list
toHeap : (xs : List Nat) -> LeftistHeap (insertAll xs)
toHeap [] = leftistHeap (leafIsLeftist refl) (leafIsHeap refl)
toHeap (x ∷ xs) = merge (singleton x) (toHeap xs)

-- creates a list containing all elements from the heap
{-# TERMINATING #-}
flatten : {t : HTree} -> LeftistHeap t -> List Nat
flatten {leaf} _ = []
flatten h with pop h
flatten h | popd v ph _ = v ∷ (flatten ph)

-- sorts a list by turning it into a heap and then back to a list
sort : List Nat -> List Nat
sort xs = flatten (toHeap xs)
