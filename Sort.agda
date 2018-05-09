module Sort where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Heap
open import Heap.HTree
open import Heap.IsHeap
open import Heap.IsLeftist
open import Heap.Item
open import Tree
open import Tuple

insertAll : List Nat -> HTree
insertAll [] = leaf
insertAll (x ∷ xs) = mergeTree (singletonHTree x) (insertAll xs)

toHeap : (xs : List Nat) -> LeftistHeap (insertAll xs)
toHeap [] = leftistHeap (leafIsLeftist refl) (leafIsHeap refl)
toHeap (x ∷ xs) with toHeap xs
... | h = merge (singleton x) h

flatten : HTree -> List Nat
flatten leaf = []
flatten t@(branch l (item v _) r) = v ∷ flatten (mergeTree l r)
