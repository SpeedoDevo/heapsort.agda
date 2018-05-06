module Heap where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Size

open import Heap.HTree
open import Heap.Item
open import Heap.IsHeap
open import Heap.IsLeftist
open import NatExt
open import Ord
open import Tree hiding (singleton)

record LeftistHeap (t : HTree) : Set where
  field
    {isLeftist} : t IsLeftist
    {isHeap} : t IsHeap
open LeftistHeap

leftistHeap : {t : HTree} -> t IsLeftist -> t IsHeap -> LeftistHeap t
leftistHeap p q = record {isLeftist = p; isHeap = q}

singleton : (v : Nat) -> LeftistHeap (singletonTree v)
singleton v = leftistHeap
    (branchIsLeftist refl (leafIsLeftist refl) (leafIsLeftist refl) (zero≤ zero) refl)
    (branchIsHeap refl (leafIsHeap refl) (leafIsHeap refl) (v ≤∞) (v ≤∞))

merge : {l r : HTree} -> LeftistHeap l -> LeftistHeap r -> LeftistHeap (mergeTree l r)
merge l r = leftistHeap (mergeIsLeftist (isLeftist l) (isLeftist r)) (mergeIsHeap (isHeap l) (isHeap r))
