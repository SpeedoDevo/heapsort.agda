module Heap where

open import Agda.Builtin.Nat
open import Agda.Builtin.Size

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Ord.Heap
open import Tree hiding (singleton)

data _IsHeap : HTree -> Set where
  leafIsHeap : ⊥ IsHeap
  branchIsHeap : ∀ {l r i} -> l IsHeap -> r IsHeap
    -> Item.value i ≤ value l -> Item.value i ≤ value r
    -> (branch l i r) IsHeap

data _IsLeftist : HTree -> Set where
  leafIsLeftist : ⊥ IsLeftist
  branchIsLeftist : ∀ {l r i} -> l IsLeftist -> r IsLeftist
    -> rank r ≤ rank l
    -- -> Item.rank i ≡ 1 + (min (rank l) (rank r))
    -> (branch l i r) IsLeftist

record Heap {i : Size} : Set where
  constructor heap
  field
    tree : HTree
    {isHeap} : tree IsHeap
    {isLeftist} : tree IsLeftist

singleton : Nat -> Heap
Heap.tree (singleton n) = (branch leaf (item n 0) leaf)
Heap.isHeap (singleton n) = branchIsHeap leafIsHeap leafIsHeap (n ≤∞) (n ≤∞)
Heap.isLeftist (singleton n) = branchIsLeftist leafIsLeftist leafIsLeftist (zero≤ 0)

HRank : Heap -> Nat
HRank h = rank (Heap.tree h)

HValue : Heap -> Nat
HValue h = value (Heap.tree h)

make : (val : Nat) -> (l r : Heap) -> val ≤ HValue l -> val ≤ HValue r -> Heap
Heap.tree (make val l r j k) with ord (HRank l) (HRank r)
... | lte p = branch (Heap.tree r) (item val (suc (HRank l))) (Heap.tree l)
... | gte p = branch (Heap.tree l) (item val (suc (HRank r))) (Heap.tree r)
Heap.isHeap (make val l@(heap lt {lIsHeap}) r@(heap rt {rIsHeap}) j k) with ord (HRank l) (HRank r)
... | lte _ = branchIsHeap rIsHeap lIsHeap k j
... | gte _ = branchIsHeap lIsHeap rIsHeap j k
Heap.isLeftist (make val l@(heap lt {_} {ltIsLeftist}) r@(heap rt {_} {rtIsLeftist}) j k) with ord (HRank l) (HRank r)
... | lte p = branchIsLeftist rtIsLeftist ltIsLeftist p
... | gte p = branchIsLeftist ltIsLeftist rtIsLeftist p
