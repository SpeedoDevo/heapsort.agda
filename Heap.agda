module Heap where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Size

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Ord.Heap
open import Tree hiding (singleton)

data _IsHeap : ∀ {i} -> HTree {i} -> Set where
  leafIsHeap : ⊥ IsHeap
  branchIsHeap : ∀ {l r i} -> l IsHeap -> r IsHeap
    -> Item.value i ≤ value l -> Item.value i ≤ value r
    -> (branch l i r) IsHeap

data _IsLeftist : {i : Size} -> HTree {i} -> Set where
  leafIsLeftist : ⊥ IsLeftist
  branchIsLeftist : ∀ {l r i} -> l IsLeftist -> r IsLeftist
    -> rank r ≤ rank l
    -- -> Item.rank i ≡ 1 + (min (rank l) (rank r))
    -> (branch l i r) IsLeftist

record Heap {i : Size} : Set where
  constructor heap
  field
    tree : HTree {↑ i}
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

leftHeap : Heap -> Heap
leftHeap (heap leaf) = heap leaf {leafIsHeap} {leafIsLeftist}
leftHeap (heap (branch l _ _) {branchIsHeap lIsHeap _ _ _} {branchIsLeftist lIsLeftist _ _}) = heap l {lIsHeap} {lIsLeftist}

rightHeap : Heap -> Heap
rightHeap (heap leaf) = heap leaf {leafIsHeap} {leafIsLeftist}
rightHeap (heap (branch _ _ r) {branchIsHeap _ rIsHeap _ _} {branchIsLeftist _ rIsLeftist  _}) = heap r {rIsHeap} {rIsLeftist}

wtf : {i j : Size} (l r : Heap) → Ord (value (Heap.tree l)) (value (Heap.tree r)) → Heap
wtf l r o = {!   !}

merge : {i j : Size} -> Heap {i} -> Heap {j} -> Heap {i ⊔ˢ j}
merge {i} {j} (heap leaf) r = {! r !}
-- merge l (heap leaf) = l
-- merge l r with ord (HValue l) (HValue r)
-- merge (heap (branch ll (item v _) lr) {branchIsHeap lih rih lp rp}) r | lte x = make v (heap ll) (merge (heap lr) r) lp {!   !}
-- merge l r@(heap (branch rl (item v _) rr) {branchIsHeap lih rih lp rp}) | gte x = make v (heap rl) (merge l (heap rr)) lp {!   !}
