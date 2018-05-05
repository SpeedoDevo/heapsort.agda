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

data _ILH : (t : HTree) -> Set where
  ilh : (t : HTree) -> t IH -> t IL -> t ILH

merge : {l r : HTree} -> l ILH -> r ILH -> (mergeT l r) ILH
merge (ilh lt lih lil) (ilh rt rih ril) = ilh (mergeT lt rt) (mergeIH lih rih) (mergeIL lil ril)
