module Sort.Permutation.Heap where

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
open import Sort.Sort
open import Tree

data HContains (v : Nat) : {t : HTree} -> LeftistHeap t -> Set where
  contains : ∀ {t} -> (h : LeftistHeap t) -> TContains v t -> HContains v h

toHeapContains : ∀ {x xs} -> LContains x xs -> HContains x (toHeap xs)
toHeapContains {x} {xs} p = contains (toHeap xs) (insertAllContains p)

mergeContainsLeft : ∀ {x lt rt} -> (l : LeftistHeap lt) -> (r : LeftistHeap rt) -> HContains x l -> HContains x (merge l r)
mergeContainsLeft {x} {lt} {rt} l r (contains .l p) = contains {x} {_} (merge l r) (mergeTreeContainsLeft {x} {lt} {rt} p)

mergeContainsRight : ∀ {x lt rt} -> (l : LeftistHeap lt) -> (r : LeftistHeap rt) -> HContains x r -> HContains x (merge l r)
mergeContainsRight {x} {lt} {rt} l r (contains .r p) = contains {x} {_} (merge l r) (mergeTreeContainsRight {x} {lt} {rt} p)

{-# TERMINATING #-}
flattenContains : ∀ {x t h} -> HContains x h -> LContains x (flatten {t} h)
flattenContains {x} {leaf} {.h} (contains h ())
flattenContains {x} {_} {_} (contains (leftistHeap (leafIsLeftist ()) _) here)
flattenContains {x} {_} {_} (contains (leftistHeap (branchIsLeftist _ _ _ _ _) (leafIsHeap ())) here)
flattenContains {x} {.(branch _ (item x _) _)} {h} (contains (leftistHeap (branchIsLeftist refl lil ril ilp ilq) (branchIsHeap refl lih rih lp rp)) here) = here
flattenContains {x} {_} {_} (contains (leftistHeap (leafIsLeftist ()) _) (toLeft _))
flattenContains {x} {_} {_} (contains (leftistHeap (branchIsLeftist _ _ _ _ _) (leafIsHeap ())) (toLeft _))
flattenContains {x} {t@(branch l i r)} {h} (contains (leftistHeap (branchIsLeftist refl lil ril ilp ilq) (branchIsHeap refl lih rih lp rp)) (toLeft p))
  = there (flattenContains (mergeContainsLeft (leftistHeap lil lih) (leftistHeap ril rih) (contains (leftistHeap lil lih) p)))
flattenContains {x} {_} {_} (contains (leftistHeap (leafIsLeftist ()) _) (toRight _))
flattenContains {x} {_} {_} (contains (leftistHeap (branchIsLeftist _ _ _ _ _) (leafIsHeap ())) (toRight _))
flattenContains {x} {t@(branch l i r)} {h} (contains (leftistHeap (branchIsLeftist refl lil ril ilp ilq) (branchIsHeap refl lih rih lp rp)) (toRight p))
  = there (flattenContains (mergeContainsRight (leftistHeap lil lih) (leftistHeap ril rih) (contains (leftistHeap ril rih) p)))
