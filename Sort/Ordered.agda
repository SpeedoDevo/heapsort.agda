module Sort.Ordered where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Heap
open import Heap.HTree
open import Heap.IsHeap
open import Heap.IsLeftist
open import Heap.Item
open import Ord
open import Sort.Sort
open import Tree

data _≤*_ (x : Nat) : List Nat -> Set where
  [] : x ≤* []
  _∷_ : ∀ {y ys} -> (x ≤ y) -> x ≤* ys -> x ≤* (y ∷ ys)

data Ordered : List Nat -> Set where
  [] : Ordered []
  _∷_ : ∀ {x xs} -> x ≤* xs -> Ordered xs -> Ordered (x ∷ xs)

{-# TERMINATING #-}
flattenKeepsOrd : ∀ {t h} -> (s : HTree) -> value s ≤ value t -> value s ≤* flatten {t} h
flattenKeepsOrd {.leaf} {leftistHeap (leafIsLeftist refl) (leafIsHeap refl)} s o = []
flattenKeepsOrd {.leaf} {leftistHeap (leafIsLeftist refl) (branchIsHeap () _ _ _ _)} s o
flattenKeepsOrd {.leaf} {leftistHeap (branchIsLeftist () _ _ _ _) (leafIsHeap refl)} s o
flattenKeepsOrd {branch l _ r} {h@(leftistHeap (branchIsLeftist refl lil ril p q) (branchIsHeap refl lih rih lp rp))} s o
  = o ∷ flattenKeepsOrd {_} {(merge (leftistHeap lil lih) (leftistHeap ril rih))} s (mergeKeepsOrd s l r (transitive o lp) (transitive o rp))

{-# TERMINATING #-}
flattenMakesOrdered : ∀ {t h} -> Ordered (flatten {t} h)
flattenMakesOrdered {.leaf} {leftistHeap (leafIsLeftist refl) (leafIsHeap refl)} = []
flattenMakesOrdered {.leaf} {leftistHeap (leafIsLeftist refl) (branchIsHeap () _ _ _ _)}
flattenMakesOrdered {.leaf} {leftistHeap (branchIsLeftist () _ _ _ _) (leafIsHeap refl)}
flattenMakesOrdered {t@(branch l _ r)} {h@(leftistHeap (branchIsLeftist refl lil ril p q) (branchIsHeap refl lih rih lp rp))}
  = flattenKeepsOrd {_} {merge (leftistHeap lil lih) (leftistHeap ril rih)} t (mergeKeepsOrd t l r lp rp)
  ∷ flattenMakesOrdered {_} {merge (leftistHeap lil lih) (leftistHeap ril rih)}

sortMakesOrdered : ∀ {xs} -> Ordered (sort xs)
sortMakesOrdered {xs} = flattenMakesOrdered {_} {toHeap xs}
