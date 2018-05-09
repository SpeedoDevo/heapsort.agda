module Heap where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Heap.HTree
open import Heap.Item
open import Heap.IsHeap
open import Heap.IsLeftist
open import NatExt
open import Ord
open import Tree
open import Tuple

record LeftistHeap (t : HTree) : Set where
  constructor leftistHeap
  field
    isLeftist : t IsLeftist
    isHeap : t IsHeap
open LeftistHeap

singleton : (v : Nat) -> LeftistHeap (singletonHTree v)
singleton v = leftistHeap
    (branchIsLeftist refl (leafIsLeftist refl) (leafIsLeftist refl) (zero≤ zero) refl)
    (branchIsHeap refl (leafIsHeap refl) (leafIsHeap refl) (v ≤∞) (v ≤∞))

merge : {l r : HTree} -> LeftistHeap l -> LeftistHeap r -> LeftistHeap (mergeTree l r)
merge l r = leftistHeap (mergeIsLeftist (isLeftist l) (isLeftist r)) (mergeIsHeap (isHeap l) (isHeap r))

deleteMin : {t : HTree} -> LeftistHeap t -> LeftistHeap (deleteMinTree t)
deleteMin {leaf} h = leftistHeap (isLeftist h) (isHeap h)
deleteMin {branch _ _ _} (leftistHeap (leafIsLeftist ()) ih)
deleteMin {branch _ _ _} (leftistHeap il (leafIsHeap ()))
deleteMin {branch _ _ _} (leftistHeap (branchIsLeftist refl lil ril p q) (branchIsHeap refl lih rih lp rp))
  = merge (leftistHeap lil lih) (leftistHeap ril rih)

data PopD : Set where
  popd : {t : HTree} (v : Nat) (h : LeftistHeap t) -> (vvt : v ≤ value t) -> PopD

pop : {t : HTree} -> LeftistHeap t -> PopD
pop {leaf} h@(leftistHeap _ _)
  = popd {leaf} (value leaf) h (x≤x ∞)
pop {branch _ _ _} h@(leftistHeap (leafIsLeftist ()) _)
pop {branch _ _ _} h@(leftistHeap _ (leafIsHeap ()))
pop {t@(branch l _ r)} h@(leftistHeap _ (branchIsHeap refl lih rih lp rp))
  = popd (value t) (deleteMin h) (mergeKeepsOrd t l r lp rp)
