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
open import Tuple

record LeftistHeap (t : HTree) : Set where
  constructor leftistHeap
  field
    isLeftist : t IsLeftist
    isHeap : t IsHeap
open LeftistHeap

singleton : (v : Nat) -> LeftistHeap (singletonTree v)
singleton v = leftistHeap
    (branchIsLeftist refl (leafIsLeftist refl) (leafIsLeftist refl) (zero≤ zero) refl)
    (branchIsHeap refl (leafIsHeap refl) (leafIsHeap refl) (v ≤∞) (v ≤∞))

merge : {l r : HTree} -> LeftistHeap l -> LeftistHeap r -> LeftistHeap (mergeTree l r)
merge l r = leftistHeap (mergeIsLeftist (isLeftist l) (isLeftist r)) (mergeIsHeap (isHeap l) (isHeap r))

pop : {t : HTree} -> LeftistHeap t -> Tuple Nat (LeftistHeap (Tuple.snd (popTree t)))
pop {leaf} h = ∞ ** leftistHeap (isLeftist h) (isHeap h)
pop {branch l i r} (leftistHeap (leafIsLeftist ()) ih)
pop {branch l i r} (leftistHeap lh (leafIsHeap ()))
pop {branch l i r} (leftistHeap (branchIsLeftist refl lil ril lp rp) (branchIsHeap refl lih rih p q))
  = (Item.value i) ** leftistHeap (mergeIsLeftist lil ril) (mergeIsHeap lih rih)

popSingleton : ∀ {n} -> n ≡ Tuple.fst (pop (singleton n))
popSingleton {n} = refl
