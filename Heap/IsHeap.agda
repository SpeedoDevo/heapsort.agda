module Heap.IsHeap where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Tree

data _IsHeap : (t : HTree) -> Set where
  leafIsHeap : {t : HTree} -> t ≡ leaf -> t IsHeap
  branchIsHeap : ∀ {l i r} -> {t : HTree} -> t ≡ (branch l i r)
    -> l IsHeap -> r IsHeap
    -> Item.value i ≤ value l -> Item.value i ≤ value r
    -> t IsHeap

mergeIsHeap : {l r : HTree} -> l IsHeap -> r IsHeap -> (mergeTree l r) IsHeap
mergeIsHeap (leafIsHeap refl) r = r
mergeIsHeap l@(branchIsHeap refl _ _ _ _) (leafIsHeap refl) = l

mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    with ord (value lt) (value rt)
mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    | lte x with mergeIsHeap lrih r | ord (rank ll) (rank (mergeTree lr rt))
mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    | lte x | m | lte y
      = branchIsHeap refl m llih (mergeKeepsOrd lt lr rt lrp x) llp
mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    | lte x | m | gte y
      = branchIsHeap refl llih m llp (mergeKeepsOrd lt lr rt lrp x)

mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    | gte x with mergeIsHeap l rrih | ord (rank rl) (rank (mergeTree lt rr))
mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    | gte x | m | lte y
      = branchIsHeap refl m rlih (mergeKeepsOrd rt lt rr x rrp) rlp
mergeIsHeap
  l@(branchIsHeap {t = lt@(branch ll _ lr)} refl llih lrih llp lrp)
  r@(branchIsHeap {t = rt@(branch rl _ rr)} refl rlih rrih rlp rrp)
    | gte x | m | gte y
      = branchIsHeap refl rlih m rlp (mergeKeepsOrd rt lt rr x rrp)
