module Heap.IsHeap where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Tree

data _IH : (t : HTree) -> Set where
  leafIsHeap : (t : HTree) -> t ≡ leaf -> t IH
  branchIsHeap : ∀ {l i r} -> (t : HTree) -> t ≡ (branch l i r)
    -> l IH -> r IH
    -> Item.value i ≤ value l -> Item.value i ≤ value r
    -> t IH

mergeIH : {l r : HTree} -> l IH -> r IH -> (mergeT l r) IH
mergeIH (leafIsHeap .leaf refl) r = r
mergeIH l@(branchIsHeap .(branch _ _ _) refl _ _ _ _) (leafIsHeap .leaf refl) = l
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  with ord lv rv
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x with mergeIH lrih r
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m with ord (rank ll) (rank (mergeT lr rt))
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m | lte y = branchIsHeap _ refl m llih (mergeKeepsOrd lt lr rt lrp x) llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m | gte y = branchIsHeap _ refl llih m llp (mergeKeepsOrd lt lr rt lrp x)

mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x with mergeIH l rrih
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m with ord (rank rl) (rank (mergeT lt rr))
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | lte y = branchIsHeap _ refl m rlih (mergeKeepsOrd rt lt rr x rrp) rlp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | gte y = branchIsHeap _ refl rlih m rlp (mergeKeepsOrd rt lt rr x rrp)
