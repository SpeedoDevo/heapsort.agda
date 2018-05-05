module Heap.IsHeap where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Tree

data _IsHeap : HTree -> Set where
  leafIsHeap : ⊥ IsHeap
  branchIsHeap : ∀ {l i r} -> l IsHeap -> r IsHeap
    -> Item.value i ≤ value l -> Item.value i ≤ value r
    -> (branch l i r) IsHeap

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
  | lte x | m with ord (rank ll) (rank (mergeT lr rt)) | ord (value lr) (value rt)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m | lte y | lte z = branchIsHeap _ refl m llih (substitution (mergeInheritsLeftValue lr rt z) lrp) llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m | lte y | gte z = branchIsHeap _ refl m llih (substitution (mergeInheritsRightValue lr rt z) x) llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m | gte y | lte z = branchIsHeap _ refl llih m llp (substitution (mergeInheritsLeftValue lr rt z) lrp)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m | gte y | gte z = branchIsHeap _ refl llih m llp (substitution (mergeInheritsRightValue lr rt z) x)

mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x with mergeIH l rrih
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m with ord (rank rl) (rank (mergeT lt rr)) | ord (value lt) (value rr)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | lte y | lte z = branchIsHeap _ refl m rlih (substitution (mergeInheritsLeftValue lt rr z) x) rlp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | lte y | gte z = branchIsHeap _ refl m rlih (substitution (mergeInheritsRightValue lt rr z) rrp) rlp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | gte y | lte z = branchIsHeap _ refl rlih m rlp (substitution (mergeInheritsLeftValue lt rr z) x)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | gte y | gte z = branchIsHeap _ refl rlih m rlp (substitution (mergeInheritsRightValue lt rr z) rrp)
