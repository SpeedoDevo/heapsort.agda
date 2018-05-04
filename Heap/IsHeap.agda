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

-- mergeH : ∀ {l r} -> l IsHeap -> r IsHeap -> (mergeT l r) IsHeap
-- mergeH leafIsHeap r = r
-- mergeH l@(branchIsHeap _ _ _ _) leafIsHeap = l
-- mergeH {l@(branch ll (item lv _) lr)} {r@(branch rl (item rv _) rr)} lh@(branchIsHeap llih lrih llp lrp) rh@(branchIsHeap rlih rrih rlp rrp)
--    with ord lv rv
-- mergeH {l@(branch ll (item lv _) lr)} {r@(branch rl (item rv _) rr)} lh@(branchIsHeap llih lrih llp lrp) rh@(branchIsHeap rlih rrih rlp rrp)
--   | lte p with mergeT lr r
-- mergeH {l@(branch ll (item lv _) lr)} {r@(branch rl (item rv _) rr)} lh@(branchIsHeap llih lrih llp lrp) rh@(branchIsHeap rlih rrih rlp rrp)
--   | lte p | m with ord (rank ll) (rank m)
-- mergeH {l@(branch ll (item lv _) lr)} {r@(branch rl (item rv _) rr)} lh@(branchIsHeap llih lrih llp lrp) rh@(branchIsHeap rlih rrih rlp rrp)
--   | lte p | m | lte q with mergeH lrih rh
-- mergeH {branch ll (item lv _) lr} {branch rl (item rv _) rr} (branchIsHeap llih lrih llp lrp) (branchIsHeap rlih rrih rlp rrp)
--   | lte p | m | lte q | n = {!   !}
-- mergeH {l@(branch ll (item lv _) lr)} {r@(branch rl (item rv _) rr)} lh@(branchIsHeap llih lrih llp lrp) rh@(branchIsHeap rlih rrih rlp rrp)
--   | lte p | m | gte q  = {!   !}
-- mergeH {l@(branch ll (item lv _) lr)} {r@(branch rl (item rv _) rr)} lh@(branchIsHeap llih lrih llp lrp) rh@(branchIsHeap rlih rrih rlp rrp)
--   | gte p = {!  !}

data _IH : (t : HTree) -> Set where
  leafIsHeap : (t : HTree) -> t ≡ leaf -> t IH
  branchIsHeap : ∀ {l i r} -> (t : HTree) -> t ≡ (branch l i r)
    -> l IH -> r IH
    -> Item.value i ≤ value l -> Item.value i ≤ value r
    -> t IH

f : ∀ {t} -> t IH -> HTree
f (leafIsHeap t _) = t
f (branchIsHeap t _ _ _ _ _) = t

leftIH : ∀ {l i r} -> {t : HTree} -> t IH -> t ≡ branch l i r -> l IH
leftIH (leafIsHeap .(branch _ _ _) ()) refl
leftIH (branchIsHeap .(branch _ _ _) refl lih rih lp rp) refl = lih

rightIH : ∀ {l i r} -> {t : HTree} -> t IH -> t ≡ branch l i r -> r IH
rightIH (leafIsHeap .(branch _ _ _) ()) refl
rightIH (branchIsHeap .(branch _ _ _) refl lih rih lp rp) refl = rih

mergeIH : {l r : HTree} -> l IH -> r IH -> (mergeT l r) IH
mergeIH (leafIsHeap .leaf refl) r = r
mergeIH l@(branchIsHeap .(branch _ _ _) refl _ _ _ _) (leafIsHeap .leaf refl) = l
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  with ord lv rv
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | lte x with mergeIH lrih r
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | lte x | m with mergeT lr rt
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | lte x | m | n with ord (rank ll) (rank n)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m@(leafIsHeap .leaf refl) | n@.leaf | lte y
    = branchIsHeap (branch n (item lv (suc (rank ll))) ll) refl (leafIsHeap leaf refl) llih (lv ≤∞) llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m@(branchIsHeap {_} {item mv _} mt@.(branch _ _ _) refl lih rih lp rp) | n@.(branch _ _ _) | lte y
    = branchIsHeap (branch mt (item lv (suc (rank ll))) ll) refl (branchIsHeap mt refl lih rih lp rp) llih (lemma x) llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m@(leafIsHeap .leaf refl) | n@.leaf | gte y
    = branchIsHeap (branch ll (item lv 1) leaf) refl llih (leafIsHeap leaf refl) llp (lv ≤∞)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | lte x | m@(branchIsHeap {_} {item mv _} mt@.(branch _ _ _) refl lih rih lp rp) | n@.(branch _ _ _) | gte y
    = branchIsHeap (branch ll (item lv (suc (rank mt))) mt) refl llih (branchIsHeap mt refl lih rih lp rp) llp (lemma x)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x with mergeIH l rrih
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m with mergeT lt rr
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m | n with ord (rank rl) (rank n)
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m@(leafIsHeap .leaf refl) | n@.leaf | lte y
    = branchIsHeap (branch leaf (item rv (suc (rank rl))) rl) refl (leafIsHeap leaf refl) rlih (rv ≤∞) rlp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m@(branchIsHeap {_} {item mv _} mt@.(branch _ _ _) refl lih rih lp rp) | n@.(branch _ _ _) | lte y
    = branchIsHeap (branch mt (item rv (suc (rank rl))) rl) refl (branchIsHeap mt refl lih rih lp rp) rlih (lemma x) rlp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m@(leafIsHeap .leaf refl) | n@.leaf | gte y
    = branchIsHeap (branch leaf (item rv 1) rl) refl (leafIsHeap leaf refl) rlih (rv ≤∞) rlp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih rlp rrp)
  | gte x | m@(branchIsHeap {_} {item mv _} mt@.(branch _ _ _) refl lih rih lp rp) | n@.(branch _ _ _) | gte y
    = branchIsHeap (branch mt (item rv (suc (rank mt))) rl) refl (branchIsHeap mt refl lih rih lp rp) rlih (lemma x) rlp
