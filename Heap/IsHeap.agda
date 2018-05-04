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
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
 | lte x | m@(leafIsHeap .leaf refl) | n@.leaf | lte y = branchIsHeap (branch n (item lv (suc (rank ll))) ll) refl (leafIsHeap leaf refl) llih (lv ≤∞) llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
 | lte x | m@(branchIsHeap {ml} {item mv _} {mr} mt@.(branch _ _ _) refl lih rih lp rp) | n@.(branch _ _ _) | lte y
  = branchIsHeap (branch mt (item lv (suc (rank ll))) ll) refl (branchIsHeap mt refl lih rih lp rp) llih {! x  !} llp
    where
      k : mv ≡ lv
      k = {!   !}

 -- | lte x | m | n | lte y = branchIsHeap (branch n (item lv (suc (rank ll))) ll) refl m llih {! m  !} llp
-- mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih llp lrp) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
--  | lte x | m | n | lte y = branchIsHeap (branch n (item lv (suc (rank ll))) ll) refl m llih {!   !} llp
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
 | lte x | m | n | gte y = {!   !}


mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | gte x with mergeT lt rr
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | gte x | m with ord (rank rl) (rank m) | mergeIH l rrih
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | gte x | m | lte y | n = branchIsHeap (branch m (item rv (suc (rank rl))) rl) refl {!   !} rlih {!   !} {!   !}
mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _)
  | gte x | m | gte y | n = {!   !}


-- -- mergeIH l@(branchIsHeap {ll} {item lv _} {lr} .(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} .(branch _ _ _) refl rlih rrih _ _) | gte x | y = {!   !}
-- mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _) | gte x | leafIsHeap .(mergeT lt rr) x₂ = {! x₂  !}
-- -- mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _) | gte x | leafIsHeap .(mergeT lt rr) x₂ = {!   !}
-- mergeIH l@(branchIsHeap {ll} {item lv _} {lr} lt@.(branch _ _ _) refl llih lrih _ _) r@(branchIsHeap {rl} {item rv _} {rr} rt@.(branch _ _ _) refl rlih rrih _ _) | gte x | branchIsHeap .(mergeT lt rr) x₂ y y₁ x₃ x₄ = {!   !}
