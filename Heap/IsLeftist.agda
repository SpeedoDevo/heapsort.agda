module Heap.IsLeftist where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Tree

data _IL : (t : HTree) -> Set where
  leafIsLeftist : (t : HTree) -> t ≡ leaf -> t IL
  branchIsLeftist : ∀ {l i r} -> (t : HTree) -> t ≡ (branch l i r)
    -> l IL -> r IL
    -> rank r ≤ rank l
    -> rank t ≡ suc (rank r)
    -> t IL

mergeIL : {l r : HTree} -> l IL -> r IL -> (mergeT l r) IL
mergeIL (leafIsLeftist .leaf refl) r = r
mergeIL l@(branchIsLeftist .(branch _ _ _) refl _ _ _ _) (leafIsLeftist .leaf refl) = l
mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  with ord lv rv
mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  | lte x with mergeIL lril r | ord (rank ll) (rank (mergeT lr rt))
mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  | lte x | m | lte y = branchIsLeftist _ refl m llil y refl
mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  | lte x | m | gte y = branchIsLeftist _ refl llil m y refl

mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  | gte x with mergeIL l rril | ord (rank rl) (rank (mergeT lt rr))
mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  | gte x | m | lte y = branchIsLeftist _ refl m rlil y refl
mergeIL l@(branchIsLeftist {ll} {item lv lw} {lr} lt@.(branch _ _ _) refl llil lril lp lq) r@(branchIsLeftist {rl} {item rv rw} {rr} rt@.(branch _ _ _) refl rlil rril rp rq)
  | gte x | m | gte y = branchIsLeftist _ refl rlil m y refl
