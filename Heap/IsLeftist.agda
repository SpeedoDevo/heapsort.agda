module Heap.IsLeftist where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

open import Heap.HTree
open import Heap.Item
open import NatExt
open import Ord
open import Tree

data _IsLeftist : (t : HTree) -> Set where
  leafIsLeftist : {t : HTree} -> t ≡ leaf -> t IsLeftist
  branchIsLeftist : ∀ {l i r} -> {t : HTree} -> t ≡ (branch l i r)
    -> l IsLeftist -> r IsLeftist
    -> rank r ≤ rank l
    -> rank t ≡ suc (rank r)
    -> t IsLeftist

mergeIsLeftist : {l r : HTree} -> l IsLeftist -> r IsLeftist -> (mergeTree l r) IsLeftist
mergeIsLeftist (leafIsLeftist refl) r = r
mergeIsLeftist l@(branchIsLeftist refl _ _ _ _) (leafIsLeftist refl) = l

mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    with ord (value lt) (value rt)
mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    | lte x with mergeIsLeftist lril r | ord (rank ll) (rank (mergeTree lr rt))
mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    | lte x | m | lte y
      = branchIsLeftist refl m llil y refl
mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    | lte x | m | gte y
      = branchIsLeftist refl llil m y refl

mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    | gte x with mergeIsLeftist l rril | ord (rank rl) (rank (mergeTree lt rr))
mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    | gte x | m | lte y
      = branchIsLeftist refl m rlil y refl
mergeIsLeftist
  l@(branchIsLeftist {t = lt@(branch ll _ lr)} refl llil lril lp lq)
  r@(branchIsLeftist {t = rt@(branch rl _ rr)} refl rlil rril rp rq)
    | gte x | m | gte y
      = branchIsLeftist refl rlil m y refl
