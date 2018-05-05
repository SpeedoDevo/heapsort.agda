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

record Heap {i : Size} : Set where
  constructor heap
  field
    tree : HTree
    {isHeap} : tree IsHeap
    {isLeftist} : tree IsLeftist

singleton : Nat -> Heap
Heap.tree (singleton n) = (branch leaf (item n 0) leaf)
Heap.isHeap (singleton n) = branchIsHeap leafIsHeap leafIsHeap (n ≤∞) (n ≤∞)
Heap.isLeftist (singleton n) = branchIsLeftist leafIsLeftist leafIsLeftist (zero≤ 0)

HRank : Heap -> Nat
HRank h = rank (Heap.tree h)

HValue : Heap -> Nat
HValue h = value (Heap.tree h)

-- make : (val : Nat) -> (l r : Heap) -> val ≤ HValue l -> val ≤ HValue r -> Heap
-- Heap.tree (make val l r j k) with ord (HRank l) (HRank r)
-- ... | lte p = branch (Heap.tree r) (item val (suc (HRank l))) (Heap.tree l)
-- ... | gte p = branch (Heap.tree l) (item val (suc (HRank r))) (Heap.tree r)
-- Heap.isHeap (make val l@(heap lt {lIsHeap}) r@(heap rt {rIsHeap}) j k) with ord (HRank l) (HRank r)
-- ... | lte _ = branchIsHeap rIsHeap lIsHeap k j
-- ... | gte _ = branchIsHeap lIsHeap rIsHeap j k
-- Heap.isLeftist (make val l@(heap lt {_} {ltIsLeftist}) r@(heap rt {_} {rtIsLeftist}) j k) with ord (HRank l) (HRank r)
-- ... | lte p = branchIsLeftist rtIsLeftist ltIsLeftist p
-- ... | gte p = branchIsLeftist ltIsLeftist rtIsLeftist p

data _IsLHeap : (t : HTree) -> Set where
  -- leafIsLHeap : ⊥ IsLHeap
  isLHeap : (t : HTree) -> t IsLeftist -> t IsHeap -> t IsLHeap

leftIsHeap : ∀ {l i r} -> (branch l i r) IsLHeap -> l IsLHeap
leftIsHeap {l = l} (isLHeap .(branch _ _ _) (branchIsLeftist lil ril p) (branchIsHeap lih rih lq rq)) = isLHeap l lil lih

rightIsHeap : ∀ {l i r} -> (branch l i r) IsLHeap -> r IsLHeap
rightIsHeap {r = r} (isLHeap .(branch _ _ _) (branchIsLeftist lil ril p) (branchIsHeap lih rih lq rq)) = isLHeap r ril rih

isLeftist : ∀ {t} -> t IsLHeap -> t IsLeftist
isLeftist (isLHeap _ p _) = p

isHeap : ∀ {t} -> t IsLHeap -> t IsHeap
isHeap (isLHeap _ _ p) = p

-- merge : ∀ {l r} -> l IsLHeap -> r IsLHeap -> (mergeT l r) IsLHeap
-- merge (isLHeap leaf _ _) r = r
-- merge l@(isLHeap (branch _ _ _) p q) (isLHeap leaf _ _) = l
-- merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
--   with ord lVal rVal
-- merge lh@(isLHeap l@(branch ll (item lVal lRank) lr) lp lq) rh@(isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
--   | lte x with merge (leftIsHeap lh) rh
-- -- merge lh@(isLHeap l@(branch ll (item lVal lRank) lr) lp lq) rh@(isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
-- merge (isLHeap (branch ll (item lVal lRank) lr) lp lq) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
--   | lte x | isLHeap .(mergeT ll (branch rl (item rVal rRank) rr)) x₁ x₂ with ord (rank ll) (rank (mergeT lr (branch rl (item rVal rRank) rr)))
-- merge lh@(isLHeap (branch ll (item lVal lRank) lr) lp lq) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
--   | lte x | isLHeap .(mergeT ll (branch rl (item rVal rRank) rr)) x₁ x₂ | lte y
--     = isLHeap
--       (branch (mergeT lr (branch rl (item rVal rRank) rr)) (item lVal (suc (rank ll))) ll)
--       {!   !}
--       (branchIsHeap {!   !} (isHeap (leftIsHeap lh)) {!   !} {!   !})
-- merge (isLHeap (branch ll (item lVal lRank) lr) lp lq) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
--   | lte x | isLHeap .(mergeT ll (branch rl (item rVal rRank) rr)) x₁ x₂ | gte y = {!   !}
--
--
-- merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
--   | gte x with ord (rank ll) (rank (mergeT l rr))
-- merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
--   | gte x | p = {!   !}

{-
-- merge leafIsLHeap q = q
-- merge (isLHeap t p q) leafIsLHeap with mergeT t leaf
-- merge (isLHeap t p q) leafIsLHeap | leaf = leafIsLHeap
-- merge (isLHeap .leaf leafIsLeftist q) leafIsLHeap | branch l i r = isLHeap (branch l i r) (branchIsLeftist {!   !} {!   !} {!   !}) {!   !}
-- merge (isLHeap .(branch _ _ _) (branchIsLeftist p p₁ x) q) leafIsLHeap | branch l i r = isLHeap (branch l i r) (branchIsLeftist {!   !} {!   !} {!   !}) {!   !}
-- merge (isLHeap t p q) (isLHeap t₁ x₂ x₃) = {!   !}
merge (isLHeap leaf _ _) r = r
merge l@(isLHeap (branch _ _ _) p q) (isLHeap leaf _ _) = l
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  with ord lVal rVal
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | lte x with mergeT lr r
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | lte x | merged with ord (rank ll) (rank merged)
-- merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
-- merge (isLHeap (branch ll (item lVal lRank) lr) (branchIsLeftist lp lp₁ x₁) lq) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
-- merge (isLHeap (branch ll (item lVal lRank) lr) (branchIsLeftist lp lp₁ x₁) (branchIsHeap lq lq₁ x₂ x₃)) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
merge (isLHeap (branch ll (item lVal lRank) lr) (branchIsLeftist lp lp₁ x₁) (branchIsHeap lq lq₁ x₂ x₃)) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
  | lte x | leaf | lte y = isLHeap (branch leaf (item lVal (suc (rank ll))) ll) (branchIsLeftist leafIsLeftist lp y) (branchIsHeap leafIsHeap lq (lVal ≤∞) x₂)
merge (isLHeap (branch ll (item lVal lRank) lr) (branchIsLeftist lp lp₁ x₁) (branchIsHeap lq lq₁ x₂ x₃)) (isLHeap (branch rl (item rVal rRank) rr) rp rq)
  | lte x | branch merged e merged₁ | lte y = isLHeap {!   !} (branchIsLeftist (branchIsLeftist {!   !} {!   !} {!   !}) lp y) (branchIsHeap {!   !} lq {!   !} x₂)
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | lte x | merged | gte y = {!   !}
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | gte x with mergeT l rr
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | gte x | merged with ord (rank rl) (rank merged)
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | gte x | merged | lte y = {!   !}
merge (isLHeap l@(branch ll (item lVal lRank) lr) lp lq) (isLHeap r@(branch rl (item rVal rRank) rr) rp rq)
  | gte x | merged | gte y = {!   !}
-}
