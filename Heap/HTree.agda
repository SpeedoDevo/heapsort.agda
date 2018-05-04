module Heap.HTree where

open import Agda.Builtin.Nat
open import Heap.Item
open import NatExt
open import Ord
open import Tree

HTree : Set
HTree = Tree Item

rank : HTree -> Nat
rank leaf = 0
rank (branch _ i _) = Item.rank i

value : HTree -> Nat
value leaf = ∞
value (branch _ i _) = Item.value i

mergeT : (l r : HTree) -> HTree
mergeT leaf r = r
mergeT l leaf = l
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  with ord lVal rVal
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p with mergeT lr r
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p | merged with ord (rank ll) (rank merged)
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p | merged | lte q = branch merged (item lVal (suc (rank ll))) ll
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p | merged | gte q = branch ll (item lVal (suc (rank merged))) merged
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p with mergeT l rr
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p | merged with ord (rank rl) (rank merged)
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p | merged | lte q = branch merged (item rVal (suc (rank rl))) rl
mergeT l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p | merged | gte q = branch merged (item rVal (suc (rank merged))) rl


lemma : ∀ {l r} -> value l ≤ value r -> value l ≤ value (mergeT l r)
lemma {leaf} {r} p = p
lemma {l@(branch ll li lr)} {leaf} p = x≤x (Item.value li)
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p with ord (value l) (value r)
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | lte q with mergeT lr r
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | lte q | m with ord (rank ll) (rank m)
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | lte q | m | lte s = x≤x (Item.value li)
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | lte q | m | gte s = x≤x (Item.value li)
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | gte q with mergeT l rr
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | gte q | m with ord (rank rl) (rank m)
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | gte q | m | lte s = p
lemma {l@(branch ll li lr)} {r@(branch rl ri rr)} p | gte q | m | gte s = p
