module Heap.HTree where

open import Agda.Builtin.Equality
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
  | gte p | merged | gte q = branch rl (item rVal (suc (rank merged))) merged

mergeKeepsOrd : (t l r : HTree) -> value t ≤ value l -> value t ≤ value r -> value t ≤ value (mergeT l r)
mergeKeepsOrd t (leaf) (r) o p = p
mergeKeepsOrd t (l@(branch ll li lr)) (leaf) o p = o
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p with ord (value l) (value r)
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q with mergeT lr r
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q | m with ord (rank ll) (rank m)
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q | m | lte s = o
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q | m | gte s = o
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q with mergeT l rr
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q | m with ord (rank rl) (rank m)
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q | m | lte s = p
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q | m | gte s = p
