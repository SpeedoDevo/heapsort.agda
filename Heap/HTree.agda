module Heap.HTree where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

open import Heap.Item
open import NatExt
open import Ord
open import Tree
open import Tuple

HTree : Set
HTree = Tree Item

rank : HTree -> Nat
rank leaf = 0
rank (branch _ i _) = Item.rank i

value : HTree -> Nat
value leaf = ∞
value (branch _ i _) = Item.value i

mergeTree : (l r : HTree) -> HTree
mergeTree leaf r = r
mergeTree l leaf = l
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  with ord lVal rVal
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p with mergeTree lr r
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p | merged with ord (rank ll) (rank merged)
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p | merged | lte q = branch merged (item lVal (suc (rank ll))) ll
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | lte p | merged | gte q = branch ll (item lVal (suc (rank merged))) merged
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p with mergeTree l rr
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p | merged with ord (rank rl) (rank merged)
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p | merged | lte q = branch merged (item rVal (suc (rank rl))) rl
mergeTree l@(branch ll (item lVal lRank) lr) r@(branch rl (item rVal rRank) rr)
  | gte p | merged | gte q = branch rl (item rVal (suc (rank merged))) merged

singletonTree : Nat -> HTree
singletonTree v = branch ⊥ (item v 1) ⊥

mergeKeepsOrd : (t l r : HTree) -> value t ≤ value l -> value t ≤ value r -> value t ≤ value (mergeTree l r)
mergeKeepsOrd t (leaf) (r) o p = p
mergeKeepsOrd t (l@(branch ll li lr)) (leaf) o p = o
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p with ord (value l) (value r)
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q with ord (rank ll) (rank (mergeTree lr r))
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q | lte s = o
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | lte q | gte s = o
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q with ord (rank rl) (rank (mergeTree l rr))
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q | lte s = p
mergeKeepsOrd t (l@(branch ll li lr)) (r@(branch rl ri rr)) o p | gte q | gte s = p

popTree : HTree -> Tuple Nat HTree
popTree leaf = ∞ ** ⊥
popTree (branch l (item v _) r) = v ** mergeTree l r

insertTree : Nat -> HTree -> HTree
insertTree n t = mergeTree (singletonTree n) t
