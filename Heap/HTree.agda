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

mergeInheritsLeftValue : (l r : HTree)-> value l ≤ value r -> value l ≡ value (mergeT l r)
mergeInheritsLeftValue (leaf) (r) p = infGteInf (value r) p
mergeInheritsLeftValue (l@(branch ll li lr)) (leaf) p = refl
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p with ord (value l) (value r)
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q with mergeT lr r
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q | m with ord (rank ll) (rank m)
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q | m | lte s = refl
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q | m | gte s = refl
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q with mergeT l rr
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q | m with ord (rank rl) (rank m)
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q | m | lte s = ordToEq (Item.value li) (Item.value ri) p q
mergeInheritsLeftValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q | m | gte s = ordToEq (Item.value li) (Item.value ri) p q

mergeInheritsRightValue : (l r : HTree)-> value r ≤ value l -> value r ≡ value (mergeT l r)
mergeInheritsRightValue (leaf) (r) p = refl
mergeInheritsRightValue (l@(branch ll li lr)) (leaf) p = infGteInf (Item.value li) p
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p with ord (value l) (value r)
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q with mergeT lr r
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q | m with ord (rank ll) (rank m)
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q | m | lte s = ordToEq (Item.value ri) (Item.value li) p q
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | lte q | m | gte s = ordToEq (Item.value ri) (Item.value li) p q
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q with mergeT l rr
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q | m with ord (rank rl) (rank m)
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q | m | lte s = refl
mergeInheritsRightValue (l@(branch ll li lr)) (r@(branch rl ri rr)) p | gte q | m | gte s = refl
