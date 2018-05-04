module Heap.IsLeftist where

open import Heap.HTree
open import Heap.Item
open import Ord
open import Tree

data _IsLeftist : HTree -> Set where
  leafIsLeftist : ⊥ IsLeftist
  branchIsLeftist : ∀ {l r i} -> l IsLeftist -> r IsLeftist
    -> rank r ≤ rank l
    -- -> Item.rank i ≡ 1 + (min (rank l) (rank r))
    -> (branch l i r) IsLeftist
