module Ord.Heap where

open import Heap.Item
open import Ord
open import Tree

data _≤v_ : Item -> Tree Item -> Set where
  ≤vLeaf : ∀ {i} -> i ≤v ⊥
  zero≤v : ∀ {r t} -> item 0 r ≤v t
  prove≤v : ∀ {val1 rank1 val2 rank2 l r} -> val1 ≤ val2 -> (item val1 rank1) ≤v branch l (item val2 rank2) r

data _≤r_ : Item -> Tree Item -> Set where
  ≤rLeaf : ∀ {i} -> i ≤r ⊥
  zero≤r : ∀ {v t} -> item v 0 ≤r t
  prove≤r : ∀ {val1 rank1 val2 rank2 l r} -> rank1 ≤ rank2 -> (item val1 rank1) ≤r branch l (item val2 rank2) r
