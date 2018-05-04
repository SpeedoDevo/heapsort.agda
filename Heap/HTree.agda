module Heap.HTree where

open import Agda.Builtin.Nat
open import Heap.Item
open import NatExt
open import Tree

HTree : Set
HTree = Tree Item

rank : HTree -> Nat
rank leaf = 0
rank (branch _ i _) = Item.rank i

value : HTree -> Nat
value leaf = ∞
value (branch _ i _) = Item.value i
