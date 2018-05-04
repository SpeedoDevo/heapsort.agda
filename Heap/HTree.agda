module Heap.HTree where

open import Agda.Builtin.Nat
open import Agda.Builtin.Size
open import Heap.Item
open import NatExt
open import Tree

HTree : {i : Size} -> Set
HTree {i} = Tree {i} Item

rank : HTree -> Nat
rank leaf = 0
rank (branch _ i _) = Item.rank i

value : HTree -> Nat
value leaf = ∞
value (branch _ i _) = Item.value i
