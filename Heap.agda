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

data _ILH : (t : HTree) -> Set where
  ilh : (t : HTree) -> t IH -> t IL -> t ILH

merge : {l r : HTree} -> l ILH -> r ILH -> (mergeT l r) ILH
merge (ilh lt lih lil) (ilh rt rih ril) = ilh (mergeT lt rt) (mergeIH lih rih) (mergeIL lil ril)
