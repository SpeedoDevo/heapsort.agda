module Heap.Item where

open import Agda.Builtin.Nat

record Item : Set where
  constructor item
  field
    value : Nat
    rank : Nat
