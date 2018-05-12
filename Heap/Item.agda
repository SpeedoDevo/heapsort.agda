module Heap.Item where

open import Agda.Builtin.Nat

-- this really should be replaced with Tuple
record Item : Set where
  constructor item
  field
    value : Nat
    rank : Nat
