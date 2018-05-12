module Sort.Permutation.Tree where

open import Agda.Builtin.Nat

open import Heap
open import Heap.HTree
open import Heap.Item
open import Ord
open import Tree

data TContains (v : Nat) : HTree -> Set where
  here : ∀ {l w r} -> TContains v (branch l (item v w) r)
  toLeft : ∀ {l i r} -> TContains v l -> TContains v (branch l i r)
  toRight : ∀ {l i r} -> TContains v r -> TContains v (branch l i r)

singletonContains : ∀ {n} -> TContains n (singletonHTree n)
singletonContains {n} = here {n} {⊥} {1} {⊥}

-- if a tree contains x and it is merged with another tree then the merged tree will contain x too
mergeContainsLeft : ∀ {x l r} -> TContains x l -> TContains x (mergeTree l r)
mergeContainsLeft {_} {leaf} ()
mergeContainsLeft {_} {branch _ _ _} {leaf} p = p
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here with ord x (value r)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o with mergeTree lr r
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o | m with ord (rank ll) (rank m)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o | m | lte n = here
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o | m | gte n = here
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | gte o with mergeContainsLeft {x} {l} {rr} here | ord (rank rl) (rank (mergeTree l rr))
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | gte o | m | lte n = toLeft m
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | gte o | m | gte n = toRight m

mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) with ord (value l) (value r)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o with mergeTree lr r
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o | m with ord (rank ll) (rank m)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o | m | lte n = toRight p
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o | m | gte n = toLeft p
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | gte o with ord (rank rl) (rank (mergeTree l rr))
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | gte o | lte n = toLeft (mergeContainsLeft {x} {l} {rr} (toLeft p))
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | gte o | gte n = toRight (mergeContainsLeft {x} {l} {rr} (toLeft p))

mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) with ord (value l) (value r)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | lte o with ord (rank ll) (rank (mergeTree lr r))
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | lte o | lte n = toLeft (mergeContainsLeft {x} {lr} {r} p)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | lte o | gte n = toRight (mergeContainsLeft {x} {lr} {r} p)
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | gte o with ord (rank rl) (rank (mergeTree l rr))
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | gte o | lte n = toLeft (mergeContainsLeft {x} {l} {rr} (toRight p))
mergeContainsLeft {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | gte o | gte n = toRight (mergeContainsLeft {x} {l} {rr} (toRight p))

-- if a tree contains x and it is merged with another tree then the merged tree will contain x too
mergeContainsRight : ∀ {x l r} -> TContains x r -> TContains x (mergeTree l r)
mergeContainsRight {_} {leaf} {r} p = p
mergeContainsRight {_} {l = branch _ _ _} {leaf} ()
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here with ord (value l) x
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o with ord (rank ll) (rank (mergeTree lr r))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o | lte n = toLeft (mergeContainsRight {x} {lr} {r} here)
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | lte o | gte n = toRight (mergeContainsRight {x} {lr} {r} here)
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | gte o with ord (rank rl) (rank (mergeTree l rr))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | gte o | lte n = here
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} here | gte o | gte n = here

mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) with ord (value l) (value r)
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o with ord (rank ll) (rank (mergeTree lr r))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o | lte n = toLeft (mergeContainsRight {x} {lr} {r} (toLeft p))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | lte o | gte n = toRight (mergeContainsRight {x} {lr} {r} (toLeft p))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | gte o with ord (rank rl) (rank (mergeTree l rr))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | gte o | lte n = toRight p
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toLeft p) | gte o | gte n = toLeft p

mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) with ord (value l) (value r)
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | lte o with ord (rank ll) (rank (mergeTree lr r))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | lte o | lte n = toLeft (mergeContainsRight {x} {lr} {r} (toRight p))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | lte o | gte n = toRight (mergeContainsRight {x} {lr} {r} (toRight p))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | gte o with ord (rank rl) (rank (mergeTree l rr))
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | gte o | lte n = toLeft (mergeContainsRight {x} {l} {rr} p)
mergeContainsRight {x} {l@(branch ll _ lr)} {r@(branch rl _ rr)} (toRight p) | gte o | gte n = toRight (mergeContainsRight {x} {l} {rr} p)
