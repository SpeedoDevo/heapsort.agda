module Sort.Permutation where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Heap
open import Heap.HTree
open import Heap.IsHeap
open import Heap.IsLeftist
open import Heap.Item
open import Ord
open import Sort.Sort
open import Tree

data _+_~_ (x : Nat) : List Nat -> List Nat -> Set where
  here : ∀ {xs} -> x + xs ~ (x ∷ xs)
  there : ∀ {y xs xxs} -> (p : x + xs ~ xxs) -> x + (y ∷ xs) ~ (y ∷ xxs)

data IsPermutation : List Nat -> List Nat -> Set where
  [] : IsPermutation [] []
  _∷_ : ∀ {x xs ys xys} -> (p : x + ys ~ xys) -> (ps : IsPermutation xs ys) -> IsPermutation (x ∷ xs) (xys)

lemma3 : ∀ {x xs} -> x + [] ~ xs -> xs ≡ (x ∷ [])
lemma3 here = refl

lemma2 : ∀ {x y xs xys} -> y + x ∷ xs ~ xys -> x + y ∷ xs ~ xys
lemma2 {x} {y} {xs} {.(y ∷ x ∷ xs)} here = there here
lemma2 {x} {y} {xs} {.x ∷ []} (there ())
lemma2 {x} {_} {[]} {.x ∷ _ ∷ _} (there here) = here
lemma2 {x} {_} {x₁ ∷ xs} {.x ∷ _ ∷ _} (there here) = ?
lemma2 {x} {y} {x₁ ∷ xs} {.x ∷ _ ∷ _} (there (there p)) = ?
-- lemma2 {x} {y} {y2 ∷ xs2} {x ∷ y2 ∷ xys2}
-- lemma2 {y} {y} {y2 ∷ xs2} {y ∷ y2 ∷ xys2} (there p)


lemma : ∀ {x y xs} -> y + x ∷ xs ~ (x ∷ sort (y ∷ xs)) -> x + y ∷ xs ~ sort (x ∷ y ∷ xs)
lemma {x} {y} {xs} p = {!   !}

sortInsertsSomehere : ∀ {x xs} -> x + xs ~ sort (x ∷ xs)
sortInsertsSomehere {x} {[]} = here
sortInsertsSomehere {x} {y ∷ xs} = {! there {y} {x} {xs} {?} p  !}
  where p = sortInsertsSomehere {y} {xs}

sortIsPermutation : ∀ {xs} -> IsPermutation xs (sort xs)
sortIsPermutation {[]} = []
sortIsPermutation {x ∷ xs} = {!   !}

-- (p : x + ys ~ xys) -> (ps : IsPermutation xs ys) -> IsPermutation (x ∷ xs) (xys)
--                                                        IsPermutation (x ∷ xs) (sort (x ∷ xs))
-- xys == sort x :: xs
-- ys == xs
-- p : x + xs ~ sort x :: xs -> ps : IsPermutation xs xs
