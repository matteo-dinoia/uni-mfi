module Code.ExtrinsicInsertSort where

open import Library.Logic
open import Library.Nat
open import Library.List
open import Library.LessThan renaming (_<=_ to _≤_)
open import Library.List.Permutation


data LowerBound (x : ℕ) : List ℕ → Set where

  lb-[] : ---------------
          LowerBound x []

  lb-:: : ∀{y : ℕ} {ys : List ℕ}
        → x ≤ y
        → LowerBound x ys
        ------------------------
        → LowerBound x (y :: ys)


lower-lower-bound : ∀{x y : ℕ} {ys : List ℕ} →
        x ≤ y → LowerBound y ys → LowerBound x ys

lower-lower-bound x≤y lb-[]              = lb-[]
lower-lower-bound x≤y₁ (lb-:: y₁≤y lb-[]) =
      lb-:: (le-trans x≤y₁ y₁≤y) lb-[]

lower-lower-bound x≤y (lb-:: y≤z z≤ys) =
      lb-:: (le-trans x≤y y≤z) (lower-lower-bound x≤y z≤ys)

data Sorted : List ℕ → Set where
  sorted-[] : ---------
              Sorted []
              
  sorted-:: : ∀{x : ℕ} {xs : List ℕ}
           → LowerBound x xs
           → Sorted xs
           ------------------
           → Sorted (x :: xs)

SortingFunction : Set
SortingFunction = ∀(xs : List ℕ) → ∃[ ys ] ys # xs ∧ Sorted ys


-- CODICE EFFETTIVO LEZIONE --------------------------------------

--noi sappiamo che ordinamento su ℕ è totale (le-total)
insert : ℕ -> List ℕ -> List ℕ
insert x []        = [ x ]
insert x (y :: ys) with le-total x y
...| inl x<=y = x :: y :: ys
...| inr y<=x = y :: insert x ys

insertion-sort : List ℕ -> List ℕ
insertion-sort [] = []
insertion-sort (x :: xs) = insert x (insertion-sort xs)

lower-bound-insert : ∀{x y : ℕ} {ys : List ℕ} -> x ≤ y -> LowerBound x ys -> LowerBound x (insert y ys)
lower-bound-insert dis lb-[] = lb-:: dis lb-[]
lower-bound-insert {x} {y} {z :: ys} x≤y (lb-:: x≤z x≤ys) with le-total y z
... | inl y≤z = lb-:: x≤y (lb-:: x≤z x≤ys)
... | inr z≤y = lb-:: x≤z (lower-bound-insert x≤y x≤ys)

sorted-insert : ∀(x : ℕ) (ys : List ℕ) -> Sorted ys -> Sorted (insert x ys)
sorted-insert x [] sorted-[] = sorted-:: lb-[] sorted-[]
sorted-insert x (y :: ys) (sorted-:: y≤ys sort) with le-total x y
... | inl x≤y = sorted-:: (lb-:: x≤y (lower-lower-bound x≤y y≤ys)) (sorted-:: y≤ys sort)
... | inr y≤x = sorted-::  (lower-bound-insert y≤x y≤ys)  (sorted-insert x ys sort)

sorted-insertion-sort : ∀(xs : List ℕ) -> Sorted (insertion-sort xs)
sorted-insertion-sort []        = sorted-[]
sorted-insertion-sort (x :: xs) = sorted-insert x (insertion-sort xs) (sorted-insertion-sort xs)

--PERMUTATION
insert-permutation : ∀(x : ℕ)(ys : List ℕ) -> insert x ys # x :: ys
insert-permutation x [] = #refl
insert-permutation x (y :: ys) with le-total x y
... | inl x≤y = #refl
... | inr y≤x = #trans (#cong (insert-permutation x ys)) #swap

insertion-sort-permutation : ∀(xs : List ℕ) -> insertion-sort xs # xs
insertion-sort-permutation [] = #refl
insertion-sort-permutation (x :: xs) = #trans
                                (insert-permutation x (insertion-sort xs))
                                  (#cong (insertion-sort-permutation xs))

verified-insertion-sort : SortingFunction
verified-insertion-sort xs = insertion-sort xs , ((insertion-sort-permutation xs) , (sorted-insertion-sort xs))
