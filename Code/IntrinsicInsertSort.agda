module Code.IntrinsicInsertSort where

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


lower-bound-perm : ∀{x : ℕ} {xs ys : List ℕ} →
                      ys # xs → LowerBound x xs → LowerBound x ys
lower-bound-perm #refl                 x≤xs = x≤xs

lower-bound-perm #swap (lb-:: x (lb-:: x₂≤x₃ x≤xs)) =
       lb-:: x₂≤x₃ (lb-:: x x≤xs)
                       
lower-bound-perm (#cong ys#xs) (lb-:: x x≤xs) =
       lb-:: x (lower-bound-perm ys#xs x≤xs)

lower-bound-perm (#trans ys#xs ys#xs₁) x≤xs =
       lower-bound-perm ys#xs (lower-bound-perm ys#xs₁ x≤xs)
       


-- ACTUAL FILE --------------------------------

intrinsic-insert : ∀(x : ℕ)(ys : List ℕ) -> Sorted ys ->
                       ∃[ zs ] (zs # x :: ys ∧ Sorted zs)
intrinsic-insert x [] sorted-[] = [ x ] , (#refl , (sorted-:: lb-[] sorted-[]))
intrinsic-insert x (y :: ys) (sorted-:: y≤ys sort_ys) with le-total x y
... | inl x≤y = (x :: y :: ys) ,
                  (#refl , (sorted-:: (lb-:: x≤y (lower-lower-bound x≤y y≤ys))
                  (sorted-:: y≤ys sort_ys))) 
... | inr y≤x with intrinsic-insert x ys sort_ys
--sottocase
... | zs , perm_zs , sorted_z = (y :: zs) ,
               (#trans (#cong perm_zs) #swap ,
               sorted-:: (lower-bound-perm perm_zs (lb-:: y≤x y≤ys)) sorted_z)

verified-insertion-sort : SortingFunction
verified-insertion-sort [] = [] , (#refl , sorted-[])
verified-insertion-sort (x :: xs) with verified-insertion-sort xs
... | zs , perm_zs , sort_zs with intrinsic-insert x zs sort_zs
... | x_zs , perm_x_zs , sort_x_zs = x_zs , (#trans perm_x_zs (#cong perm_zs) , sort_x_zs)
