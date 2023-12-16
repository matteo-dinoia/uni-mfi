module Code.SortedLists where

open import Library.Fun
open import Library.Nat
open import Library.LessThan
open import Library.Logic
open import Library.Equality
open import Library.List using (List; []; _::_; [_]; reverse; _++_)
open import Library.List.Properties
open import Library.List.Permutation hiding (_#_; #symm; #push)

-- Specifica alg. di ordinamento liste
--vogliamo qualcosa tiposort : List ℕ -> SortedPermutationList ℕ

data LowerBound (x : ℕ) : List ℕ -> Set where
     lb-[] : -----------------------
               LowerBound x []
     lb-:: : ∀{y : ℕ} {ys : List ℕ} ->
                      x <= y    ->     LowerBound x ys ->
                    --------------------------------------
                           LowerBound x (y :: ys)


data Sorted : List ℕ -> Set where
  sorted-[] : -------------------------
                   Sorted []
  sorted-:: : ∀{x : ℕ} {xs : List ℕ} ->
                    LowerBound x xs    ->   Sorted xs ->
                   -------------------------------------------
                               Sorted (x :: xs)


lower-lower-bound : ∀{x y : ℕ} {ys : List ℕ} -> x <= y -> LowerBound y ys -> LowerBound x ys
lower-lower-bound dis lb-[] = lb-[]
lower-lower-bound dis (lb-:: dis2 low) = lb-:: (le-trans dis dis2) (lower-lower-bound dis low)


singleton-sorted : ∀(x : ℕ) -> Sorted [ x ]
singleton-sorted x = sorted-:: lb-[] sorted-[]

-- definiamo il predicato xs # ys che significa una è permutazione dell'altra
infix  4 _#_

data _#_ {A : Set} : List A -> List A -> Set where
  #refl  : {xs : List A} -> xs # xs
  #swap  : {x y : A} {xs : List A} -> x :: y :: xs # y :: x :: xs
  #cong  : {x : A} {xs ys : List A} -> xs # ys -> x :: xs # x :: ys
  #trans : {xs ys zs : List A} -> xs # ys -> ys # zs -> xs # zs

_ : 1 :: 2 :: 3 :: [] # 3 :: 2 :: 1 :: []
_ = #trans (#trans #swap (#cong #swap))  #swap

-- E' relazione di equivalenza
#symm : ∀{A : Set} {xs ys : List A} -> xs # ys -> ys # xs
#symm #refl               = #refl
#symm #swap               = #swap
#symm (#cong perm)        = #cong (#symm perm)
#symm (#trans perm perm₁) = #trans (#symm perm₁) (#symm perm)

SortingFunction : Set
SortingFunction = ∀(xs : List ℕ) -> ∃[ ys ] (ys # xs ∧ Sorted ys)


-- ESERCIZI --------------------------------------------------------
lower-bound-permutation : ∀{x : ℕ} {xs ys : List ℕ} -> ys # xs ->
                          LowerBound x xs -> LowerBound x ys
lower-bound-permutation #refl lower = lower
lower-bound-permutation #swap (lb-:: dis1 (lb-:: dis2 lower)) = lb-:: dis2 (lb-:: dis1 lower)
lower-bound-permutation (#cong perm) (lb-:: dis lower) = lb-:: dis (lower-bound-permutation perm lower)
lower-bound-permutation (#trans perm1 perm2) lower =
                  (lower-bound-permutation perm1 (lower-bound-permutation perm2 lower ))


data HeadLowerBound : ℕ -> List ℕ -> Set where
  hlb-[] : ∀{x : ℕ} -> HeadLowerBound x []
  hlb-:: : ∀{x y : ℕ} {ys : List ℕ} -> x <= y -> HeadLowerBound x (y :: ys)

data Sorted' : List ℕ -> Set where
  sorted-[] : Sorted' []
  sorted-:: : ∀{x : ℕ} {xs : List ℕ} -> HeadLowerBound x xs -> Sorted' xs -> Sorted' (x :: xs)

Sorted->Sorted' : ∀{xs : List ℕ} -> Sorted xs -> Sorted' xs
Sorted->Sorted' sorted-[] = sorted-[]
Sorted->Sorted' (sorted-:: dis sort) = sorted-:: (lemma dis) (Sorted->Sorted' sort)
  where
    lemma :  ∀{x : ℕ} {xs : List ℕ} -> LowerBound x xs ->  HeadLowerBound x xs
    lemma lb-[] = hlb-[]
    lemma (lb-:: dis low) = hlb-:: dis

Sorted'->Sorted : ∀{xs : List ℕ} -> Sorted' xs -> Sorted xs
Sorted'->Sorted sorted-[] = sorted-[]
Sorted'->Sorted (sorted-:: dis sort') = sorted-:: (lemma dis sort') (Sorted'->Sorted sort')
  where
    lower : ∀{x y : ℕ} {ys : List ℕ} -> x <= y -> HeadLowerBound y ys -> HeadLowerBound x ys
    lower dis hlb-[] = hlb-[]
    lower dis (hlb-:: dis2) = hlb-:: (le-trans dis dis2)

    lemma :  ∀{x : ℕ} {xs : List ℕ} -> HeadLowerBound x xs -> Sorted' xs -> LowerBound x xs
    lemma hlb-[] sort = lb-[]
    lemma (hlb-:: dis) (sorted-:: low sort) = lb-:: dis (lemma (lower dis low) sort)


#push : ∀{A : Set} (x : A) (xs ys : List A) -> x :: xs ++ ys # xs ++ x :: ys
#push x [] ys = #refl
#push x (x₁ :: xs) ys = #trans #swap (#cong (#push x xs ys))


#++ : ∀{A : Set} (xs ys : List A) -> xs ++ ys # ys ++ xs
#++ [] ys rewrite ++-unit-r ys = #refl
#++ (x :: xs) ys = #trans #refl (#trans (#cong (#++ xs ys)) (#push x ys xs))

#reverse : ∀{A : Set} (xs : List A) -> reverse xs # xs
#reverse [] = #refl
#reverse (x :: xs) = #trans (#++ (reverse xs) [ x ]) (#cong (#reverse xs))



