module Code.Inequality where

open import Library.Fun
open import Library.Bool
open import Library.Nat
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality

_≤ₘ_ : ℕ -> ℕ -> Set
x ≤ₘ y  = ∃[ z ] x + z == y

{-
  le-zero ---------------
            0 ≤ x

                x ≤ y  
  le-succ ---------------------
           succ(x) ≤ succ (y)
-}


infix 4 _≤_
data _≤_ : ℕ -> ℕ -> Set where
  le-zero : ∀{x : ℕ} -> 0 ≤ x
  le-succ : ∀{x y : ℕ} -> x ≤ y -> succ x ≤ succ y

_ : 2 ≤ 4
_ = le-succ (le-succ le-zero)

_ : 2 ≤ₘ 3
_ = 1 , refl

le-correct : ∀{x y : ℕ} -> x ≤ y -> x ≤ₘ y
le-correct le-zero = _ , refl
le-correct (le-succ a) = fst(le-correct a) , cong succ (snd(le-correct a))
