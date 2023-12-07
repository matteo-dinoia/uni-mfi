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
le-correct le-zero     = _ , refl
le-correct (le-succ a) = fst(le-correct a) , cong succ (snd(le-correct a))

le-complete : ∀{x y : ℕ} -> x ≤ₘ y -> x ≤ y
le-complete {zero} {.(zero + dif)} (dif , refl) = le-zero
le-complete {succ x} {.(succ x + dif)} (dif , refl) = le-succ (le-complete (dif , refl))

-- ORDINE: riflessiva, transitività e antisimmetria (ma considerando che a != b per antisimmeria)
le-refl : ∀{x : ℕ} -> x ≤ x
le-refl {zero}   = le-zero
le-refl {succ x} = le-succ le-refl

le-antisymm : ∀{x y : ℕ} -> x ≤ y -> y ≤ x -> x == y
le-antisymm le-zero le-zero = refl
le-antisymm (le-succ a) (le-succ b) = cong succ (le-antisymm a b)

le-trans : ∀{x y z : ℕ} -> x ≤ y -> y ≤ z -> x ≤ z
le-trans le-zero _ = le-zero
le-trans (le-succ p) (le-succ q) = le-succ (le-trans p q)

-- ORDINE è totale (dati a e b allora a ≤ b o b ≤ a) es non totale ⊂
le-total : ∀ (x y : ℕ) -> x ≤ y ∨ y ≤ x
le-total zero _            = inl le-zero
le-total _ zero            = inr le-zero
le-total (succ x) (succ y) with le-total x y
... | inl a = inl (le-succ a)
... | inr b = inr (le-succ b)


-- ESERCIZI
_≤?_ : ∀(x y : ℕ) -> Decidable(x ≤ y)
_≤?_ zero _            = yes le-zero
_≤?_ (succ x) zero     = no λ ()
_≤?_ (succ x) (succ y) with _≤?_ x y
... | inl gt = no λ { (le-succ le) → gt le}
... | inr le = yes (le-succ le)

min1 : ℕ -> ℕ -> ℕ
min1 zero _            = zero
min1 _ zero            = zero
min1 (succ x) (succ y) = succ(min1 x y)

max1 : ℕ -> ℕ -> ℕ
max1 zero y            = y
max1 x zero            = x
max1 (succ x) (succ y) = succ(max1 x y)

le-min : ∀{x y z : ℕ} -> x ≤ y -> x ≤ z -> x ≤ min y z
le-min le-zero le-zero = le-zero
le-min (le-succ dis1) (le-succ dis2) = le-succ (le-min dis1 dis2)

le-max : ∀{x y z : ℕ} -> x ≤ z -> y ≤ z -> max x y ≤ z
le-max le-zero le-zero = le-zero
le-max le-zero (le-succ dis2) = le-succ dis2
le-max (le-succ dis1) le-zero = le-succ dis1
le-max (le-succ dis1) (le-succ dis2) = le-succ(le-max dis1 dis2)

_<_ : ℕ -> ℕ -> Set
x < y = succ x ≤ y

lt-trans : ∀{x y z : ℕ} -> x < y -> y < z -> x < z
lt-trans (le-succ le-zero) (le-succ dis2) = le-succ le-zero
lt-trans (le-succ (le-succ dis1)) (le-succ dis2) = le-succ (lt-trans (le-succ dis1) dis2)

lt-irrefl : ∀{x : ℕ} -> ¬(x < x)
lt-irrefl {zero}      = λ ()
lt-irrefl {succ x}    = λ { (le-succ z) → lt-irrefl z}

