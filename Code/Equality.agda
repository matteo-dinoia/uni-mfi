module Code.Equality where

open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Logic

infix 4 _==_

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

_ : not true == false
_ = refl

symm : ∀{A : Set} {x y : A} -> x == y -> y == x
symm {A} {x} {.x} refl = refl -- dot pattern -> unificato i tipi
-- semplice è symm refl = refl 

tran : ∀{A : Set} {x y z : A} -> x == y -> y == z -> x == z
tran refl refl = refl

cong : ∀{A B : Set} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong f refl = refl


-- ESERCIZI ------------------------------------------------------
succ-injective : ∀{x y : ℕ} -> succ x == succ y -> x == y
succ-injective refl = refl

::-injective : ∀{A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys -> x == y ∧ xs == ys
::-injective refl = refl , refl

cong2 : ∀{A B C : Set} (f : A -> B -> C) {x y : A} {u v : B} -> x == y -> u == v -> f x u == f y v
cong2 f refl refl = refl

_!=_ : ∀{A : Set} -> A -> A -> Set
x != y = ¬ (x == y)

zero-succ : ∀{x : ℕ} -> zero != succ x
zero-succ = λ ()

ne-ne : ∀{x y : ℕ} -> succ x != succ y -> x != y
ne-ne neqs eq = neqs (cong succ eq)
