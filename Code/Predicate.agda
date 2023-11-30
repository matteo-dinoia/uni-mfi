module Code.Predicate where

open import Library.Fun
open import Library.Bool
open import Library.Nat
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality

half : ℕ -> ℕ -- parte intera di divisione per 2 (invertibile solo su i pari)
half zero            = zero
half (succ zero)     = zero
half (succ (succ x)) = succ (half x)

-- In agda un predicato su A ha tipo A -> Set
--Prima possibilità

even-p : ℕ -> Bool -- Stile programmazione
even-p zero            = true
even-p (succ zero)     = false
even-p (succ (succ x)) = even-p x

doublehalfeven : ∀{x : ℕ} -> (ev : even-p x == true) -> x == half x * 2 
doublehalfeven {zero} ev = refl
doublehalfeven {succ (succ x)} ev = cong (λ a -> succ (succ a)) (doublehalfeven ev)

even-m : ℕ -> Set
even-m x = ∃[ m ] x == m * 2

_ : even-m 4
_ = 2 , refl

_ : ¬ even-m 1 -- parentesi necessarie per splittare
_ = λ { (zero , ()) ; (succ x , ())}

doublehalfevenM : ∀{x : ℕ} -> (ev : even-m x) -> x == half x * 2 
doublehalfevenM (y , refl) = cong (_* 2) (lemma y)
  where
    lemma : ∀ (x : ℕ) -> x == half(x * 2)
    lemma zero = refl
    lemma (succ x) = cong succ (lemma x)


{-                                           even-i n 
     even-zero -------------   even-succ ---------------     
                 even-i 0                  even-i (2 + n)     -}

data Even-i : ℕ -> Set where -- con sistema di inferenza formale

  even-zero : --------------
                Even-i 0
                
  even-succ : ∀{n : ℕ}
              -> Even-i n
           --------------------
              ->  Even-i (2 + n)
  

_ : Even-i 4
_ = even-succ (even-succ even-zero)

_ : ¬ Even-i 1
_ = λ ()

doublehalfevenI : ∀{x : ℕ} (ev : Even-i x) -> x == half x * 2
doublehalfevenI even-zero = refl
doublehalfevenI (even-succ ev) = cong (succ ∘ succ) (doublehalfevenI ev)


-- ESERCIZI ----------------------------------
data Odd-i : ℕ -> Set where -- con sistema di inferenza formale

  odd-one : --------------
                Odd-i 1
                
  odd-succ : ∀{n : ℕ}
              -> Odd-i n
           --------------------
              ->  Odd-i (2 + n)
  

_ : Odd-i 5
_ = odd-succ (odd-succ odd-one)

_ : ¬ Odd-i 2
_ = λ { (odd-succ ()) }

even-or-odd : ∀(n : ℕ) -> Even-i n ∨ Odd-i n
even-or-odd zero = inl even-zero
even-or-odd (succ zero) = inr odd-one
even-or-odd (succ (succ x)) with even-or-odd x
... | inl p = inl (even-succ p)
... | inr p = inr (odd-succ p)

even-and-odd : ∀(x : ℕ) -> ¬ (Even-i x ∧ Odd-i x)
even-and-odd zero            (_  , ())
even-and-odd (succ zero)     (() , _ )
even-and-odd (succ (succ x)) (even-succ ev , odd-succ od) = even-and-odd x (ev , od)

even-p-i : ∀(x : ℕ) -> (even-p x == true) -> Even-i x
even-p-i zero ep = even-zero
even-p-i (succ (succ x)) ep = even-succ(even-p-i x ep)

even-i-m : ∀(x : ℕ) -> Even-i x -> even-m x
even-i-m zero ei = zero , refl
even-i-m (succ (succ x)) (even-succ ei) = (succ (fst (even-i-m x ei))) , cong (succ ∘ succ) (snd (even-i-m x ei))

even-m-p : ∀{x : ℕ} -> even-m x -> (even-p x == true)
even-m-p (y , refl) = lem y
  where
    lem : ∀(y : ℕ) -> even-p (y * 2) == true
    lem zero     = refl
    lem (succ y) = lem y

not-even : ∀(x : ℕ) -> ¬ Even-i x -> (x == 1 + half x * 2)
not-even zero ei = ex-falso (ei even-zero)
not-even (succ zero) ei = refl
not-even (succ (succ x)) ei = cong (succ ∘ succ) (not-even x λ { a -> ei (even-succ a)})

dec-evi : ∀(x : ℕ) -> Decidable (Even-i x)
dec-evi zero = yes even-zero
dec-evi (succ zero) = no λ ()
dec-evi (succ (succ x)) with dec-evi x
... | yes ok = yes (even-succ ok)
... | no nok = no λ { (even-succ a) → nok a}

yes-odd : ∀(x : ℕ) -> Odd-i x -> (x == 1 + half x * 2)
yes-odd x odi with dec-evi x
... | yes ok = ex-falso (even-and-odd x (ok , odi))
... | no nok = not-even x nok 
