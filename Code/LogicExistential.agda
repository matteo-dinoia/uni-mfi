module Code.LogicExistential where

open import Library.Fun
open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.Equality
open import Library.Logic hiding (∃; ∃-syntax; fst; snd; Σ)
open import Library.Logic.Laws

{-Tipi della coppia dipendente
  un abitante di Σ A B è una coppia (a, p) dove se a : A allora p : B a
-}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : ∀(x : A) → B x → Σ A B

-- Esempi ---------------------------------------------------
_×_ : Set → Set → Set -- Tipo coppia non dipendente
A × B = Σ A (λ _ → B) --Dipendenza vuota

fst : ∀{A : Set} → {B : A → Set} → Σ A B → A
fst (x , _) = x

snd : ∀{A : Set} → {B : A → Set} → (p : Σ A B) → B (fst p)
snd (_ , y) = y

ℕ⁺ : Set  -- il tipo dei naturali diversi da 0
ℕ⁺ = Σ ℕ (_!= 0) -- abbrevia λ z -> z != 0

_ : ℕ⁺
_ = 1 , (λ ())

-- Uso su liste ---------------------------------------------
List⁺ : Set -> Set
List⁺ A = Σ (List A) (_!= []) -- abbrevia λ z -> z != []


head : ∀{A : Set} -> List⁺ A -> A
head ([] , nempty) = ex-falso (nempty refl)
head (x :: xs , _) = x

tail : ∀{A : Set} -> List⁺ A -> List A
tail ([] , nempty) = ex-falso (nempty refl)
tail (x :: xs , _) = xs 

-- Uso come esistenza ---------------------------------------
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

pred : ∀ (p : ℕ⁺) -> ∃[ x ] (fst p == succ x) 
pred (zero , nzero)   = ex-falso (nzero refl)
pred (succ x , nzero) = x , refl




-- ESERCIZI ---------------------------------------------------
pred' : ∀(x : ℕ) -> x == 0 ∨ (∃[ y ] (x == succ y))
pred' zero = inl refl
pred' (succ x) = inr (x , refl)

ℕ2 : Set
ℕ2 = Σ ℕ λ x -> x != 0 ∧ x != 1

succ2 : ℕ2 -> ℕ2
succ2 (x , nzero , none) = succ x , (λ ()) , λ { refl → nzero refl}

last-view : ∀{A : Set} (xs : List A) -> xs != [] -> ∃[ ys ] ∃[ y ] (xs == ys ++ [ y ])
last-view {A} [] nempty        = ex-falso (nempty refl)
last-view (x :: []) nempty     = [] , x , refl
last-view {A} (x :: z ::  xs) nempty with last-view (z :: xs) (λ ())
... | (rest , (last , eq)) = x :: rest , (last , cong (x ::_) eq ) 

half : ∀(x : ℕ) -> ∃[ y ] ∃[ z ] (x == y * 2 + z ∧ (z == 0 ∨ z == 1))
half zero = zero , (zero , (refl , inl refl))
half (succ zero) = zero , ((succ zero) , (refl , inr refl))
half (succ (succ x)) with half x
... | d , r , eq , zr = succ d , r , cong (succ ∘ succ) eq , zr
