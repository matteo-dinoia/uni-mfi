module Code.LogicExistential where

open import Library.Fun
open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.Equality
--open import Library.Logic hiding (fst; snd; Σ)
--open import Library.Logic.Laws


{- Termini con che dipende dal termine
ma il tipo non dipende realmente dal tipo
    x : A |- B : A -> Set
    ---------------------
     x : A |- B x : Set
     -----------------
      Π (x : A) (B x)   possiamo leggerlo come ∀-}

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : ∀(x : A) -> B x -> Σ A B      --coppia dipendente x : A, B x : A->Set

_×_ : Set -> Set -> Set
A × B = Σ A λ _ -> B -- dipendenza vuota

ℕ⁺ : Set --coppia di naturali e dimostrazione
ℕ⁺ = Σ ℕ (_!=  0)  

∃ : ∀ {A : Set} (B : A -> Set) -> Set --posso nasconere A
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x -> B) = ∃ [ x ] B


