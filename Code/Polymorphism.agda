module Code.Polymorphism where

open import Library.Bool
open import Library.Nat

-- Potremmo scrivere varie funzione per ogni tipo ma è spreco
id : ∀(A : Set) -> A -> A
id A x = x

a : ℕ -> ℕ -- id su interi
a x = id ℕ x

b : ℕ -> ℕ -- id su interi
b x = id _ x -- lo inferisce che è ℕ


id2 : ∀{A : Set} -> A -> A -- di default lo immagina
id2 x = x

forza : ℕ -> ℕ
forza x = id2 {ℕ} x

-- ESERCIZI
flip : ∀{A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f b a = f a b

_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
_∘_ f g x = f (g x)

apply : ∀{A B : Set} -> (A -> B) -> A -> B
apply f a = f a
