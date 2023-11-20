module Code.Connectives where

open import Library.Fun
open import Library.Nat
open import Library.Bool
open import Library.Equality
open import Library.List

-- AND ---------------------------------------------
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

infixr 3 _∧_
infixr 4 _,_

fst : ∀{A B : Set} -> A ∧ B -> A
fst (x , _) = x

snd : ∀{A B : Set} -> A ∧ B -> B
snd (_ , y) = y

∧-comm : ∀{A B : Set} -> A ∧ B  -> B ∧ A
∧-comm (a , b) = b , a

-- OR -----------------------------------------------
data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B

infixr 2 _∨_

∨-elim : ∀{A B C : Set} -> (A -> C) -> (B -> C) -> A ∨ B -> C
∨-elim f g (inl x) = f x
∨-elim f g (inr x) = g x

∨-comm : ∀{A B : Set} -> A ∨ B -> B ∨ A
∨-comm = ∨-elim inr inl

-- ⊤ e ⊥ --------------------------------------------
data ⊤ : Set where -- ⊤ si scrive \top
  <> : ⊤

data ⊥ : Set where -- ⊥ si scrive \bot
  
ex-falso : ∀{A : Set} -> ⊥ -> A
ex-falso ()

¬_ : Set -> Set -- ¬ si scrive \neg
¬ A = A -> ⊥  --anche Classicamente ¬ A <==> A ⊃ ⊥


contrapositive : ∀ {A B : Set} -> (A -> B) -> ¬ B -> ¬ A
contrapositive f p a = p (f a)

double-negation : ∀{A : Set} -> A -> ¬ ¬ A  -- ≡ A -> (A->⊥) -> ⊥
double-negation a f = f a 

-- Classicamente ¬ A ∨ A cosidetta terzo escluso ma non vale perchè potrei decidere se vale A
-- Ma noi sappiamo che formule possono essere indecidibili

Decidable : Set -> Set
Decidable A = ¬ A ∨ A

-- pattern è primitiva di abbreviazione
pattern yes x = inr x
pattern no x = inl x

Bool-eq-decidable : ∀(x y : Bool) -> Decidable (x == y)
Bool-eq-decidable true true = yes refl
Bool-eq-decidable true false = no λ () -- ¬(true == false) ≡ true == false -> ⊥ 
Bool-eq-decidable false true = no λ () -- mi serve una funzione di nessun caso (/niente)
Bool-eq-decidable false false = yes refl

Nat-eq-decidable : ∀(x y : ℕ) -> Decidable (x == y)
Nat-eq-decidable zero zero = yes refl
Nat-eq-decidable zero (succ y) = no λ ()
Nat-eq-decidable (succ x) zero = no λ ()
Nat-eq-decidable (succ x) (succ y) with Nat-eq-decidable x y
... | yes refl = yes refl -- ok C-c C-c => unico caso è refl
... | no nok   = no (λ {refl -> nok refl}) --succ x == succ y -> (x == y -> ⊥) succ x == succ y
                       -- uso λ {z -> ?} poi C-c C-c

List-eq-decidable : ∀{A : Set} -> (∀(x y : A) -> Decidable (x == y)) -> (xs ys : List A) -> Decidable (xs == ys)
List-eq-decidable _==?_ [] [] = yes refl
List-eq-decidable _==?_ [] (x :: ys) = no λ ()
List-eq-decidable _==?_ (x :: xs) [] = no λ () -- tattici sono macro per euristiche di prossimo passaggio
List-eq-decidable _==?_ (x :: xs) (y :: ys) with x ==? y | List-eq-decidable _==?_ xs ys
... | no neq | _          = no λ { refl → neq refl}
... | yes _ | no neq      = no λ { refl → neq refl} 
... | yes refl | yes refl = yes refl





-- ESERCIZI
∧-idem-l : ∀{A : Set} -> A ∧ A -> A
∧-idem-l (a1 , a2) = a1
∧-idem-r : ∀{A : Set} -> A -> A ∧ A
∧-idem-r a = a , a

∨-idem-l : ∀{A : Set} -> A ∨ A -> A
∨-idem-l (inl x) = x
∨-idem-l (inr x) = x
∨-idem-r : ∀{A : Set} -> A -> A ∨ A
∨-idem-r a = inl a

∧∨-dist-l : ∀{A B C : Set} -> A ∧ (B ∨ C) -> (A ∧ B) ∨ (A ∧ C)
∧∨-dist-l (a , bc) = ∨-elim (λ {b -> inl (a , b) }) (λ {c -> inr (a , c) }) bc
∧∨-dist-r : ∀{A B C : Set} -> (A ∧ B) ∨ (A ∧ C) ->  A ∧ (B ∨ C)
∧∨-dist-r x = ∨-elim (λ {ab -> fst ab , inl (snd ab)}) ( (λ {ac -> fst ac , inr (snd ac)})) x

∧-unit-ll : ∀{A : Set} -> ⊤ ∧ A -> A
∧-unit-ll (<> , a) = a
∧-unit-lr : ∀{A : Set} -> A -> ⊤ ∧ A
∧-unit-lr a = (<> , a)
∧-unit-rl : ∀{A : Set} -> A ∧ ⊤ -> A
∧-unit-rl (a , <>) = a
∧-unit-rr : ∀{A : Set} -> A -> A ∧ ⊤
∧-unit-rr a = (a , <>)

∨-⊤-ll : ∀{A : Set} -> ⊤ ∨ A -> ⊤
∨-⊤-ll x = <>
∨-⊤-lr : ∀{A : Set} -> ⊤ -> ⊤ ∨ A
∨-⊤-lr <> = inl <>
∨-⊤-rl : ∀{A : Set} -> A ∨ ⊤ -> ⊤
∨-⊤-rl x = <>
∨-⊤-rr : ∀{A : Set} -> ⊤ -> A ∨ ⊤
∨-⊤-rr <> = inr <>

∨-unit-ll : ∀{A : Set} -> ⊥ ∨ A -> A
∨-unit-ll (inr a) = a
∨-unit-lr : ∀{A : Set} -> A -> ⊥ ∨ A
∨-unit-lr a = inr a
∨-unit-rl : ∀{A : Set} -> A ∨ ⊥ -> A
∨-unit-rl (inl a) = a
∨-unit-rr : ∀{A : Set} -> A -> A ∨ ⊥
∨-unit-rr a = inl a

∧-⊥-ll : ∀{A : Set} -> ⊥ ∧ A -> ⊥
∧-⊥-ll (x , y) = x
∧-⊥-lr : ∀{A : Set} -> ⊥ -> ⊥ ∧ A
∧-⊥-lr x = x , ex-falso x
∧-⊥-rl : ∀{A : Set} -> A ∧ ⊥ -> ⊥
∧-⊥-rl (x , y) = y
∧-⊥-rr : ∀{A : Set} -> ⊥ -> A ∧ ⊥
∧-⊥-rr x = ex-falso x , x 

Bool-∨ : ∀(b : Bool) -> (b == true) ∨ (b == false)
Bool-∨ true  = inl refl
Bool-∨ false = inr refl

-- ALTRI ES
ntop : ¬ ⊤ -> ⊥ -- (T -> ⊥) -> ⊥ 
ntop p = p <>

demorgan-∨l : ∀{A B : Set} ->  ¬ A ∨ ¬ B -> ¬ (A ∧ B)
demorgan-∨l (inl x) (a , b) = x a
demorgan-∨l (inr x) (a , b) = x b

demorgan-∧l : ∀{A B : Set} ->  ¬ A ∧ ¬ B -> ¬ (A ∨ B)
demorgan-∧l (na , nb) (inl x) = na x
demorgan-∧l (na , nb) (inr x) = nb x

--demorgan-∨r : ∀{A B : Set} -> ¬ (A ∧ B) ->  ¬ A ∨ ¬ B -- NO

demorgan-∧r : ∀{A B : Set} -> ¬ (A ∨ B) -> ¬ A ∧ ¬ B 
demorgan-∧r naob = (λ {a -> naob (inl a)}) , λ {b -> naob (inr b)}

{-
                [A]                            [B]
               ----- ∨ I                     ------ ∨ I
 [¬ (A ∨ B)]   A ∨ B            [¬ (A ∨ B)]   A ∨ B 
  ------------------- ¬E      ---------------------- ¬E
      ⊥                          ⊥
     ----- ¬ I                  ----- ¬ I
      ¬ A                        ¬ B
      --------------------------------- ∧ I
          ¬ A ∧ ¬ B
        ---------------------- → I
          ¬ (A ∨ B) -> ¬ A ∨ ¬ B

-}

--nndec : ∀{A : Set} -> ¬ ¬ Decidable A
--nndec nda = {!!} 


--em-dn : (∀{A : Set} -> ¬ A ∨ A) -> ∀{A : Set} -> ¬ ¬ A -> A
--em-dn t {A} p = {!!}

--dn-em : (∀{A : Set} -> (¬ ¬ A -> A)) -> ∀{A : Set} -> Decidable A
--dn-em t = {!!}

