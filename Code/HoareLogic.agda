module Code.HoareLogic where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws 
open import Library.Equality
open import Library.Equality.Reasoning

open import Code.AexpBexp
open import Code.BigStep



Assn = State -> Set -- asserzione = predicato stato

data Triple : Set₁ where -- Ignoro 1 in set
     [_]_[_] : Assn -> Com -> Assn -> Triple

-- la tripla [ P ] c [ Q ] è valida
|=_ : Triple -> Set
|= [ P ] c [ Q ] = ∀{s t} -> P s -> ⦅ c , s ⦆ ⇒ t -> Q t



-- Lifting da Bexp a Assn
lift : Bexp -> Assn
lift b s = bval b s == true

-- Operazioni tra Assn
_∧'_ : Assn -> Assn -> Assn
P ∧' Q = λ s -> (P s ∧ Q s)

_==>_ : Assn -> Assn -> Assn
P ==> Q = λ s -> (P s -> Q s)

⊤' : Assn
⊤' = λ s -> ⊤ -- ⊤ scritto \top

-- Validità asserzione
⊨_ : Assn -> Set
⊨ P = ∀ s -> P s

-- Sostituzione
_⟨_/_⟩ : Assn -> Aexp -> Vname -> Assn
P ⟨ a / x ⟩ = λ s -> P (s [ x ::= (aval a s)])


{-
H-If
  [P ∧ b] c1 [Q]     [P ∧ ¬b] c2 [Q]
  ----------------------------------
     [P] IF b THEN c1 ELSE c2 [Q]

H-While (P è invariante e se termina soddisfa postcondizione)
           [P ∧ b] c [P] 
  ----------------------------------
       [P] WHILE b DO c [P ∧ ¬b]

Implicazione logica
  ⊨ P' ==> P      [P]  c [Q]     ⊨ Q ==> Q'
  -------------------------------------
            [P'] c [Q']
-} 
data |-_ : Triple -> Set₁ where
  H-Skip : ∀ {P}
         ----------------------
         -> |- [ P ] SKIP [ P ]
  H-Loc : ∀ {P a x}
         ---------------------- (risalgo da precondizione a post)
         -> |- [ P ⟨ a / x ⟩ ] x := a [ P ]
  -- 'a' sostituisce 'x' => non è più necessaria sostituzione dopo
  H-Comp : ∀ {P R Q c1 c2}
         -> |- [ P ] c1 [ R ]
         -> |- [ R ] c2 [ Q ]
         ----------------------
         -> |- [ P ] c1 :: c2 [ Q ]
  H-If : ∀ {P Q b c1 c2}  -- usa not di bexp (con 2 casi)
         -> |- [ P ∧' lift b ] c1 [ Q ]
         -> |- [ P ∧' lift (Not b) ] c2 [ Q ]
         ----------------------
         -> |- [ P ] IF b THEN c1 ELSE c2 [ Q ]
  H-While : ∀ {P b c} -- P precondizione e ¬b è postcondizione
         -> |- [ P  ∧' lift b ] c [ P ]
         ----------------------
         -> |- [ P ] WHILE b DO c [ P ∧' lift (Not b) ]
  -- Extra che non è strutturale ma serve comunque
  H-Conseq : ∀ {P' P Q Q' c}
         -> ⊨ (P' ==> P)       --usa validità asserzioni
         -> |- [ P ] c [ Q ]
         -> ⊨ (Q ==> Q')
         ----------------------
         -> |- [ P' ] c [ Q' ]


-- Esempio
X : Vname
X = Vn 0
Y : Vname
Y = Vn 1
Z : Vname
Z = Vn 2

_=='_ : Aexp -> Aexp -> Assn
a1 ==' a2 = λ s -> (aval a1 s == aval a2 s)

pr0-1 : |- [ V X ==' N 1 ]
           (Z := V X) :: (Y := V Z)
           [ V Y ==' N 1 ]
pr0-1 = H-Comp {V X ==' N 1} {V Z ==' N 1} {V Y ==' N 1} H-Loc H-Loc



-- Regole derivate
H-Str : ∀ {P' P Q c} -- Strenghten (know less of pre)
  -> ⊨ (P' ==> P)       
  -> |- [ P ] c [ Q ]
  ----------------------
  -> |- [ P' ] c [ Q ]
H-Str impl prem = H-Conseq impl prem (λ s z → z)

H-Weak : ∀ {P Q Q' c} -- Weaken (know less of post)
  -> |- [ P ] c [ Q ]
  -> ⊨ (Q ==> Q')
  ----------------------
  -> |- [ P ] c [ Q' ]
H-Weak prem impl = H-Conseq (λ s z → z) prem impl 

H-While' : ∀ {P Q b c}
  -> |- [ P  ∧' lift b ] c [ P ]
  -> ⊨ ((P ∧' lift (Not b)) ==> Q)
  ----------------------
  -> |- [ P ] WHILE b DO c [ Q ]
H-While' prem impl = H-Weak (H-While prem) impl



-- Esempio calcolo del massimo
-- vedo se una variabile (a3) è massima di altre due
max' : Aexp -> Aexp -> Aexp -> Assn
max' a1 a2 a3 = λ {s -> max (aval a1 s) (aval a2 s) == (aval a3 s)}

_<'_ : Aexp -> Aexp -> Assn
a1 <' a2 = λ s -> aval a1 s <ℕ aval a2 s == true

{-
lemma-b-false-rev : ∀{b s} ->  lift (Not b) s ->  bval b s == false
lemma-b-false-rev {b} {s} lift rewrite lift = {!!}

pr-calc-max : |- [ ⊤' ] IF (Less (V X) (V Y)) THEN (Z := V Y) ELSE (Z := V X) [ max' (V X) (V Y) (V Z) ]
pr-calc-max = H-If pr-calc-True pr-calc-False
    where
      less-max : ∀(n m : ℕ) -> n <ℕ m == true -> max n m == m
      less-max zero (succ m) less = refl
      less-max (succ n) (succ m) less = cong succ (less-max n m less) 

      X<Y : ⊨ ((⊤' ∧' lift (Less (V X) (V Y))) ==> max' (V X) (V Y) (V Y))
      X<Y s (<> , less) = less-max (aval (V X) s) (aval (V Y) s) less

      not-less-max : ∀(n m : ℕ) -> n <ℕ m == false -> max n m == n
      not-less-max zero zero not-less = refl
      not-less-max (succ n) zero not-less = refl
      not-less-max (succ n) (succ m) not-less = cong succ (not-less-max n m not-less)

      X≥Y :  ⊨ ((⊤' ∧' lift (Not (Less (V X) (V Y)))) ==> max' (V X) (V Y) (V X))
      X≥Y s (<> , not-less) = not-less-max (aval (V X) s) (aval (V Y) s) (lemma-b-false-rev not-less )

      pr-calc-True : |- [ ⊤' ∧' lift (Less (V X) (V Y)) ] Z := V Y [ max' (V X) (V Y) (V Z) ]
      pr-calc-True = H-Str X<Y H-Loc

      pr-calc-False : |- [ ⊤' ∧' lift (Not (Less (V X) (V Y))) ] Z := V X [ max' (V X) (V Y) (V Z) ]
      pr-calc-False = H-Str X≥Y H-Loc
-}



-- Excercise
conj : |- [ (V X ==' N 1) ∧' (V Y ==' N 2) ]
          (Z := V X) :: ((X := V Y) :: (Y := V Z))
          [ (V Y ==' N 1) ∧' (V X ==' N 2) ]
conj = H-Comp H-Loc (H-Comp H-Loc H-Loc) 
