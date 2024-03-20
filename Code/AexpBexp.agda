module Code.AexpBexp where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning



Index = ℕ   -- Per i "nomi" variabili 
data Vname : Set where
   Vn : Index -> Vname

_=ℕ_ : ℕ -> ℕ -> Bool
_=ℕ_ zero zero = true
_=ℕ_ (succ n) (succ m) = _=ℕ_ n m
_=ℕ_ _ _ = false

_=Vn_ : (x y : Vname) -> Bool
_=Vn_ (Vn i) (Vn j) = _=ℕ_ i j

Val = ℕ
State = Vname -> Val

_[_::=_] : State -> Vname -> Val -> State
(s [ x ::= v ]) = λ y -> if (x =Vn y) then v else s y



data Aexp : Set where   -- es. Plus (V X) (Plus (N 1) (V Y)) = X + (1 + Y)
   N : ℕ -> Aexp                  -- numerali
   V : Vname -> Aexp              -- variabili
   Plus : Aexp -> Aexp -> Aexp    -- somma

aval : Aexp -> State -> Val
aval (N n) s = n
aval (V vn) s = s vn
aval (Plus a1 a2) s = aval a1 s + aval a2 s


_[_/_] : Aexp -> Aexp -> Vname -> Aexp -- sostituisco x ad a'
N n [ a' / x ] = N n
V v [ a' / x ] with x =Vn v
... | true  = a'
... | false = V v
Plus a1 a2 [ a' / x ] = Plus (a1 [ a' / x ]) (a2 [ a' / x ])  

lemma-subst : ∀ (a a' : Aexp) (x : Vname) (s : State) ->
         aval (a [ a' / x ]) s == aval a (s [ x ::= aval a' s ])
lemma-subst (N n) a' x s = refl
lemma-subst (V v) a' x s with x =Vn v
... | true = refl
... | false = refl
lemma-subst (Plus a1 a2) a' x s rewrite lemma-subst a1 a' x s |
                                        lemma-subst a2 a' x s = refl


data Bexp : Set where
   B : Bool -> Bexp             -- boolean constants
   Less : Aexp -> Aexp -> Bexp    -- less than
   Not : Bexp -> Bexp           -- negation
   And : Bexp -> Bexp -> Bexp    -- conjunction

_<ℕ_ : ℕ -> ℕ -> Bool
zero <ℕ   zero   = false
zero <ℕ   succ n = true
succ n <ℕ zero   = false
succ n <ℕ succ m = n <ℕ m

bval : Bexp -> State -> Bool
bval (B x)        s = x
bval (Less a1 a2) s = aval a1 s <ℕ aval a2 s 
bval (Not b)      s = not (bval b s)
bval (And b1 b2)  s = bval b1 s && bval b2 s

-- ESERCIZI
lemma-bval-tot : ∀ (b : Bexp) (s : State) ->
                    bval b s == true ∨ bval b s == false
lemma-bval-tot b s with bval b s
... | true = inl refl
... | false = inr refl

_[_/_]B : Bexp -> Aexp -> Vname -> Bexp
B x        [ a / v ]B = B x
Less x1 x2 [ a / v ]B = Less x1 x2 
Not b      [ a / v ]B = Not (b [ a / v ]B)
And b1 b2  [ a / v ]B = And (b1 [ a / v ]B) (b2 [ a / v ]B)


{-
lemma-subst-bexp : ∀(b : Bexp) (a : Aexp) (x : Vname) (s : State) ->
                    bval (b [ a / x ]B) s == bval b (s [ x ::= aval a s ])
lemma-subst-bexp (B b) a x s = refl
lemma-subst-bexp (Less a1 a2) a x s =
    begin
       bval (Less a1 a2 [ a / x ]B) s                        ==⟨⟩
       bval (Less (a1 [ a / x ]) (a2 [ a / x ])) s           ==⟨⟩
       (aval  (a1 [ a / x ]) s) <ℕ (aval  (a2 [ a / x ]) s) ==⟨ cong2 _<ℕ_ lm1 lm2 ⟩
       (aval a1 s') <ℕ (aval a2 s')                         ==⟨⟩
       bval (Less a1 a2) s'
    end
    where
         s' : State
         s' = s [ x ::= aval a s ]

         lm1 : aval (a1 [ a / x ]) s == aval a1 (s [ x ::= aval a s ])
         lm1 = lemma-subst a1 a x s

         lm2 : aval (a2 [ a / x ]) s == aval a2 (s [ x ::= aval a s ])
         lm2 = lemma-subst a2 a x s
lemma-subst-bexp (Not b) a x s = cong not (lemma-subst-bexp b a x s)
lemma-subst-bexp (And b1 b2) a x s rewrite lemma-subst-bexp b1 a x s |
                                           lemma-subst-bexp b2 a x s = refl

-}
