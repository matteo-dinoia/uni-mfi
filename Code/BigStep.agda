module Code.BigStep where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning

open import Code.AexpBexp



data Com : Set where
  SKIP  : Com                              -- inaction
  _:=_  : Vname → Aexp → Com              -- assignment
  _::_  : Com → Com → Com                 -- sequence
  IF_THEN_ELSE_ : Bexp → Com → Com → Com  -- conditional
  WHILE_DO_     : Bexp → Com → Com         -- iteration

-- Definiamo relazione ⦅ c , s ⦆ ⇒ t dove ⦅ scritto \(( e ⇒ scritto \=>
data Config : Set where
  ⦅_,_⦆ : Com -> State -> Config

data _⇒_ : Config -> State -> Set where
 -- Fine programma
    Skip : ∀ {s}
         ----------------
         → ⦅ SKIP , s ⦆ ⇒ s
 -- Assegnamento      
    Loc : ∀{x a s}
        ---------------------------------------
        → ⦅ x := a , s ⦆ ⇒ (s [ x ::= (aval a s) ])
 -- Composizione
    Comp : ∀{c1 c2 s1 s2 s3}
         → ⦅ c1 , s1 ⦆ ⇒ s2
         → ⦅ c2 , s2 ⦆ ⇒ s3
           --------------------
         → ⦅ c1 :: c2 , s1 ⦆ ⇒ s3
 -- Se if-else vero
    IfTrue : ∀{c1 c2 b s t}
           → bval b s == true
           → ⦅ c1 , s ⦆ ⇒ t
             -------------------------------
           → ⦅ IF b THEN c1 ELSE c2 , s ⦆ ⇒ t
 -- Se if-else Falso   
    IfFalse : ∀{c1 c2 b s t}
            → bval b s == false
            → ⦅ c2 , s ⦆ ⇒ t
              -------------------------------
            → ⦅ IF b THEN c1 ELSE c2 , s ⦆ ⇒ t
 -- While non più vero
    WhileFalse : ∀{c b s}
               → bval b s == false
                 -----------------------
               → ⦅ WHILE b DO c , s ⦆ ⇒ s
 -- Finche vero        
    WhileTrue  : ∀{c b s1 s2 s3}
               → bval b s1 == true
               → ⦅ c , s1 ⦆ ⇒ s2
               → ⦅ WHILE b DO c , s2 ⦆ ⇒ s3
                 ------------------------
               → ⦅ WHILE b DO c , s1 ⦆ ⇒ s3

infix 10 _⇒_



-- Proprietà ⦅ c , s ⦆ ⇒ t non è triviale
lemma-while-true : ∀{c s t} -> ¬ ( ⦅ WHILE (B true) DO c , s ⦆ ⇒ t )
lemma-while-true (WhileTrue b-true h h') = lemma-while-true h'

-- Proprietà  ⦅ c , s ⦆ ⇒ t è deterministica
true-neq-false : ¬ (true == false)
true-neq-false = λ () -- oppure true-neq-false ()

lemma-true-neq-false : ∀ {A : Set} → true == false → A
lemma-true-neq-false x = ex-falso (true-neq-false x)

theorem-det : ∀{c s t r} -> ⦅ c , s ⦆ ⇒ t -> ⦅ c , s ⦆ ⇒ r -> t == r
theorem-det Skip Skip = refl
theorem-det Loc Loc = refl
theorem-det (Comp h1 h2) (Comp k1 k2) rewrite theorem-det h1 k1 |
                                              theorem-det h2 k2 = refl
theorem-det (IfTrue x h1) (IfTrue x₁ h2) = theorem-det h1 h2
theorem-det (IfFalse x h1) (IfFalse x₁ h2) = theorem-det h1 h2
theorem-det (WhileFalse x) (WhileFalse x₁) = refl
theorem-det (WhileTrue x h1 h2) (WhileTrue x₁ k1 k2)
              rewrite theorem-det h1 k1 | theorem-det h2 k2 = refl
 -- casi difficili uso assurdità
theorem-det (IfTrue bval1 h1) (IfFalse bval2 h2) = lemma-true-neq-false abs
                   where
                     abs : true == false
                     abs = tran (symm bval1) bval2
theorem-det (IfFalse bval1 h1) (IfTrue bval2 h2) = lemma-true-neq-false abs
                   where
                     abs : true == false
                     abs = tran (symm bval2) bval1
theorem-det (WhileFalse bval1) (WhileTrue bval2 h2 h3) = lemma-true-neq-false abs
                   where
                     abs : true == false
                     abs = tran (symm bval2) bval1
theorem-det (WhileTrue bval1 h1 h2) (WhileFalse bval2) = lemma-true-neq-false abs
                   where
                     abs : true == false
                     abs = tran (symm bval1) bval2


-- Equivalenza di comandi
_~_ : Com -> Com -> Set
c ~ c' = ∀{s t} -> ⦅ c , s ⦆ ⇒ t <=> ⦅ c' , s ⦆ ⇒ t

infixl 19 _~_

lemma-if-true : ∀(c c' : Com) -> (IF (B true) THEN c ELSE c') ~ c
lemma-if-true c c' {s} {t} = only-if-part , if-part
  where
    only-if-part : ⦅ IF B true THEN c ELSE c' , s ⦆ ⇒ t → ⦅ c , s ⦆ ⇒ t
    only-if-part (IfTrue x h) = h
    if-part :  ⦅ c , s ⦆ ⇒ t → ⦅ IF B true THEN c ELSE c' , s ⦆ ⇒ t
    if-part h = IfTrue refl h

lemma-if-c-c : ∀(b : Bexp) (c : Com) -> (IF b THEN c ELSE c) ~ c
lemma-if-c-c b c {s} {t} = only-if-part , if-part
   where
    only-if-part : ⦅ IF b THEN c ELSE c , s ⦆ ⇒ t → ⦅ c , s ⦆ ⇒ t
    only-if-part (IfTrue x h) = h
    only-if-part (IfFalse x h) = h
    if-part :   ⦅ c , s ⦆ ⇒ t → ⦅ IF b THEN c ELSE c , s ⦆ ⇒ t
    if-part h with lemma-bval-tot b s
    ... | inl x = IfTrue x h
    ... | inr x = IfFalse x h



-- ESERCIZI
lemma-if-false : ∀ (c c' : Com) → (IF B false THEN c ELSE c') ~ c'
lemma-if-false c c' = (λ{(IfFalse x h) -> h}) , λ{h -> IfFalse refl h}

lemma-while-false-skip : ∀ {c} → WHILE B false DO c ~ SKIP
lemma-while-false-skip = only-if , if-part
  where
    only-if : ∀{c s t} ->  ⦅ WHILE B false DO c , s ⦆ ⇒ t → ⦅ SKIP , s ⦆ ⇒ t
    only-if (WhileFalse x) = Skip
    if-part : ∀{c s t} -> ⦅ SKIP , s ⦆ ⇒ t → ⦅ WHILE B false DO c , s ⦆ ⇒ t
    if-part Skip = WhileFalse refl

lemma-while-if : ∀ (b : Bexp) (c : Com) →
        (WHILE b DO c) ~ (IF b THEN (c :: (WHILE b DO c)) ELSE SKIP)
lemma-while-if b c = only-if , if-part
   where
     only-if : ∀{b c s t} -> ⦅ WHILE b DO c , s ⦆ ⇒ t → ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆ ⇒ t
     only-if (WhileFalse x) = IfFalse x Skip
     only-if (WhileTrue x h1 h2) = IfTrue x (Comp h1 h2)
     if-part : ∀{b c s t} -> ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆ ⇒ t → ⦅ WHILE b DO c , s ⦆ ⇒ t
     if-part (IfTrue x (Comp h1 h2)) = WhileTrue x h1 h2
     if-part (IfFalse x Skip) = WhileFalse x
