module Code.HoareCompl where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning

open import Code.AexpBexp
open import Code.BigStep
open import Code.HoareLogic
open import Code.HoareSoundness

-- weakest liberal precondition
wlp : Com -> Assn -> Assn -- Assn = State -> Set
wlp c Q s = ∀ t -> ⦅ c , s ⦆ ⇒ t -> Q t -- equiv. a:  wlp c Q = λ s -> ...
-- il ∀ esce da |= [P] c [Q] = ∀{s t}  ->  P t -> ⦅ c , s ⦆ ⇒ t  ->  Qt
-- E' asserzione che vale in tutte le s in cui vale la parte a destra
-- ⟦ P ⟧ = {s | P s} insieme stati in cui vera asserzione (scirtti \[[, \]], \subseteq)
-- ⟦P⟧ ⊆ ⟦wlp c Q⟧, visto che precondiz. è più forte se insieme piccolo
-- Allora wlp è precondizione più debole di P con rispetto a c, Q

Fact : ∀ {P c Q} -> |= [ P ] c [ Q ] -> (∀ s -> P s -> (wlp c Q) s)
Fact hyp1 = λ s Ps t com → hyp1 Ps com



lemma-b-false-inv : ∀{b s} -> lift (Not b) s -> bval b s == false
lemma-b-false-inv {b} {s} lift-not-b with bval b s
... | false = refl



wlp-lemma : ∀ c {Q} → |- [ wlp c Q ] c [ Q ]
wlp-lemma SKIP                       {Q} = H-Str {!refl!} H-Skip
  where
    wlp-SKIP : ∀ s -> (wlp SKIP Q) s -> Q s
    wlp-SKIP s wp = wp s Skip -- stato e passo -> Q t
{-   wlp-SKIP -----------------       H-Skip --------------
              wlp SKIP Q ==> Q               [Q] SKIP [Q]
     H-Str  -----------------------------------------------
                          [ wlp SKIP Q ] c [ Q ]                      -}

-- |- [ wlp (x := a) Q ] x := a [ Q ]
wlp-lemma (x := a)                   {Q} = H-Str wlp-LOC H-Loc
  where
    wlp-LOC : ∀ s -> (wlp (x := a) Q) s -> (Q ⟨ a / x ⟩) s
    wlp-LOC s wp = wp (s [ x ::= aval a s ]) Loc
{-  wlp-LOC -------------------------       H-Loc -----------------------
             wlp (x:=a) Q ==> Q⟨a/x⟩                [ Q⟨a/x⟩ ] x:=a [Q]
     H-Str  -------------------------------------------------------------
                          [ wlp (x:=a) Q ] x:=a [ Q ]                      -}

-- |- [ wlp (com1 :: com2) Q ] com1 :: com2 [ Q ]
wlp-lemma (c1 :: c2)             {Q} = H-Str wlp-Comp-lemma (H-Comp H1 H2)
  where
    wlp-Comp-lemma : ∀ {c1 c2 Q} -> ∀ s  ->  wlp (c1 :: c2) Q s ->  wlp c1 (wlp c2 Q) s
    wlp-Comp-lemma s wp-comp = λ s1 der-c1 -> λ s2 der-c2 → wp-comp s2 (Comp der-c1 der-c2)

    H2 : |- [ wlp c2 Q ] c2 [ Q ]
    H2 = wlp-lemma c2 {Q}
    H1 : |-  [ wlp c1 (wlp c2 Q) ] c1 [ wlp c2 Q ]
    H1 = wlp-lemma c1 {wlp c2 Q}
{-                                               [ wlp c1 (wlp c2 Q)  ] c1 [ wlp c2 Q ]     [ wlp c2 Q ] c2 [Q]
  wlp-Comp-Lemma --------------------------------------    H-comp  --------------------------------------------
                 wlp (c1 :: c2) Q ==> wlp c1 (wlp c2 Q)               [ wlp c1 (wlp c2 Q)  ] c1 :: c2 [ Q ]  
      H-Str  ------------------------------------------------------------------------------------------------
                     [ wlp (c1::c2) Q ] c1::c2 [ Q ]
-}
-- |- [ wlp (IF x THEN c1 ELSE c2) Q ] IF x THEN c1 ELSE c2 [ Q ]
wlp-lemma (IF x THEN c1 ELSE c2) {Q} = H-If (H-Str lft IH1) (H-Str rft IH2)
  where
    P = wlp (IF x THEN c1 ELSE c2) Q
    
    lft : ⊨ ((P ∧' lift x) ==> wlp c1 Q) -- vero in tutti s
    lft s (Ps , x=true) = λ t ⦅c1,s⦆⇒t → Ps t (IfTrue x=true ⦅c1,s⦆⇒t)

    rft : ⊨ ((P ∧' lift (Not x)) ==> wlp c2 Q)
    rft s (Ps , x=false) = λ t ⦅c2,s⦆⇒t → Ps t (IfFalse (lemma-b-false-inv {x} {s} x=false) ⦅c2,s⦆⇒t)

    IH1 : |- [ wlp c1 Q ] c1 [ Q ]
    IH1 = wlp-lemma c1 {Q}
    
    IH2 : |- [ wlp c2 Q ] c2 [ Q ]
    IH2 = wlp-lemma c2 {Q}
{-
  lft  --------------------              rft ----------------------
        P ∧ x ==> wlp c1 Q    IH1            P ∧ ¬ x ==>' wlp c2 Q    IH2
 H-Str ---------------------------  H-Str  ------------------------------
                 [P ∧ x] c1 [Q]                   [P ∧ ¬ x] c2 [Q]
  H-If  --------------------------------------------------------------------
                        [P] IF x THEN c1 ELSE c2 [Q]
-}
--|- [ wlp (WHILE x DO c) Q ] WHILE x DO c [ Q ]
wlp-lemma (WHILE x DO c)           {Q} = H-Weak (H-While (H-Str cl1 IH)) cl2
  where
    P = wlp (WHILE x DO c) Q

    IH : |- [ wlp c P ] c [ P ]
    IH = wlp-lemma c {P}

    cl1 : ⊨ ((P ∧' lift x) ==> wlp c P)
    cl1 s (Ps , x=true) = λ t1 big_c
                → λ t big_int → Ps t (WhileTrue x=true big_c big_int)

    cl2 : ⊨ ((P ∧' lift (Not x)) ==> Q)
    cl2 s (Ps , x=false) = Ps s (WhileFalse (lemma-b-false-inv {x} {s} x=false))
{-    cli --------------------
           P ∧' b ==> wlp c P           IH      
 H-Str -------------------------------------
               [P ∧' b] c [P]
    H-While ---------------------------          cl2 ---------------- 
            [P] WHILE x DO c [P ∧' ¬ x]                P ∧' ¬ x ==> Q
    H-Weak -----------------------------------------------------------
              [P] WHILE x DO c [Q]                                 -}
 


-- Completezza finale
completeness : ∀ c -> ∀ {P Q} -> |= [ P ] c [ Q ] -> |-  [ P ] c [ Q ]
completeness c hyp = H-Str (Fact hyp) (wlp-lemma c)
{-       |= [P] c [Q] 
  Fact ---------------------  wlp-lemma ---------------------
        |= P ==> wlp c Q                  |- [wlp c Q] c [Q]
 H-Str ----------------------------------------------------
                     |- [P] c [Q]                           -}
