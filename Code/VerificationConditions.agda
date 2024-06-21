module Code.VerificationConditions where

open import Library.Bool
open import Library.Nat
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning
open import Code.AexpBexp
open import Code.BigStep
open import Code.HoareLogic

open import Code.HoareCompl

data Acom : Set₁ where
  SKIP  :  Acom
  _:=_  :  Vname → Aexp → Acom           
  _::_  :  Acom → Acom → Acom   
  IF_THEN_ELSE_ : Bexp → Acom → Acom → Acom 
  WHILE[_]_DO_  : Assn → Bexp → Acom → Acom

pre : Acom → Assn → Assn
pre SKIP Q = Q
pre (x := a) Q = Q ⟨ a / x ⟩ -- Q su stato cambiato
pre (C1 :: C2) Q = pre C1 (pre C2 Q)   -- precond. di precond.
pre (IF b THEN C1 ELSE C2) Q s with bval b s  -- per casi
...   | true  = pre C1 Q s
...   | false = pre C2 Q s
pre (WHILE[ I ] b DO C) Q = I  -- uso suggerimento dato

vc : Acom → Assn → Set
vc SKIP Q = ⊤
vc (x := a) Q = ⊤
vc (C1 :: C2) Q = vc C1 (pre C2 Q) ∧ vc C2 Q -- uso precond. di C2
vc (IF b THEN C1 ELSE C2) Q = vc C1 Q ∧ vc C2 Q
vc (WHILE[ I ] b DO C) Q =
        (∀ s → I s ∧ bval b s == true → pre C I s) ∧  -- si mantiene
        (∀ s → I s ∧ bval b s == false → Q s) ∧  --termina => post
        vc C I  -- verifica il caso interno


strip : Acom → Com
strip SKIP = SKIP
strip (x := a) = x := a
strip (C₁ :: C₂) = strip C₁ :: strip C₂
strip (IF b THEN C₁ ELSE C₂) = IF b THEN strip C₁ ELSE strip C₂
strip (WHILE[ I ] b DO C) = WHILE b DO strip C



vc-sound : ∀ {Q} C -> vc C Q -> |- [ pre C Q ] strip C [ Q ] 
vc-sound SKIP <> = H-Skip
vc-sound (x := x₁) <> = H-Loc

-- |- [ pre C1 (pre C2 Q) ] strip C1 :: strip C2 [ Q ]
vc-sound {Q} (C1 :: C2) (vc1 , vc2) = H-Comp IH1 IH2
  where
    IH1 : |- [ pre C1 (pre C2 Q) ] strip C1 [ pre C2 Q ]
    IH1 = vc-sound C1 vc1

    IH2 : |- [ pre C2 Q ] strip C2 [ Q ]
    IH2 = vc-sound C2 vc2

-- |- [ (λ s → pre C Q s | bval x s) ] C [ Q ]
vc-sound {Q} (IF x THEN C1 ELSE C2) (vcC1 , vcC2) = 
               H-If(H-Str case-true IH1 ) (H-Str case-false IH2)
  where
    C : Acom
    C = IF x THEN C1 ELSE C2

    IH1 : |- [ pre C1 Q ] strip C1 [ Q ]
    IH1 = vc-sound C1 vcC1

    IH2 : |- [ pre C2 Q ] strip C2 [ Q ]
    IH2 = vc-sound C2 vcC2

    case-true : ∀ s -> (pre C Q s ∧ bval x s == true) -> pre C1 Q s
    case-true s (preIF , x=true) = {!!}
    
    case-false : ∀ s -> (pre C Q s ∧ lift (Not x) s) -> pre C2 Q s
    case-false s (preIF , liftNotX) rewrite lemma-b-false-inv {x} {s} liftNotX = preIF
{-

  case-true -------------------------------
            pre C Q ∧' lift x  ==> pre c1 Q     IH1            ... (simile a sinistra)
  H-Str    ----------------------------------------   ---------------------------------------
                 [pre C Q s ∧ lift x] strip C [Q]      [pre C Q s ∧ lift (Not x)] strip C [Q]
  H-if --------------------------------------------------
                    [pre C Q] strip C [ Q ]
-}

-- |- [ I ] WHILE x DO strip C [ Q ]
vc-sound {Q} (WHILE[ I ] x DO C) (hyp1 , hyp2 , vcC) =
                   ? -- H-Weak (H-While (H-Str w-true IH)) w-false
  -- hyp1 : ∀ s → I s ∧ bval b s == true → pre C I s
  -- hyp2 : ∀ s → I s ∧ bval b s == false → Q s
  -- vcC : vc C I
  where
    IH : |- [ pre C I ] strip C [ I ]
    IH = vc-sound C vcC

    w-true : ∀ s -> (I ∧' lift x) s -> (pre C I) s 
    w-true = hyp1

    w-false :  ∀ s -> (I ∧' lift (Not x)) s -> Q s 
    w-false s (Is , liftNotX) = hyp2 s (Is , lemma-b-false-inv {x} {s} liftNotX)
{-
          w-true                        IH
     ----------------------     --------------------       
     I ∧' lift b ==> pre C I    [pre C I] strip C [I]
H-Str ----------------------------------------------
           [I ∧' lift b] strip C [I]                     
 H-While ---------------------------          hyp2 -----------------------
          [I] Cw [I ∧' lift (Not b)]              (I ∧' lift (Not b)) => Q 
 H-Weak   ---------------------------------------------------------
                               |- [I] Cw [Q]

con     Cw =  WHILE x DO strip C    per brevità  -}


{-

vc-completeness : ∀ {P Q : Assn} c →
            |- [ P ] c [ Q ] →
            ∃[ C ] ( (c == strip C) ∧ (vc C Q) ∧ (P ==> pre C Q) )
vc-completeness = ?

-}
