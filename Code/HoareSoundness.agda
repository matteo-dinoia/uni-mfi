module Code.HoareSoundness where

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


lemma-b-false : ∀{b s} -> bval b s == false -> lift (Not b) s
lemma-b-false {b} {s} b-false rewrite b-false = refl

-- Correttezza while
lemma-Hoare-inv : ∀ {P : Assn} {s b c t} ->
                  (∀{s' t'} -> (P s' ∧ bval b s' == true)
                            -> ⦅ c , s' ⦆ ⇒ t'
                            -> P t') -- = premessa di while |=[P ∧' lift b] c [P]
                  -> P s -> ⦅ WHILE b DO c , s ⦆ ⇒ t -> P t
lemma-Hoare-inv hyp Ps (WhileFalse x) = Ps
lemma-Hoare-inv hyp Ps (WhileTrue x com while-com) = claim2
  where
    claim1 = hyp (Ps , x) com -- P s2
    claim2 = lemma-Hoare-inv hyp claim1 while-com


lemma-Hoare-loop-exit : ∀ {b c s t}
             -> ⦅ WHILE b DO c , s ⦆ ⇒ t -> lift (Not b) t
lemma-Hoare-loop-exit (WhileFalse {b = b} x) = lemma-b-false {b} x
lemma-Hoare-loop-exit (WhileTrue x com while-com) = lemma-Hoare-loop-exit while-com


-- Correttezza
lemma-Hoare-sound : ∀ {P c Q s t} -> -- "Spacchetta" parte destra
             |- [ P ] c [ Q ] -> 
             P s  ->  ⦅ c , s ⦆ ⇒ t  ->  Q t -- passo = big step
lemma-Hoare-sound H-Skip             Ps Skip = Ps
lemma-Hoare-sound H-Loc              Ps Loc  = Ps --forma diversa
lemma-Hoare-sound (H-Comp der1 der2) Ps (Comp passo1 passo2) = hyp2
  where
    hyp1 = lemma-Hoare-sound der1 Ps passo1 -- tipo R s
    hyp2 = lemma-Hoare-sound der2 hyp1  passo2 -- tipo Q t
lemma-Hoare-sound (H-If der1 der2) Ps (IfTrue x passo) =  -- Ps , x ha Tipo (P s, lift b s) [è un and]
                  lemma-Hoare-sound der1 (Ps , x) passo
lemma-Hoare-sound {s = s} {t = t} (H-If der1 der2) Ps (IfFalse {b = b} x passo) =
                  lemma-Hoare-sound der2 (Ps , lemma-b-false {b} {s} x) passo
lemma-Hoare-sound {_}{_}{_}{s}{t} (H-Conseq pre der post) Ps passo = Q
  where
    P1 = pre s Ps -- Tipo P' S
    hyp = lemma-Hoare-sound der P1 passo -- Q' t
    Q = post t hyp
lemma-Hoare-sound (H-While der) = {!H-Weak!}
 
-- Correttezza finale
theorem-Hoare-sound : ∀ {P c Q} ->
                    |- [ P ] c [ Q ] -> |= [ P ] c [ Q ] 
theorem-Hoare-sound hyp = lemma-Hoare-sound hyp

