module Code.SmallStep where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning

open import Code.AexpBexp
open import Code.BigStep

data _⟶_ : Config -> Config -> Set where  -- the symbol ⟶ is written \-->
  --Skip non riduce

  Loc : ∀{x a s}
        --------------------------------------------------
      -> ⦅ x := a , s ⦆ ⟶ ⦅ SKIP , s [ x ::= aval a s ] ⦆
      
  Comp₁ : ∀{c s}
          ---------------------------------
          -> ⦅ SKIP :: c , s ⦆ ⟶ ⦅ c , s ⦆
        
  Comp₂ : ∀{c1 c2 c1b s s′}
          -> ⦅ c1 , s ⦆ ⟶ ⦅ c1b , s′ ⦆  -- se riduce => non SKIP
          -----------------------------------------
          -> ⦅ c1 :: c2 , s ⦆ ⟶ ⦅ c1b :: c2 , s′ ⦆
        
  IfTrue  : ∀{b s c1 c2}
          -> bval b s == true
          ---------------------------------------------
          -> ⦅ IF b THEN c1 ELSE c2 , s ⦆ ⟶ ⦅ c1 , s ⦆
          
  IfFalse : ∀{b s c1 c2}
          -> bval b s == false
          ---------------------------------------------
          -> ⦅ IF b THEN c1 ELSE c2 , s ⦆ ⟶ ⦅ c2 , s ⦆
          
  While : ∀{b c s}
          ----------------------------------------------------------------------------
          -> ⦅ WHILE b DO c , s ⦆ ⟶ ⦅ IF b THEN (c :: (WHILE b DO c)) ELSE SKIP , s ⦆



data  _⟶*_ : Config -> Config -> Set where
   ⟶*-refl : ∀ {c s} -> ⦅ c , s ⦆ ⟶* ⦅ c , s ⦆  -- reflexivity
   ⟶*-incl : ∀ {c1 s1 c2 s2 c3 s3} ->            -- including ⟶
                 ⦅ c1 , s1 ⦆ ⟶ ⦅ c2 , s2 ⦆ ->
                 ⦅ c2 , s2 ⦆ ⟶* ⦅ c3 , s3 ⦆ ->
                 ⦅ c1 , s1 ⦆ ⟶* ⦅ c3 , s3 ⦆

⟶*-tran : ∀{c1 s1 c2 s2 c3 s3}
        -> ⦅ c1 , s1 ⦆ ⟶* ⦅ c2 , s2 ⦆   ->  ⦅ c2 , s2 ⦆ ⟶* ⦅ c3 , s3 ⦆
        ->  ⦅ c1 , s1 ⦆ ⟶* ⦅ c3 , s3 ⦆
⟶*-tran ⟶*-refl der2 = der2
⟶*-tran (⟶*-incl der1a der1b) der2 = ⟶*-incl der1a (⟶*-tran der1b der2)

⦅_,_⦆∎ : ∀ c s -> ⦅ c , s ⦆ ⟶* ⦅ c , s ⦆
⦅ c , s ⦆∎ = ⟶*-refl
⦅_,_⦆⟶⟨_⟩_ : ∀ c s {c' c'' s' s''} ->
             ⦅ c , s ⦆ ⟶ ⦅ c' , s' ⦆ ->
             ⦅ c' , s' ⦆ ⟶* ⦅ c'' , s'' ⦆ ->
             ⦅ c , s ⦆ ⟶* ⦅ c'' , s'' ⦆
⦅ c , s ⦆⟶⟨ x ⟩ y = ⟶*-incl x y
⦅_,_⦆⟶*⟨_⟩_ : ∀ c s {c' c'' s' s''} ->
             ⦅ c , s ⦆ ⟶* ⦅ c' , s' ⦆ ->
             ⦅ c' , s' ⦆ ⟶* ⦅ c'' , s'' ⦆ ->
             ⦅ c , s ⦆ ⟶* ⦅ c'' , s'' ⦆
⦅ c , s ⦆⟶*⟨ x ⟩ y = ⟶*-tran x y



-- Teorema : ⦅ c , s ⦆ ⇒ t  sse.  ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆
lemma-small-big : ∀ {c1 s1 c2 s2 t} ->
                 ⦅ c1 , s1 ⦆ ⟶ ⦅ c2 , s2 ⦆ ->
                 ⦅ c2 , s2 ⦆ ⇒ t ->
                 ⦅ c1 , s1 ⦆ ⇒ t
lemma-small-big Loc Skip = Loc
lemma-small-big Comp₁ bd = Comp Skip bd
lemma-small-big (Comp₂ sd) (Comp c1 c2) = Comp (lemma-small-big sd c1) c2
lemma-small-big (IfTrue x) bd = IfTrue x bd
lemma-small-big (IfFalse x) bd = IfFalse x bd
lemma-small-big While (IfTrue x (Comp c1 c2)) = WhileTrue x c1 c2
lemma-small-big While (IfFalse x Skip) = WhileFalse x

theorem-small-big : ∀{c s t} -> ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆ -> ⦅ c , s ⦆ ⇒ t
theorem-small-big ⟶*-refl = Skip
theorem-small-big (⟶*-incl small hyp) =
                          lemma-small-big small (theorem-small-big hyp)


lemma-big-small : ∀{c c' c'' s s'} ->
                    ⦅ c , s ⦆ ⟶* ⦅ c' , s' ⦆ ->
                    ⦅ c :: c'' , s ⦆ ⟶* ⦅ c' :: c'' , s' ⦆
lemma-big-small ⟶*-refl = ⟶*-refl
lemma-big-small (⟶*-incl x hyp) = ⟶*-incl (Comp₂ x) (lemma-big-small hyp)

theorem-big-small : ∀ {c s t} -> ⦅ c , s ⦆ ⇒ t -> ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆
theorem-big-small (Skip {s}) = ⦅ SKIP , s ⦆∎
theorem-big-small (Loc {x} {a} {s}) =
           ⦅ x := a , s ⦆⟶⟨ Loc ⟩ ⦅ SKIP , s [ x ::= aval a s ] ⦆∎
theorem-big-small (Comp {c1} {c2} {s1} {s2} {s3} hyp1 hyp2) =
           ⦅ c1 :: c2 , s1 ⦆⟶*⟨ lemma-big-small (theorem-big-small hyp1) ⟩
           (⦅ SKIP :: c2 , s2 ⦆⟶⟨ Comp₁ ⟩
           (⦅ c2 , s2 ⦆⟶*⟨ theorem-big-small hyp2 ⟩ ⦅ SKIP , s3 ⦆∎))
theorem-big-small (IfTrue {c1} {c2} {b} {s} {t} x hyp) =
           ⦅ IF b THEN c1 ELSE c2 , s ⦆⟶⟨ IfTrue x ⟩
           ((⦅ c1 , s ⦆⟶*⟨ theorem-big-small hyp ⟩ ⦅ SKIP , t ⦆∎))
theorem-big-small (IfFalse {c1} {c2} {b} {s} {t} x hyp) =
           ⦅ IF b THEN c1 ELSE c2 , s ⦆⟶⟨ IfFalse x ⟩
           ((⦅ c2 , s ⦆⟶*⟨ theorem-big-small hyp ⟩ ⦅ SKIP , t ⦆∎))
theorem-big-small (WhileFalse {c} {b} {s} x) =
           ⦅ WHILE b DO c , s ⦆⟶⟨ While ⟩
           (⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆⟶⟨ IfFalse x ⟩ ⦅ SKIP , s ⦆∎)
theorem-big-small (WhileTrue {c} {b} {s1} {s2} {s3} x hyp1 hyp2) =
          ⦅ WHILE b DO c , s1 ⦆⟶⟨ While ⟩
          (⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s1 ⦆⟶⟨ IfTrue x ⟩
          (⦅ c :: (WHILE b DO c) , s1 ⦆⟶*⟨ lemma-big-small (theorem-big-small hyp1)⟩
          (⦅ SKIP :: (WHILE b DO c) , s2 ⦆⟶⟨ Comp₁ ⟩
          (⦅ WHILE b DO c , s2 ⦆⟶*⟨ theorem-big-small hyp2 ⟩ ⦅ SKIP , s3 ⦆∎))))


-- Exercise
X : Vname
X = Vn 0

Y : Vname
Y = Vn 1

Z : Vname
Z = Vn 2

com0 : Com
com0 = (Z := V X) :: ((X := V Y) :: (Y := V Z))

st07 : State
st07 = ((λ z -> 0) [ X ::= 1 ]) [ Y ::= 2 ]

st08 : State
st08 = st07 [ Z ::= aval (V X) st07 ]

st09 : State
st09 = st08 [ X ::= aval (V Y) st08 ]

st10 : State
st10 = st09 [ Y ::= aval (V Z) st09 ]

_ : st07 X == 1
_ = refl

_ : st07 Y == 2
_ = refl

_ : st10 X == 2
_ = refl

_ : st10 Y == 1
_ = refl


exec0 : ⦅ com0 , st07 ⦆ ⟶* ⦅ SKIP , st10 ⦆
exec0 = {!!}
