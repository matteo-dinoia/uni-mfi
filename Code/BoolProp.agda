module Code.BoolProp where

open import Library.Equality
open import Code.Bool

-- _==_ : Set dove Set = Prop (proposizione)
  -- prop è insieme di evidenze che cosa è vera
  -- questo è abitato da refl feflesività
-- Set lo abbiamo usato come sinonimo di Tipo

true-eq : true == true
true-eq = refl  -- C-c C-a se è banale lo risolve lui 

false-eq : false == false
false-eq = refl

not-true-eq : not true == false  -- false == false
not-true-eq = refl

--TEOREMA
not-inv : ∀(x : Bool) -> not (not x) == x --involutività 
not-inv true = true-eq  --DIMOSTRAZIONE
not-inv false = refl
