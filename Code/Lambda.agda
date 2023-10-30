module Code.Lambda where
open import Library.Nat

f : ℕ -> ℕ
f x = x ^ 2 + 1

f₁ : ℕ -> ℕ
f₁ = λ x -> x ^ 2 + 1

g : ℕ -> ℕ -> ℕ
g = λ x -> λ y -> x ^ 2 + 2 * x * y + y ^ 2

{- Γ = f : ℕ -> ℕ, x : ℕ

                    f  : ℕ -> ℕ     x : ℕ
  ----------  ax  --------------------------  -> E 
  f : ℕ -> ℕ            f x : ℕ
 -----------------------------------  -> E
          Γ ⊢ f (f x) : ℕ
  -----------------------------
 Γ, f : ℕ -> ℕ  ⊢ λ x -> f x : ℕ -> ℕ
   ---------------------------
    ⊢ λ f -> λ x -> f (f x) : (ℕ -> ℕ) -> ℕ -> ℕ 
-}

twice : (ℕ -> ℕ) -> ℕ -> ℕ
twice = λ f -> λ x -> f (f x)

test : ℕ
test = twice f₁ 3


{-
twice f₁ 3 -> f₁ (f₁ 3)
           -> (f₁ 3) ^ 2 + 1
           -> (3 ^ 2 + 1) ^ 2 + 1
-}

h = λ (x : ℕ) -> x + 1

t = λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x y y