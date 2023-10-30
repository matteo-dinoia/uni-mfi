module Code.Exercise.01-random where

open import Library.Nat
open import Library.Bool
open import Library.Equality

-- es 1
succ1 : ℕ -> ℕ
succ1 x = x + 1
succ2 : ℕ -> ℕ
succ2 x = max zero (succ(x))
succ3 : ℕ -> ℕ
succ3 x = succ(zero) + x + zero
succ4 : ℕ -> ℕ
succ4 x = x + max 1 0
succ5 : ℕ -> ℕ
succ5 x = x + min 1 (succ(succ(zero)))
succ6 : ℕ -> ℕ
succ6 zero = succ(zero)
succ6 (succ(x)) = succ(succ(x)) 

--es 2
poly1 : ℕ -> ℕ
poly1 x = 2 * x ^ 2

poly2 : ℕ -> ℕ -> ℕ
poly2 x y = 2 * (x ^ 3 + y ^ 2)

prova = λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x y y

--es 1,... bool
and1 : Bool -> Bool -> Bool
and1 true y = y
and1 false _ = false

and2 : Bool -> Bool -> Bool
and2 x true = x
and2 _ false = false

_|||_ : Bool -> Bool -> Bool
true ||| _ = true
false ||| y = y

infixl 8 _|||_ 

xor : Bool -> Bool -> Bool
xor true y = not y
xor false y = y

--es 1 Bool prop
&&-true-unit-r : ∀ (x : Bool) -> true && x == x
&&-true-unit-r x = refl

&&-true-unit-l : ∀ (x : Bool) -> x && true == x
&&-true-unit-l true = refl
&&-true-unit-l false = refl

--es 2
&&-ass : ∀ (x : Bool) (y : Bool)  (z : Bool) -> (x && y) && z == x && (y && z)
&&-ass true y z = refl
&&-ass false y z = refl

--es 3
morgan-&& : ∀ (x : Bool) (y : Bool) -> not (x && y) == not x || not y
morgan-&& true y = refl
morgan-&& false y = refl

morgan-|| : ∀ (x : Bool) (y : Bool) -> not (x || y) == not x && not y
morgan-|| true y = refl
morgan-|| false y = refl
