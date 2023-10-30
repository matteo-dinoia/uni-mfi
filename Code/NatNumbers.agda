module Code.NatNumbers where

open import Library.Equality
-- Reasoning is for ...=...=... for dimostrations
open import Library.Equality.Reasoning


data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

tree-eq : succ(succ(succ zero)) == 3
tree-eq = refl --sono lo stesso oggetto

infixl 6 _+_
infixl 7 _*_
infixl 8 _^_

_+_ : ℕ -> ℕ -> ℕ
zero + y = y
succ x + y = succ (x + y)

_*_ : ℕ -> ℕ -> ℕ
zero * y = zero
succ x * y = y + x * y

_^_ : ℕ -> ℕ -> ℕ
x ^ zero = succ(zero)
x ^ succ y = x * x ^ y

--PROPRIETA'

+-ass : ∀ (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-ass zero y z = refl   --Rango è numero volte che compare a sinistra (vogliamo il maggiore)
+-ass (succ x) y z = cong succ (+-ass x y z)  --cong (congruenza) ? ? C-c C-l

+-ass2 : ∀ (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-ass2 zero y z = refl
+-ass2 (succ x) y z =
  begin
    (succ x) + (y + z) ==⟨⟩
    succ (x + (y + z)) ==⟨ cong succ (+-ass2 x y z)⟩
    succ ((x + y) + z) ==⟨⟩
    ((succ x) + y) + z
  end
    
+-ass3 : ∀ (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-ass3 zero  y z = refl
+-ass3 (succ x) y z rewrite +-ass3 x y z = refl

+-unit-r : ∀(x : ℕ) -> x == x + zero --LEMMA
+-unit-r zero = refl
+-unit-r (succ x) = cong succ (+-unit-r x)

+-succ : ∀(x y : ℕ) -> succ x + y == x + succ y
+-succ zero     y = refl
+-succ (succ x) y = cong succ (+-succ x y)

+-comm : ∀ (x y : ℕ) -> x + y == y + x
+-comm zero y = +-unit-r y
+-comm (succ x) y =
  begin
    succ (x + y) ==⟨ cong succ (+-comm x y) ⟩
    succ (y + x) ==⟨ +-succ y x ⟩
    y + succ x
  end


--COMPITI
infixl 6 _-_

_-_ : ℕ -> ℕ -> ℕ
x - zero = x
zero - succ y = zero
succ x - succ y = x - y

plus-minus-l : ∀(x y : ℕ) -> (x + y) - x == y
plus-minus-l zero y = refl
plus-minus-l (succ x) y = plus-minus-l x y

--plus-minus-r : ∀(x y : ℕ) -> (x + y) - y == x
