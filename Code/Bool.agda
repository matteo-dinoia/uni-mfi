module Code.Bool where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

and : Bool -> Bool -> Bool
and true true = true
and _ _ = false

or : Bool -> Bool -> Bool
or false false = false
or _ _ = true


_&&_ : Bool -> Bool -> Bool
true && true = true
true && false = false
false && true = false
false && false = false

_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true

!_ : Bool -> Bool
! true = false
! false = true


infixr 6 _&&_ --for associazione a destra con precedenza 6
infixr 7 _||_ --for associazione a destra con precedenza 6





--bb = true  && true && false
bb2 = false && true || true
