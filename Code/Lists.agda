module Code.Lists where

open import Library.Fun
open import Library.Equality
open import Library.Equality.Reasoning
--open import Library.Nat
open import Code.MyNat

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 5 _::_  -- per fare a = 0 :: 1 :: 2 :: 3 :: []

[_] : ∀{A : Set} -> A -> List A -- costruttore con 1 elemento
[ x ] = x :: []      --b = [ 10 ]

length : ∀{A : Set} -> List A -> ℕ
length []        = zero
length (x :: xs) = succ(length xs)

_++_ : ∀{A : Set} -> List A -> List A -> List A
[]        ++ y = y
(x :: xs) ++ y = x :: (xs ++ y)

length-++ : ∀{A : Set} (xs ys : List A) -> length (xs ++ ys) == length xs + length ys
length-++ []       ys = refl
length-++ (x :: xs) ys rewrite length-++ xs ys = refl -- oppure ... = cong succ (length-++ xs ys)

++-assoc : ∀{A : Set} (xs ys zs : List A) -> xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
++-assoc []        ys zs = refl
++-assoc (x :: xs) ys zs = cong (x ::_) (++-assoc xs ys zs)

++-unit-l : ∀{A : Set} (xs : List A) -> xs == [] ++ xs
++-unit-l _ = refl

++-unit-r : ∀{A : Set} (xs : List A) -> xs == xs ++ []
++-unit-r [] = refl
++-unit-r (x :: xs) =  cong (x ::_) (++-unit-r xs)

reverse : ∀{A : Set} -> List A -> List A
reverse []        = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-++ : ∀{A : Set} (xs ys : List A) -> reverse (xs ++ ys) == reverse ys ++ reverse xs
reverse-++ [] ys = ++-unit-r (reverse ys)
reverse-++ (x :: xs) ys =
  begin
    reverse (xs ++ ys) ++ [ x ] ==⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ] ⟨ ++-assoc (reverse ys) (reverse xs) ([ x ]) ⟩==
    (reverse ys ++ (reverse xs ++ [ x ]))
  end

reverse-inv : ∀{A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-inv [] = refl
reverse-inv (x :: xs) =
  begin
    reverse (reverse xs ++ [ x ]) ==⟨ reverse-++ (reverse xs) [ x ] ⟩
    x :: reverse (reverse xs) ==⟨ cong (x ::_) (reverse-inv xs) ⟩
    x :: xs
  end

reverse-onto : ∀{A : Set} -> List A -> List A -> List A
reverse-onto []        ys = ys
reverse-onto (x :: xs) ys = reverse-onto xs (x :: ys)

fast-reverse : ∀{A : Set} -> List A -> List A
fast-reverse xs = reverse-onto xs []

{-
  reverse-iter(xs : List)
    var ys := [], zs := xs 
    while xs != []
      // inv. reverse zs ++ ys == reverse xs
      ys := x :: ys
      zs := tail(zs)
    return ys

-}

lemma-reverse-onto : ∀{A : Set} (xs ys : List A) -> reverse-onto xs ys == reverse xs ++ ys
lemma-reverse-onto [] ys = refl
lemma-reverse-onto (x :: xs) ys = `tran` (lemma-reverse-onto xs (x :: ys)) (++-assoc (reverse xs) [ x ] ys) -- tran (lemma-reverse-onto xs (x :: ys)) (++-assoc (reverse xs) [ x ] ys)
                                
fast-rev-corr :  ∀{A : Set} (xs : List A) -> fast-reverse xs == reverse xs
fast-rev-corr [] = refl
fast-rev-corr (x :: xs) = lemma-reverse-onto xs [ x ]


-- ESERCIZI
map : ∀{A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

len-map : ∀{A B : Set} (f : (A -> B)) (xs : List A) -> length (map f xs) == length xs
len-map f [] = refl
len-map f (x :: xs) = cong (1 +_) (len-map f xs)

++-map : ∀{A B : Set} (f : (A -> B)) (xs ys : List A) -> map f (xs ++ ys) == map f xs ++ map f ys
++-map f [] ys = refl
++-map f (x :: xs) ys = cong (f x ::_) (++-map f xs ys)

reverse-map : ∀{A B : Set} (f : A -> B) (xs : List A) -> map f (reverse xs) == reverse (map f xs)
reverse-map f [] = refl
reverse-map f (x :: xs) =
  begin
    map f (reverse xs ++ [ x ]) ==⟨ ++-map f (reverse xs) [ x ] ⟩
    map f (reverse xs) ++ [ f x ]  ==⟨ cong (_++ [ f x ]) (reverse-map f xs) ⟩
    reverse (map f xs) ++ [ f x ] ==⟨⟩
     reverse (map f xs) ++ reverse [ f x ]  ⟨ reverse-++ ([ f x ]) (map f xs) ⟩==
     reverse (f x :: map f xs) ==⟨⟩
     reverse (map f (x :: xs))
  end


len-reverse :  ∀{A : Set} (xs : List A) -> length (reverse xs) == length xs
len-reverse [] = refl
len-reverse (x :: xs) =
  begin
    length (reverse (x :: xs)) ==⟨⟩
    length ((reverse xs) ++ [ x ]) ==⟨ length-++ (reverse xs) [ x ] ⟩
    length (reverse xs) + length [ x ] ==⟨⟩
    length (reverse xs) + 1 ==⟨ cong (_+ 1) (len-reverse xs)⟩
    length xs + 1 ==⟨ +-comm (length xs) 1 ⟩
    1 + length xs
  end

∘-map : ∀{A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) ->(map f ∘ map g) xs == map (f ∘ g) xs
∘-map f g [] = refl
∘-map f g (x :: xs) =
  begin
    map f (map g (x :: xs)) ==⟨⟩
    map f ((g x) :: (map g xs))  ==⟨⟩
    ((f ∘ g) x) :: ((map f ∘ map g) xs) ==⟨ cong (((f ∘ g) x) ::_) (∘-map f g xs) ⟩
    ((f ∘ g) x) :: map (f ∘ g) xs 
  end 
