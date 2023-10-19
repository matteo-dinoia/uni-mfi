module Code.Demo where

open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Nat
open import Library.Nat.Properties

fibo : ℕ -> ℕ -- spazio importante
fibo 0 = 0
fibo 1 = 1
fibo (succ (succ n)) = fibo n + fibo (succ n)

--fibo-from : ℕ -> ℕ -> ℕ -> ℕ -- ? C-c C-c C-l segno k
--fibo-from m n zero = m  -- C-C c-spazio dopo un valore
--fibo-from m n (succ zero) = n
--fibo-from m n (succ (succ k)) = fibo-from n (n + m) (succ k)

--fast-fibo : ℕ -> ℕ
--fast-fibo n = fibo-from 0 1 n

fibo-from : ℕ -> ℕ -> ℕ -> ℕ -- ? e poi load
fibo-from m n zero = m  -- C-c C-c e poi chiede variabile
                      -- C-, variabili e tipo
                      -- C-spazio per digerire se valido quello dentro
fibo-from m n (succ zero) = n
fibo-from m n (succ (succ k)) = fibo-from n (m + n) (succ k)

fib2 : ℕ -> ℕ -> ℕ -> ℕ
fib2 m n zero = m
fib2 m n (succ zero) = n
fib2 m n (succ (succ k)) = {!fib2 n (m + n) (succ k)!}
