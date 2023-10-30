module Code.Demo where

open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Nat
open import Library.Nat.Properties

fibo : ℕ -> ℕ -- spazio importante
fibo 0 = 0
fibo 1 = 1
fibo (succ (succ n)) = fibo n + fibo (succ n)

fibo-from : ℕ -> ℕ -> ℕ -> ℕ -- ? e poi load
fibo-from m n zero = m  -- C-c C-c e poi chiede variabile
                      -- C-, variabili e tipo
                      -- C-spazio per digerire se valido quello dentro
fibo-from m n (succ zero) = n
fibo-from m n (succ (succ k)) = fibo-from n (m + n) (succ k)

