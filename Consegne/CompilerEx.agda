module Consegne.CompilerEx where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.List
open import Library.List.Properties

open import Consegne.AexpBexp

------------------
-- Automa a pila
------------------

-- Istruzioni

data Instr : Set where
   LOADI : Val → Instr     -- carica un valore sullo stack
   LOAD  : Vname → Instr   -- carica il valore di una variabile sullo stack
   ADD   : Instr           -- rimuove i primi due elementi dello stack
                           -- e carica la loro somma sullo stack

Stack = List Val    -- uno stack è una pila di valori
Prog  = List Instr  -- un programma è una lista di istruzioni

-- exec1 esegue una singola istruzione modificando lo stack
-- utilizzando uno stato per trattare le variabili 

exec1 : Instr → State → Stack → Stack
exec1 (LOADI n) s       stk         = n :: stk
exec1 (LOAD x)  s       stk         = (s x) :: stk
exec1 ADD       s (m :: (n :: stk)) = (m + n) :: stk
exec1 ADD       s        _          = []    -- questo caso è un errore!

-- exec itera exec1 su un programma p : Prog

exec : Prog → State → Stack → Stack
exec []        _ stk = stk
exec (i :: is) s stk = exec is s (exec1 i s stk)

----------------
-- Compilatore
----------------

comp : Aexp → Prog
comp (N n)        = (LOADI n) :: []
comp (V x)        = (LOAD x) :: []
comp (Plus a1 a2) = (comp a2) ++ (comp a1) ++ (ADD :: [])

-- La definizione di comp, benché corretta, rende più complessa
-- la dimostrazione del teorema di correttezza del compilatore.
-- Al suo posto si utilizza comp' tale che invece di definire mediante _++_
-- la lista dei comandi associati ad un'espressione a utilizza un secondo
-- parametro p : Prog dinananzi al quale costruisce la compilazione
-- di a utilizzando soltanto il costruttore _::_

comp' : Aexp → Prog → Prog  
comp' (N n) p = (LOADI n) :: p
comp' (V x) p = (LOAD x) :: p
comp' (Plus a1 a2) p = comp' a2 (comp' a1 (ADD :: p))

-- Il seguente lemma stabilisce che comp' a p == comp a ++ p
-- onde possiamo definire il compilatore compile a = comp' a []

compile : Aexp → Prog
compile a = comp' a []

lemma-comp : ∀(a : Aexp) (p : Prog) → comp a ++ p == comp' a p
lemma-comp (N x) p = refl
lemma-comp (V x) p = refl
lemma-comp (Plus a1 a2) p =
  begin
    (comp a2 ++ (comp a1 ++ ADD :: [])) ++ p ⟨ ++-assoc (comp a2) (comp a1 ++ (ADD :: [])) p ⟩==
    comp a2 ++ ((comp a1 ++ ADD :: []) ++ p) ⟨ cong (comp a2 ++_) (++-assoc (comp a1) (ADD :: []) p)  ⟩==
    comp a2 ++ ((comp a1 ++ ADD :: p)) ==⟨ cong (comp a2 ++_) (lemma-comp a1 (ADD :: p)) ⟩
    comp a2 ++ comp' a1 (ADD :: p) ==⟨ lemma-comp a2 (comp' a1 (ADD :: p)) ⟩
    comp' a2 (comp' a1 (ADD :: p))
  end  

-- Suggerimento: nella prova si usi rewrite con l'inversa di ++-assoc

++-assoc' : ∀{A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
++-assoc' xs ys zs = symm (++-assoc xs ys zs)


--------------------------------
-- Correttezza rispetto ad aval
--------------------------------

-- Il teorema stabilisce che l'esecuzione mediante un automa a pila
-- del risultato della compilazione di un'espressione a nello stato s
-- produce una pila il cui unico elemento è aval a s.

-- Per dimostrare il teorema si dimostri il seguente lemma, che
-- generalizza l'enunciato del teorema al caso in cui a sia compilato
-- dinanzi ad un programma p e che l'esecuzione inizi con uno stack
-- stk arbitrario

Lemma : ∀(a : Aexp) (s : State) (stk : Stack) (p : Prog)
           → exec (comp' a p) s stk == exec p s ((aval a s) :: stk)
Lemma (N x) s stk p = refl
Lemma (V x) s stk p = refl
Lemma (Plus a1 a2) s stk p =
  begin
    exec (comp' a2 (comp' a1 (ADD :: p))) s stk ==⟨ Lemma a2 s stk (comp' a1 (ADD :: p)) ⟩
    exec (comp' a1 (ADD :: p)) s ((aval a2 s) :: stk) ==⟨ Lemma a1 s (aval a2 s :: stk) (ADD :: p) ⟩
    exec (ADD :: p) s (aval a1 s :: (aval a2 s :: stk)) ==⟨⟩
    exec p s (aval (Plus a1 a2) s :: stk)
  end  

-- A questo punto basta specializzare Lemma al caso in cui p == [] e stk == []
Teorema : ∀(a : Aexp) (s : State) → exec (compile a) s [] == [(aval a s)]          
Teorema a s = Lemma a s [] []
