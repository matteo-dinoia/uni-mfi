module Code.HoareLogic where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws 
open import Library.Equality
open import Library.Equality.Reasoning

open import Code.AexpBexp
open import Code.BigStep



Assn = State -> Set -- asserzione = predicato stato

data Triple : Set₁ where -- Ignoro 1 in set
     [_]_[_] : Assn -> Com -> Assn -> Triple
