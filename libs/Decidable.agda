module Decidable where

open import Idris.Builtins
open import Idris.Prelude.Basics public

Dec0 : Type -> Set1
Dec0 = Dec

Dec1 : {A : Type} -> (P : A -> Type) -> Set1
Dec1 {A} P = (a : A) -> Dec0 (P a)

DecEq0 : Type -> Set1
DecEq0 A = (a1 : A) -> (a2 : A) -> Dec (a1 == a2)

DecEq1 : {A : Type} -> (P : A -> Type) -> Set1
DecEq1 {A} P = (a : A) -> DecEq0 (P a)
