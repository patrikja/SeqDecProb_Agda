module Idris.Data.Vect where

open import Idris.Builtins
open import Idris.Prelude.Basics
open import Idris.Prelude.List as List
open import Idris.Prelude.Decidable.Equality
-- open import Idris.Language.Reflection
open import Idris.Data.VectType
open import Idris.Prelude.Nat

open Vect public

-- %access public
-- %default total

--------------------------------------------------------------------------------
-- Elem
--------------------------------------------------------------------------------

-- ||| A proof that some element is found in a vector
data Elem {a : Set} : {k : Nat} -> a -> Vect k a -> Type where
     Here  : forall {n x xs}   ->              Elem {k = S n} x (x :: xs)
     There : forall {n x y xs} -> Elem x xs -> Elem {k = S n} x (y :: xs)

-- ||| Nothing can be in an empty Vect
noEmptyElem : {a : Type} -> {x : a} -> Elem x [] -> Void
noEmptyElem {a} {x} ()

-- ||| An item not in the head and not in the tail is not in the Vect at all
neitherHereNorThere : {a : Type} -> {n : Nat} ->
                      {x y : a} -> {xs : Vect n a} -> Not (x == y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
neitherHereNorThere xneqy xninxs Here = xneqy Refl
neitherHereNorThere xneqy xninxs (There xinxs) = xninxs xinxs

-- ||| A decision procedure for Elem
isElem :  {a : Type} -> {n : Nat} ->
          {{da : DecEqDict a}} -> (x : a) -> (xs : Vect n a) -> Dec (Elem x xs)
isElem x [] = No noEmptyElem
isElem {{da}} x (y :: xs) with (DecEqDict.decEq da x y)
isElem x (.x :: xs) | (Yes Refl) = Yes Here
isElem x (y  :: xs) | (No xneqy) with (isElem x xs)
isElem x (y  :: xs) | (No xneqy) | (Yes xinxs) = Yes (There xinxs)
isElem x (y  :: xs) | (No xneqy) | (No xninxs) = No (neitherHereNorThere xneqy xninxs)

{- TODO
-- ||| A tactic for discovering where, if anywhere, an element is in a vector
-- ||| @ n how many elements to search before giving up
findElem : (n : Nat) -> List (TTName, Binder TT) -> TT -> Tactic
findElem Z ctxt goal = Refine "Here" `Seq` Solve
findElem (S n) ctxt goal = GoalType "Elem" (Try (Refine "Here" `Seq` Solve) (Refine "There" `Seq` (Solve `Seq` findElem n ctxt goal)))
-}

replaceElem : {k : Nat} -> {t : Type} -> {x : t} ->
              (xs : Vect k t) -> Elem x xs -> (y : t) -> (Sigma (Vect k t) (Elem y))
replaceElem (x :: xs) Here y = MkSigma (y :: xs) Here
replaceElem (x :: xs) (There xinxs) y with (replaceElem xs xinxs y)
...  | (MkSigma ys yinys) = MkSigma (x :: ys) (There yinys)

replaceByElem : {k : Nat} -> {t : Type} -> {x : t} ->
                (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceByElem (x :: xs) Here y = y :: xs
replaceByElem (x :: xs) (There xinxs) y = x :: replaceByElem xs xinxs y

mapElem : {k : Nat} -> {t u : Type} -> {x : t}
          {xs : Vect k t} -> {f : t -> u} -> Elem x xs -> Elem (f x) (Vect.map f xs)
mapElem Here      = Here
mapElem (There e) = There (mapElem e)
