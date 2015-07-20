module Idris.Prelude.Decidable.Equality where

open import Idris.Builtins
open import Idris.Prelude.Basics
open import Idris.Prelude.Bool
-- import Prelude.Classes
open import Idris.Prelude.Either
-- import Prelude.List
open import Idris.Prelude.Nat
open import Idris.Prelude.Maybe

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

-- ||| The negation of equality is symmetric (follows from symmetry of equality)
negEqSym : {t : Type} ->
           {a : t} -> {b : t} -> (a == b -> Void) -> (b == a -> Void)
negEqSym p h = p (sym h)


--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

DecEqDict' : Type -> Type
DecEqDict' t = (x1 : t) -> (x2 : t) -> Dec (x1 == x2)

record DecEqDict (a : Type) : Type where
  field
    decEq : DecEqDict' a

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

decEqUnit : DecEqDict' Unit
decEqUnit unit unit = Yes Refl

decEqDictUnit : DecEqDict Unit
decEqDictUnit = record { decEq = decEqUnit }

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------
trueNotFalse : True == False -> Void
trueNotFalse ()

-- instance DecEq Bool where

decEqBool : DecEqDict' Bool
decEqBool True  True  = Yes Refl
decEqBool False False = Yes Refl
decEqBool True  False = No trueNotFalse
decEqBool False True  = No (negEqSym trueNotFalse)

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

ZnotS : {n : Nat} ->
        Z == S n -> Void
ZnotS ()


-- instance DecEq Nat where
-- decEqNat already defined in Idris.Prelude.Nat

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

nothingNotJust : {t : Type} ->
                 {x : t} -> (Nothing {a = t} == Just x) -> Void
nothingNotJust ()

-- instance (DecEq t) => DecEq (Maybe t) where
decEqMaybe : {a : Type} -> DecEqDict a -> DecEqDict' (Maybe a)
decEqMaybe _ Nothing Nothing = Yes Refl
decEqMaybe da (Just x') (Just y') with (DecEqDict.decEq da x' y')
... | Yes p  = Yes (cong Just p)
... | No  p  = No (\h -> p (justInjective h))
decEqMaybe _ Nothing (Just _) = No nothingNotJust
decEqMaybe _ (Just _) Nothing = No (negEqSym nothingNotJust)

decEqDictMaybe : {a : Type} -> DecEqDict a -> DecEqDict (Maybe a)
decEqDictMaybe da = record { decEq = decEqMaybe da }


--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

leftNotRight : {a : Type} -> {b : Type} ->
               {x : a} -> {y : b} -> Left {b = b} x == Right {a = a} y -> Void
leftNotRight ()


-- instance (DecEq a, DecEq b) => DecEq (Either a b) where
decEqEither : {a : Type} -> {b : Type} ->
              DecEqDict a -> DecEqDict b -> DecEqDict' (Either a b)
decEqEither da db (Left x') (Left y') with (DecEqDict.decEq da x' y')
... | Yes p = Yes (cong Left p)
... | No p = No (\h -> p (leftInjective h))
decEqEither da db (Right x') (Right y') with (DecEqDict.decEq db x' y')
... | Yes p = Yes (cong Right p)
... | No p = No (\h -> p (rightInjective h))
decEqEither da db (Left x') (Right y') = No leftNotRight
decEqEither da db (Right x') (Left y') = No (negEqSym leftNotRight)


--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

lemmaEitherNoNo :  {a b : Type} ->
             {xa ya : a} -> {xb yb : b} ->
             Either (xa == ya → Void) (xb == yb → Void) ->
             (xa , xb) == (ya , yb) → Void
lemmaEitherNoNo (Left  na) Refl = na Refl
lemmaEitherNoNo (Right nb) Refl = nb Refl

-- instance (DecEq a, DecEq b) => DecEq (a, b) where
decEqPair : {a : Type} -> {b : Type} ->
            DecEqDict a -> DecEqDict b -> DecEqDict' (a × b)
decEqPair da db (xa , xb) (ya , yb) with DecEqDict.decEq da xa ya | DecEqDict.decEq db xb yb
... | Yes prfa    | Yes prfb    = Yes (cong2 _,_ prfa prfb)
... | Yes prfa    | No contrab  = No (lemmaEitherNoNo (Right contrab))
... | No contraa  | _           = No (lemmaEitherNoNo (Left  contraa))

{- TODO rest of the file

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

lemma_val_not_nil : {x : t, xs : List t} -> ((x :: xs) = Prelude.List.Nil {a = t} -> Void)
lemma_val_not_nil Refl impossible

lemma_x_eq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y) -> (xs = ys -> Void) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_eq_xs_neq Refl p Refl = p Refl

lemma_x_neq_xs_eq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> Void) -> (xs = ys) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_eq p Refl Refl = p Refl

lemma_x_neq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> Void) -> (xs = ys -> Void) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_neq p p' Refl = p Refl

instance DecEq a => DecEq (List a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) [] = No lemma_val_not_nil
  decEq [] (x :: xs) = No (negEqSym lemma_val_not_nil)
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys) | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No p) = No (\eq => lemma_x_eq_xs_neq Refl p eq)
    decEq (x :: xs) (y :: ys) | No p with (decEq xs ys)
      decEq (x :: xs) (y :: xs) | (No p) | (Yes Refl) = No (\eq => lemma_x_neq_xs_eq p Refl eq)
      decEq (x :: xs) (y :: ys) | (No p) | (No p') = No (\eq => lemma_x_neq_xs_neq p p' eq)


-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations.

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

instance DecEq Int where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Char
--------------------------------------------------------------------------------

instance DecEq Char where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Integer
--------------------------------------------------------------------------------

instance DecEq Integer where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void


--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------

instance DecEq String where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void
-}
