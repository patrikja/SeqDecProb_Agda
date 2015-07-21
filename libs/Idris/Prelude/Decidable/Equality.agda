module Idris.Prelude.Decidable.Equality where

open import Idris.Builtins
open import Idris.Prelude.Basics
open import Idris.Prelude.Bool
open import Idris.Prelude.Classes
open import Idris.Prelude.Either
open import Idris.Prelude.List
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

decEqDictEither : {a : Type} -> {b : Type} ->
                  DecEqDict a -> DecEqDict b -> DecEqDict (Either a b)
decEqDictEither da db = record { decEq = decEqEither da db }
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

decEqDictPair : {a : Type} -> {b : Type} ->
                DecEqDict a -> DecEqDict b -> DecEqDict (a × b)
decEqDictPair da db = record { decEq = decEqPair da db }


--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

lemma_x_eq_xs_neq : {t : Type} -> {x : t} -> {xs : List t} -> {y : t} -> {ys : List t} -> (x == y) -> (xs == ys -> Void) -> ((x :: xs) == (y :: ys) -> Void)
lemma_x_eq_xs_neq Refl p Refl = p Refl


lemma_x_neq_xs_eq : {t : Type} -> {x : t} -> {xs : List t} -> {y : t} -> {ys : List t} -> (x == y -> Void) -> (xs == ys) -> ((x :: xs) == (y :: ys) -> Void)
lemma_x_neq_xs_eq p Refl Refl = p Refl


lemma_x_neq_xs_neq : {t : Type} -> {x : t} -> {xs : List t} -> {y : t} -> {ys : List t} -> (x == y -> Void) -> (xs == ys -> Void) -> ((x :: xs) == (y :: ys) -> Void)
lemma_x_neq_xs_neq p p' Refl = p Refl


lemmaEitherNoNoList :  {a : Type} ->
             {xa ya : a} -> {xb yb : List a} ->
             Either (xa == ya → Void) (xb == yb → Void) ->
             (xa :: xb) == (ya :: yb) → Void
lemmaEitherNoNoList (Left  na) Refl = na Refl
lemmaEitherNoNoList (Right nb) Refl = nb Refl


-- instance DecEq a => DecEq (List a) where
decEqList : {a : Type} -> DecEqDict a -> DecEqDict' (List a)
decEqList da [] [] = Yes Refl
decEqList da [] (x :: ys) = No (λ ())
decEqList da (x :: xs) [] = No (λ ())
decEqList da (x :: xs) (y :: ys) with DecEqDict.decEq da x y | decEqList da xs ys
decEqList da (x :: xs) (.x :: .xs)  | Yes Refl   | Yes Refl   = Yes Refl
decEqList da (x :: xs) (.x :: ys)   | Yes Refl   | No contra  = No (lemmaEitherNoNoList (Right contra))
decEqList da (x :: xs) (y :: ys)    | No contra  | q          = No (lemmaEitherNoNoList (Left contra))

decEqDictList : {a : Type} -> DecEqDict a -> DecEqDict (List a)
decEqDictList da = record { decEq = decEqList da }

-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations.

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

-- instance DecEq Int where
decEqInt : DecEqDict' Int
decEqInt x y = if primIntegerEquality x y  then  Yes primitiveEq
                                           else  No  primitiveNotEq
       where postulate
               primitiveEq : x == y
               primitiveNotEq : x == y -> Void

decEqDictInt : DecEqDict Int
decEqDictInt = record { decEq = decEqInt }

{- TODO rest of the file
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
