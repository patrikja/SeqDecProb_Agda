module Idris.Data.Vect.Quantifiers where
open import Idris.Builtins
open import Idris.Prelude.Nat
open import Idris.Prelude.Basics -- Dec
open import Idris.Data.Vect

-- ||| A proof that some element of a vector satisfies some property
-- |||
-- ||| @ P the property to be satsified
data Any {a : Type} (P : a -> Type) : {n : Nat} -> Vect n a -> Type where
  -- ||| A proof that the satisfying element is the first one in the `Vect`
  Here  : {n : Nat} -> {x : a} -> {xs : Vect n a} ->     P x  -> Any P (x :: xs)
  -- ||| A proof that the satsifying element is in the tail of the `Vect`
  There : {n : Nat} -> {x : a} -> {xs : Vect n a} -> Any P xs -> Any P (x :: xs)

-- ||| No element of an empty vector satisfies any property
anyNilAbsurd : {a : Type} ->
               {P : a -> Type} -> Any P [] -> Void
anyNilAbsurd ()

{-
instance Uninhabited (Any p []) where
  uninhabited = anyNilAbsurd
-}

anyElim : {a : Type} -> {b : Type} -> {n : Nat} -> {x : a} ->
          {xs : Vect n a} -> {P : a -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ f (Here p) = f p
anyElim f _ (There p) = f p

-- ||| Given a decision procedure for a property, determine if an element of a
-- ||| vector satisfies it.
-- |||
-- ||| @ P the property to be satisfied
-- ||| @ dec the decision procedure
-- ||| @ xs the vector to examine
any : {a : Type} -> {n : Nat} ->
      {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : Vect n a) -> Dec (Any P xs)
any _ [] = No anyNilAbsurd
any p (x :: xs) with p x
any p (x :: xs) | Yes prf = Yes (Here prf)
any p (x :: xs) | No contra with any p xs
any p (x :: xs) | No contra | Yes prf     = Yes (There prf)
any p (x :: xs) | No contra | No contra2  = No (anyElim contra2 contra)


-- ||| A proof that all elements of a vector satisfy a property. It is a list of
-- ||| proofs, corresponding element-wise to the `Vect`.
data All {a : Type} (P : a -> Type) : {n : Nat} -> Vect n a -> Type where
  []   : All P []
  _::_ : {n : Nat} -> {x : a} -> {xs : Vect n a} -> P x -> All P xs -> All P (x :: xs)


-- ||| If there does not exist an element that satifies the property, then it is
-- ||| the case that all elements do not satisfy.
negAnyAll : {a : Type} {n : Nat} ->
            {P : a -> Type} -> {xs : Vect n a} -> Not (Any P xs) -> All (\x -> Not (P x)) xs
negAnyAll {xs = []} _ = []
negAnyAll {xs = (x :: xs)} f = (\x -> f (Here x)) :: negAnyAll (\x -> f (There x))


notAllHere : {a : Type} -> {n : Nat} ->
             {P : a -> Type} -> {x : a} -> {xs : Vect n a} -> Not (P x) -> All P (x :: xs) -> Void
-- notAllHere _ [] impossible
notAllHere np (p :: _) = np p

notAllThere : {a : Type} -> {n : Nat} ->
              {P : a -> Type} -> {x : a} -> {xs : Vect n a} -> Not (All P xs) -> All P (x :: xs) -> Void
-- notAllThere _ [] impossible
notAllThere np (_ :: ps) = np ps


-- ||| Given a decision procedure for a property, decide whether all elements of
-- ||| a vector satisfy it.
-- |||
-- ||| @ P the property
-- ||| @ dec the decision procedure
-- ||| @ xs the vector to examine
all : {a : Type} -> {n : Nat} ->
      {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : Vect n a) -> Dec (All P xs)
all _ [] = Yes []
all d (x :: xs) with (d x)
all d (x :: xs) | No prf = No (notAllHere prf)
all d (x :: xs) | Yes prf with all d xs
all d (x :: xs) | Yes prf | Yes prf' = Yes (prf :: prf')
all d (x :: xs) | Yes _   | No prf'  = No (notAllThere prf')
