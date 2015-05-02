module VectOperations where

open import Idris.Builtins
open import Idris.Prelude.Nat
open import Idris.Data.Vect hiding (filter)
open import Idris.Data.Fin
-- import Data.So

open import Decidable
open import TotalPreorder public
-- import TotalPreorderOperations
open import NatProperties


-- Lookup

-- ||| Lookup the index of an element of a vector
lookup : {A : Type} -> {n : Nat} -> (a : A) -> (as : Vect n A) -> Elem a as -> Fin n
lookup {n = Z}   a  Nil        ()
lookup {n = S m} a (.a :: as)  Here       = FZ
lookup {n = S m} a (a' :: as) (There prf) = FS (lookup a as prf)


-- Container monad operations

-- Filtering

-- ||| Filters a vector on a decidable property
filter : {A : Type} ->
         {P : A -> Type} ->
         {n : Nat} ->
         Dec1 P ->
         Vect n A ->
         Sigma Nat (\m -> Vect m A)
filter d1P [] = MkSigma Z []
filter d1P (a :: as) with (filter d1P as)
... | MkSigma m as' with (d1P a)
...   | Yes prf   = MkSigma (S m) (a :: as')
...   | No contra = MkSigma    m        as'


-- ||| Filters a vector on a decidable property and pairs elements with proofs
filterTag : {A : Type} ->
            {P : A -> Type} ->
            {n : Nat} ->
            Dec1 P ->
            Vect n A ->
            Sigma Nat (\m -> Vect m (Sigma A P))
filterTag d1P [] = MkSigma Z []
filterTag d1P (a :: as) with (filterTag d1P as)
... | MkSigma _ tail with (d1P a)
...   | (Yes p)     = MkSigma _ (MkSigma a p :: tail)
...   | (No contra) = MkSigma _ tail



-- Searching

argmaxMax : {A : Type} -> {n : Nat} ->
            TotalPreorder A -> Vect n A -> LT Z n -> (Fin n × A)
argmaxMax {n = Z}       tp  []                 ()
argmaxMax {n = S Z}     tp (a :: [])           _ = (FZ , a)
argmaxMax {n = S (S m)} tp (a' :: (a'' :: as)) _ with (TotalPreorder.totalPre tp a' a'')
... | Right x  = (FZ , a')
... | Left  x with (argmaxMax tp (a'' :: as) (ltZS m))
...   | (k , max) = (FS k , max)
