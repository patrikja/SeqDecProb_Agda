module VectOperations where

open import Idris.Builtins
open import Idris.Prelude.Nat
open import Idris.Data.Vect hiding (filter)
open import Idris.Data.Fin
-- import Data.So

open import Decidable
open import TotalPreorder
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
...  | Yes prf   = MkSigma (S m) (a :: as')
...  | No contra = MkSigma    m        as'


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
... | (Yes p)     = MkSigma _ (MkSigma a p :: tail)
... | (No contra) = MkSigma _ tail



-- Searching

argmaxMax : {A : Type} -> {n : Nat} ->
            TotalPreorder A -> Vect n A -> LT Z n -> (Fin n × A)
argmaxMax {n = Z}       tp  []                 ()
argmaxMax {n = S Z}     tp (a :: [])           _ = (FZ , a)
argmaxMax {n = S (S m)} tp (a' :: (a'' :: as)) _ with (argmaxMax tp (a'' :: as) (ltZS m))
... | (k , max) with (TotalPreorder.total tp a' max)
...         | Left  x  = (FS k , max)
...         | Right x  = (FZ , a')

{- TODO

> |||
> argmax : {A : Type} ->
>          TotalPreorder A -> Vect n A -> LT Z n -> Fin n
> argmax tp as p = fst (argmaxMax tp as p)


> |||
> max : {A : Type} ->
>       TotalPreorder A -> Vect n A -> LT Z n -> A
> max tp as p = snd (argmaxMax tp as p)


> {-

> |||
> argmaxMax : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>             Vect (S n) A -> (Fin (S n), A)
> argmaxMax     {n = Z}   (a :: Nil) = (FZ, a)
> argmaxMax {A} {n = S m} (a :: (a' :: as)) with (preorder a (snd (argmaxMax (a' :: as))))
>   | (Left  _) = (FS (fst ka), snd ka) where
>     ka : (Fin (S m), A)
>     ka = argmaxMax (a' :: as)
>   | (Right _) = (FZ, a)


> |||
> argmax : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>          Vect (S n) A -> Fin (S n)
> argmax = fst . argmaxMax


> |||
> max : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>       Vect (S n) A -> A
> max = snd . argmaxMax

> -}


> {-

> |||
> argmaxMax : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>             Vect (S n) (A,F) -> (A,F)
> argmaxMax {n = Z}   (af :: Nil) = af
> argmaxMax {n = S m} (af :: (af' :: afs)) with (order (snd af) (snd (argmaxMax (af' :: afs))))
>   | (Left  _) = argmaxMax (af' :: afs)
>   | (Right _) = af


> |||
> argmax : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>          Vect (S n) (A,F) -> A
> argmax = fst . argmaxMax


> |||
> max : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>       Vect (S n) (A,F) -> F
> max = snd . argmaxMax

> ---}

-}
