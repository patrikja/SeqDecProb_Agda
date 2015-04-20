module VectProperties where

open import Idris.Builtins
open import Idris.Prelude.Basics
import Idris.Prelude.List as List
open import Idris.Data.Vect hiding (filter)
open import Idris.Data.Vect.Quantifiers
open import Idris.Prelude.Nat
open import Idris.Data.Fin
-- import Idris.Syntax.PreorderReasoning
open import Idris.Decidable.Order
open import Idris.Prelude.Pairs

open import Pro
open import VectOperations
open import Decidable
-- import Order
open import NatProperties
open import Util

{-
instance Uninhabited (Elem {a} x Nil) where
  uninhabited Here impossible
  uninhabited (There p) impossible
-}

-- Indexing and lookup

indexLemma : {t : Type} -> {n : Nat} ->
             (k : Fin n) -> (xs : Vect n t) -> Elem (index k xs) xs
indexLemma {n = Z}    ()    Nil
indexLemma {n = S m}  FZ    (x :: xs) = Here
indexLemma {n = S m} (FS k) (x :: xs) = There (indexLemma k xs)


indexLookupLemma : {alpha : Type} -> {n : Nat} ->
                   (x : alpha) ->
                   (xs : Vect n alpha) ->
                   (prf : Elem x xs) ->
                   index (lookup x xs prf) xs == x
indexLookupLemma x []          ()
indexLookupLemma x (.x :: xs)  Here       = Refl
indexLookupLemma x (x' :: xs) (There prf) = indexLookupLemma x xs prf


{- TODO: wrong in the Idris code?
-- %assert_total
lookupIndexLemma : {t : Type} -> {n : Nat} ->
                   (k : Fin n) ->
                   (xs : Vect n t) ->
                   (prf : Elem (index k xs) xs) ->
                   lookup (index k xs) xs prf == k
lookupIndexLemma i xs p = ?
lookupIndexLemma  FZ    (x :: xs)  Here       = Refl
lookupIndexLemma (FS k) (x :: xs) (There prf) =
  let ih = lookupIndexLemma k xs prf in {!rewrite ih in Refl!}
-}




-- Membership, quantifiers:

-- ||| Membership => non emptyness
elemLemma : {A : Type} -> {n : Nat} ->
            (a : A) -> (as : Vect n A) ->
            Elem a as -> LT Z n
elemLemma {n = Z}   a [] ()
elemLemma {n = S m} a as p  = ltZS m



AnyExistsLemma : {A : Type} -> {P : A -> Pro} -> {n : Nat} -> {as : Vect n A} -> Any P as -> Exists P
AnyExistsLemma (Here {x} px) = Evidence _ px
AnyExistsLemma (There prf)   = AnyExistsLemma prf


ElemAnyLemma : {A : Type} -> {P : A -> Pro} ->
               {a : A} -> {n : Nat} -> {as : Vect n A} ->
               P a -> Elem a as -> Any P as
ElemAnyLemma p Here      = Here p
ElemAnyLemma p (There e) = There (ElemAnyLemma p e)


decAny : {A : Type} -> {P : A -> Pro} -> {n : Nat} ->
         Dec1 {A} P -> Dec1 {Vect n A} (Any P)
decAny d1P = any d1P

-- Container monad properties

mapLemma : {A B : Type} -> {n : Nat} -> (as : Vect n A) -> (f : A -> B) ->
           (a : A) -> Elem a as -> Elem (f a) (map f as)
mapLemma  []       f a   ()
mapLemma (a :: as) f .a  Here       = Here
mapLemma (a :: as) f a' (There prf) = There (mapLemma as f a' prf)

mapIdfLemma : {A B : Type} -> {n : Nat} -> (as : Vect n A) -> (f : A -> B) ->
              (ab : A × B) -> Elem ab (map (pair (id , f)) as) ->
              f (fst ab) == snd ab
mapIdfLemma  []       f ab             ()
mapIdfLemma (x :: as) f (.x , .(f x))  Here       = Refl
mapIdfLemma (x :: as) f ab             (There p)  = mapIdfLemma as f ab p



-- Filtering

-- ||| |filter| preserves membership
filterLemma : {A : Type} ->
              {P : A -> Type} ->
              {n : Nat} ->
              (d1P : Dec1 P) ->
              (a : A) ->
              (as : Vect n A) ->
              Elem a as ->
              (p : P a) ->
              Elem a (Sigma.getProof (filter d1P as))
filterLemma d1P a   []         ()
filterLemma d1P a1 (.a1 :: as) Here p with (filter d1P as)
... | (MkSigma n as') with (d1P a1)
... | (Yes _)      = Here {x = a1} {xs = as'}
... | (No  contra) = void (contra p)
filterLemma d1P a1 (a2 :: as) (There prf) p
    with filter d1P as  |  filterLemma d1P a1 as prf p
...    | MkSigma n as'  |  q with (d1P a2)
filterLemma d1P a1 (a2 :: as) (There prf) p
       | MkSigma _ _    |  q    | Yes prf2 = There q
...                             | (No  _)  = q

{- TODO

-- ||| |filterTag| preserves membership
filterTagLemma : {A : Type} ->
                 {P : A -> Type} ->
                 (d1P : Dec1 P) ->
                 (a : A) ->
                 (as : Vect n A) ->
                 Elem a as ->
                 (p : P a) ->
                 Elem a (map Sigma.getWitness (getProof (filterTag d1P as)))
filterTagLemma d1P a   Nil       prf  p = absurd prf
filterTagLemma d1P a1 (a1 :: as) Here p with (filterTag d1P as)
...  | (n ** aps') with (d1P a1)
...    | (Yes _) = Here {x = a1} {xs = map Sigma.getWitness aps'}
...    | (No  contra) = void (contra p)
filterTagLemma d1P a1 (a2 :: as) (There prf) p with (filterTag d1P as)
...  | (n ** aps') with (d1P a2)
...    | (Yes _) = {! ?issue1920.2 !}-- There {x = a1} {xs = map Sigma.getWitness aps'} {y = a2} (filterTagLemma d1P a1 as prf p)
...    | (No  _) = {! ?issue1920.3 !}-- filterTagLemma d1P a1 as prf p


-- Max and argmax

{-

maxLemma : {A : Type} -> {TO : A -> A -> Type} -> {pre : Preordered A TO} ->
           (a : A) -> (as : Vect n A) -> (p : LT Z n) -> a `Elem` as ->
           TO a (max as p)
maxLemma {TO} {n = Z}       a  Nil                p  _          = absurd p
maxLemma {TO} {n = S Z}     a (a :: Nil)          _  Here       = reflexive a
maxLemma {TO} {n = S Z}     a (a' :: Nil)         _ (There prf) = absurd prf
maxLemma {TO} {n = S (S m)} a (a :: (a'' :: as))  _  Here       with (argmaxMax (a'' :: as) (ltZS m))
...  | (k, max) with (preorder a max)
...    | (Left  p) = p
...    | (Right _) = reflexive a
maxLemma {TO} {n = S (S m)} a (a' :: (a'' :: as)) _ (There prf) with (argmaxMax (a'' :: as) (ltZS m))
...  | (k, max) with (preorder a' max)
...    | (Left  _) = {! ?issue1920.4 !} -- maxLemma {TO} {n = S m} a (a'' :: as) (ltZS m) prf
...    | (Right p) = s3 where
      s1 : TO a (snd (VectOperations.argmaxMax (a'' :: as) (ltZS m)))
      s1 = maxLemma {TO} {n = S m} a (a'' :: as) (ltZS m) prf
      s2 : TO (snd (VectOperations.argmaxMax (a'' :: as) (ltZS m))) a'
      s2 = {! ?issue1920.5 !} -- p
      s3 : TO a a'
      s3 = transitive a (snd (VectOperations.argmaxMax (a'' :: as) (ltZS m))) a' s1 s2


argmaxLemma : {A : Type} -> {TO : A -> A -> Type} -> {pre : Preordered A TO} ->
              (as : Vect n A) -> (p : LT Z n) ->
              index (argmax as p) as = max as p
argmaxLemma {TO} {n = Z}        Nil              p = absurd p
argmaxLemma {TO} {n = S Z}     (a :: Nil)        p = Refl
argmaxLemma {TO} {n = S (S m)} (a' :: (a'' :: as)) p with (argmaxMax (a'' :: as) (ltZS m))
...  | (k, max) with (preorder a' max)
...    | (Left   _) = {! ?issue1920.6 !} -- argmaxLemma (a'' :: as) (ltZS m)
...    | (Right  _) = Refl


maxElemLemma : {A : Type} -> {TO : A -> A -> Type} -> {pre : Preordered A TO} ->
               (as : Vect n A) -> (p : LT Z n) ->
               Elem (max as p) as
maxElemLemma {TO} {n = Z}        Nil                p = absurd p
maxElemLemma {TO} {n = S Z}     (a :: Nil)          p = Here
maxElemLemma {TO} {n = S (S m)} (a' :: (a'' :: as)) p with (argmaxMax (a'' :: as) (ltZS m))
...  | (k, max) with (preorder a' max)
...    | (Left   _) = {! ?issue1920.7 !} -- There (maxElemLemma (a'' :: as) (ltZS m))
...    | (Right  _) = Here


{-

|||
maxLemma : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
           (a : A) -> (as : Vect (S n) A) -> a `Elem` as ->
           TO a (max as)
maxLemma {TO} {n = Z}   a (a :: Nil)          Here       = reflexive a
maxLemma {TO} {n = Z}   a (a' :: Nil)        (There prf) = absurd prf
maxLemma {TO} {n = S m} a (a :: (a'' :: as))  Here with (preorder a (max (a'' :: as)))
  | (Left  p) = p
  | (Right _) = reflexive a
maxLemma {TO} {n = S m} a (a' :: (a'' :: as)) (There prf) with (preorder a' (max (a'' :: as)))
  | (Left  _) = maxLemma a (a'' :: as) prf
  | (Right p) = s3 where
    s1 : TO a (max (a'' :: as))
    s1 = maxLemma a (a'' :: as) prf
    s2 : TO (max (a'' :: as)) a'
    s2 = p
    s3 : TO a a'
    s3 = transitive a (max (a'' :: as)) a' s1 s2


|||
argmaxLemma : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
              (as : Vect (S n) A) ->
              index (argmax as) as = max as
argmaxLemma {TO} {n = Z}   (a :: Nil) = Refl
argmaxLemma {TO} {n = S m} (a :: (a' :: as)) with (preorder a (max (a' :: as)))
  | (Left   _) = argmaxLemma (a' :: as)
  | (Right  _) = Refl

-}


{-

|||
maxLemma : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
           (af : (A,F)) -> (afs : Vect (S n) (A,F)) -> af `Elem` afs ->
           TO (snd af) (max afs)
maxLemma {A} {F} {TO} {n = Z}   af (af :: Nil)   Here       = reflexive (snd af)
maxLemma {A} {F} {TO} {n = Z}   af (af' :: Nil) (There prf) = absurd prf
maxLemma {A} {F} {TO} {n = S m} af (af :: (af'' :: afs)) Here with (order (snd af) (snd (argmaxMax (af'' :: afs))))
  | (Left  p) = p
  | (Right _) = reflexive (snd af)
maxLemma {A} {F} {TO} {n = S m} af (af' :: (af'' :: afs)) (There prf) with (order (snd af') (snd (argmaxMax (af'' :: afs))))
  | (Left  _) = maxLemma {A} {F} {TO} {n = m} af (af'' :: afs) prf
  | (Right p) = s3 where
    s1 : TO (snd af) (max (af'' :: afs))
    s1 = maxLemma {A} {F} {TO} {n = m} af (af'' :: afs) prf
    s2 : TO (max (af'' :: afs)) (snd af')
    s2 = p
    s3 : TO (snd af) (snd af')
    s3 = transitive (snd af) (VectOperations.max (af'' :: afs)) (snd af') s1 s2

-}

-}
-}
