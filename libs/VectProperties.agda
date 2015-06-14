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

-- Injectivity (of |flip index|):

-- ||| Injectivity (one direction)
Injective1 : {t : Type} -> {n : Nat} ->
             Vect n t -> Type
Injective1 {t} {n} xs = (i : Fin n) -> (j : Fin n) -> index i xs == index j xs  ->  i == j


-- ||| Injectivity (the other direction)
Injective2 : {t : Type} -> {n : Nat} ->
             Vect n t -> Type
Injective2 {t} {n} xs = (i : Fin n) -> (j : Fin n) -> Not (i == j) -> Not (index i xs == index j xs)

help : {n : Nat} -> {i j : Fin n} ->
       Not (i == j) -> Not (FS i == FS j)
help nij Refl = nij Refl

tailInj2 :  {t : Type} -> {n : Nat} ->
            (x : t) -> (xs : Vect n t) -> Injective2 (x :: xs) -> Injective2 xs
tailInj2 x xs inj2  i j nij nindij = inj2 (FS i) (FS j) (help nij) nindij



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

-- Elem can be seen as a Fin n with a proof
elemToIndex : {a : Type} -> {n : Nat} ->
              (x : a) -> (xs : Vect n a) ->
              Elem x xs -> Sigma (Fin n) (\i -> x == index i xs)
elemToIndex x ._ Here = MkSigma FZ Refl
elemToIndex x (._ :: xs) (There el) with elemToIndex x xs el
elemToIndex x (._ :: xs) (There el) | MkSigma j p = MkSigma (FS j) p

lookupIndexLemma : {t : Type} -> {n : Nat} ->
                   (k : Fin n) ->
                   (xs : Vect n t) ->
                   (p : Injective2 xs) ->
                   (q : Elem (index k xs) xs) ->
                   lookup (index k xs) xs q == k
lookupIndexLemma k  []        inj2 ()
lookupIndexLemma FZ (x :: xs) inj2 Here = Refl

lookupIndexLemma FZ (x :: xs) inj2 (There q) with elemToIndex _ _ q
lookupIndexLemma FZ (x :: xs) inj2 (There q) | MkSigma j z with inj2 FZ (FS j) (\()) z
... | ()    -- x is in two places which contradicts Injective2
lookupIndexLemma (FS i) (.(index i xs) :: xs) inj2 Here with inj2 (FS i) FZ (\()) Refl
... | ()    -- x is in two places which contradicts Injective2
lookupIndexLemma (FS i) (x :: xs) inj2 (There q) = cong {f = FS} (lookupIndexLemma i xs (tailInj2 x xs inj2) q)

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



-- ||| |filterTag| preserves membership
filterTagLemma : {A : Type} ->
                 {P : A -> Type} ->
                 {n : Nat} ->
                 (d1P : Dec1 P) ->
                 (a : A) ->
                 (as : Vect n A) ->
                 Elem a as ->
                 (p : P a) ->
                 Elem a (map Sigma.getWitness (Sigma.getProof (filterTag d1P as)))
filterTagLemma d1P a   []       ()
filterTagLemma d1P a1 (.a1 :: as) Here p with (filterTag d1P as)
...  | MkSigma n aps' with (d1P a1)
...    | (Yes _)      = Here
...    | (No  contra) = void (contra p)
filterTagLemma d1P a1 (a2 :: as) (There prf) p
  with filterTag d1P as  |  filterTagLemma d1P a1 as prf p  |  (d1P a2)
...  | MkSigma _ _ | q | Yes _ = There q
...  | MkSigma _ _ | q | No _  = q

-- Max and argmax

-- I think Elem mx as is equivalent to Sigma (Fin (S n)) (\i -> index i as == mx)
-- TODO: This equivalence indicates that we should stick to one form (Elem or argmax), not both.
ind2Elem : {A : Type}  -> {n : Nat} ->
           (a : A)     -> (as : Vect n A) ->
           (i : Fin n) -> (index i as == a) -> Elem a as
ind2Elem a (.a :: as) FZ     Refl = Here
ind2Elem a (x  :: as) (FS i) p    = There (ind2Elem a as i p)

module MaxAndArgmax {A : Type} (tp : TotalPreorder A) where
-- factors out the common parameters A and tp from the definitions
-- introduce a few short names for record components for readability
  open TotalPreorder tp  -- brings R, reflexive, ... into scope
  _<=_ = R

  upperBound : {n : Nat} -> Vect n A -> A -> Pro
  upperBound as max = forall (a : A) -> Elem a as -> (a <= max)

  -- The only element in a singleton list is an upper bound
  upperBoundSing : (a : A) -> upperBound (a :: []) a
  upperBoundSing a .a Here = reflexive a
  upperBoundSing a b (There ())

  upperBoundCons : {n : Nat} ->
                   (a a' : A) -> (as : Vect n A) -> (mx : A) ->
                   (a <= mx) ->
                   Elem mx          (a' :: as) ->
                   upperBound (      a' :: as)   mx ->
                   upperBound (a :: (a' :: as))  mx
  upperBoundCons a a' as mx a<=mx el upbTail .a Here     = a<=mx
  upperBoundCons a a' as mx a<=mx el upbTail b (There p) = upbTail b p

  upperBoundCons2 : {n : Nat} ->
                    (mx a' : A) -> (as : Vect n A) ->
                    upperBound (       a' :: as)   mx ->
                    upperBound (mx :: (a' :: as))  mx
  upperBoundCons2 mx a' as upbTail .mx Here       = reflexive mx
  upperBoundCons2 mx a' as upbTail b (There elb)  = upbTail b elb

  allAboutMax : {n : Nat} ->
                (as : Vect n A) -> LT Z n ->
                Sigma (Fin n) (\i ->     Sigma A (\max ->
                         (index i as == max) × (upperBound as max)))
  allAboutMax [] ()
  allAboutMax (mx :: [])      p = MkSigma FZ (MkSigma mx (Refl , upperBoundSing mx))
  allAboutMax {n = S (S m)} (a :: (a' :: as)) p with allAboutMax (a' :: as) (LTESucc LTEZero)
  ... | MkSigma i' (MkSigma mx' (ind , upb)) with totalPre a mx'
  ...   | Left  q = MkSigma (FS i') (MkSigma mx' (ind  , upperBoundCons a a' as mx' q
                                                           (ind2Elem mx' (a' :: as) i' ind) upb))
  ...   | Right q = MkSigma FZ      (MkSigma a   (Refl , upperBoundCons2 a a' as
                                                           (λ a₁ z → transitive a₁ mx' a (upb a₁ z   ) q)))
  max : {n : Nat} ->
        Vect n A -> LT Z n -> A
  max as p with allAboutMax as p
  ... | MkSigma _i (MkSigma mx _) = mx

  maxLemma : {n : Nat} ->
             (a : A) -> (as : Vect n A) -> (p : LT Z n) -> Elem a as ->
             (a <= max as p)
  maxLemma a as p x with allAboutMax as p
  ... | MkSigma _i (MkSigma _mx (_ind , upb)) = upb a x

  argmax : {n : Nat} ->
           Vect n A -> LT Z n -> Fin n
  argmax as p with allAboutMax as p
  ... | MkSigma i _ = i

  argmaxLemma : {n : Nat} ->
                (as : Vect n A) -> (p : LT Z n) ->
                index (argmax as p) as == max as p
  argmaxLemma as p with allAboutMax as p
  argmaxLemma as p | MkSigma i (MkSigma _mx (ind , _upb)) = ind

open MaxAndArgmax public
