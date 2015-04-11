module Syntax.PreorderReasoning where
open import Builtins

module Equal where
    qed : {a : Type} ->
          (x : a) -> x == x
    qed x = Refl
    step : {a : Type} -> {b : Type} -> {c : Type} ->
           {y : b} -> {z : c} -> (x : a) -> x == y -> (y == z) -> x == z
    step x Refl Refl = Refl

open Equal
_QED = qed

{-
-- QED is first to get the precedence to work out. It's just Refl with an explicit argument.
-- foo ={ prf }= bar ={ prf' }= fnord QED
-- is a proof that foo is related to fnord, with the intermediate step being bar, justified by prf and prf'
syntax [from] "={" [prf] "}=" [to] = step from prf to
-}

infixr 2 _==<_>==_

_==<_>==_ = step

infix  2 _QED

subst : forall {a} {l} {A : Set a} (P : A → Set l) {x y : A} -> x == y -> P x -> P y
subst P Refl p = p

substEq : forall {a} {l} {A : Set a} (P : A → Set l) {x y : A} -> (eq : x == y) -> (p : P x) -> subst P eq p == p
substEq P Refl p = Refl

sym : {a : Type} -> {b : Type} ->
      {x : a}    -> {y : b}    ->
      (x == y) -> (y == x)
sym Refl = Refl

trans : {a : Type} -> {b : Type} -> {c : Type} ->
        {x : a}    -> {y : b}    -> {z : c}    ->
        (x == y)   -> (y == z)   -> (x == z)
trans Refl Refl = Refl

-- Perhaps needed
hcong' : forall {α} {β} {γ} -> {I : Set α} {i j : I} ->
          (A : I -> Set β) {B : {k : I} -> A k -> Set γ} {x : A i} {y : A j}
       -> i == j
       -> (f : {k : I} -> (x : A k) -> B x)
       -> x == y
       -> f x == f y
hcong' _ Refl _ Refl = Refl

cong2 : {A : Type} -> {B : A -> Type} -> {B' : A -> Type} ->
        (f : (a : A) -> B a -> B' a) ->
        {a a' : A} -> (a == a') ->
        {b : B a} ->  {b' : B a'} -> (b == b') ->
        f a b == f a' b'
cong2 f Refl Refl = Refl
