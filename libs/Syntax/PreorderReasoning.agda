module Syntax.PreorderReasoning where
open import Builtins

data _==_  {l} {a : Set l} (x : a) : {b : Set l} -> (y : b) -> Set where
  Refl : x == x

module Equal {a : Type} where
    qed : (x : a) -> x == x
    qed x = Refl
    step : {y : a} -> {z : a} -> (x : a) -> x == y -> (y == z) -> x == z
    step x Refl Refl = Refl

open Equal
_QED = qed

{-
-- QED is first to get the precedence to work out. It's just Refl with an explicit argument.
-- foo ={ prf }= bar ={ prf' }= fnord QED
-- is a proof that foo is related to fnord, with the intermediate step being bar, justified by prf and prf'
syntax [from] "={" [prf] "}=" [to] = step from prf to
-}
_==<_>==_ = step


subst : forall {a} {l} {A : Set a} (P : A → Set l) {x y : A} -> x == y -> P x -> P y
subst P Refl p = p

sym : {a : Type} -> {b : Type} ->
      {x : a}    -> {y : b}    ->
      (x == y) -> (y == x)
sym Refl = Refl

