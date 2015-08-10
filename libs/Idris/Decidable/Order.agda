module Idris.Decidable.Order where
open import Idris.Prelude.Nat
open import Idris.Prelude.Basics -- Dec
open import Idris.Decidable.Decidable
-- import Decidable.Equality
open import Idris.Data.Fin hiding (shift)
-- import Data.Fun
-- import Data.Rel


--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Preorders, Posets, total Orders, Equivalencies, Congruencies
--------------------------------------------------------------------------------
{-
class Preorder t (po : t -> t -> Type) where
  total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c
  total reflexive : (a : t) -> po a a

class (Preorder t po) => Poset t (po : t -> t -> Type) where
  total antisymmetric : (a : t) -> (b : t) -> po a b -> po b a -> a = b

class (Poset t to) => Ordered t (to : t -> t -> Type) where
  total order : (a : t) -> (b : t) -> Either (to a b) (to b a)

class (Preorder t eq) => Equivalence t (eq : t -> t -> Type) where
  total symmetric : (a : t) -> (b : t) -> eq a b -> eq b a

class (Equivalence t eq) => Congruence t (f : t -> t) (eq : t -> t -> Type) where
  total congruent : (a : t) ->
                    (b : t) ->
                    eq a b ->
                    eq (f a) (f b)

minimum : (Ordered t to) => t -> t -> t
minimum {to} x y with (order {to} x y)
  | Left _ = x
  | Right _ = y

maximum : (Ordered t to) => t -> t -> t
maximum {to} x y with (order {to} x y)
  | Left _ = y
  | Right _ = x

--------------------------------------------------------------------------------
-- Syntactic equivalence (=)
--------------------------------------------------------------------------------

instance Preorder t ((=) {A = t} {B = t}) where
  transitive a b c = trans {a = a} {b = b} {c = c}
  reflexive a = Refl

instance Equivalence t ((=) {A = t} {B = t}) where
  symmetric a b prf = sym prf

instance Congruence t f ((=) {A = t} {B = t}) where
  congruent a b = cong {a = a} {b = b} f
-}

--------------------------------------------------------------------------------
-- Natural numbers
--------------------------------------------------------------------------------

LTEIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                           LTE m n -> LTE n o ->
                           LTE m o
LTEIsTransitive Z n o                 LTEZero                  nlteo   = LTEZero
LTEIsTransitive (S m) (S n) (S o) (LTESucc mlten)    (LTESucc nlteo)   = LTESucc (LTEIsTransitive m n o mlten nlteo)

LTEIsReflexive : (n : Nat) -> LTE n n
LTEIsReflexive Z      = LTEZero
LTEIsReflexive (S n)  = LTESucc (LTEIsReflexive n)

{-
instance Preorder Nat LTE where
  transitive = LTEIsTransitive
  reflexive  = LTEIsReflexive
-}

LTEIsAntisymmetric : (m : Nat) -> (n : Nat) ->
                     LTE m n -> LTE n m -> m == n
LTEIsAntisymmetric Z     Z      p       q  = Refl
LTEIsAntisymmetric Z     (S n)  LTEZero ()
LTEIsAntisymmetric (S m) Z      ()      q
LTEIsAntisymmetric (S m) (S n)  (LTESucc p) (LTESucc q) with LTEIsAntisymmetric m n p q
LTEIsAntisymmetric (S m) (S .m) (LTESucc p) (LTESucc q) | Refl = Refl

{-
instance Poset Nat LTE where
  antisymmetric = LTEIsAntisymmetric
-}

zeroNeverGreater : {n : Nat} -> LTE (S n) Z -> Void
zeroNeverGreater ()

zeroAlwaysSmaller : {n : Nat} -> LTE Z n
zeroAlwaysSmaller = LTEZero

ltesuccinjective : {n : Nat} -> {m : Nat} -> (LTE n m -> Void) -> LTE (S n) (S m) -> Void
ltesuccinjective {n} {m} disprf (LTESucc nLTEm) = void (disprf nLTEm)

decideLTE : (n : Nat) -> (m : Nat) -> Dec (LTE n m)
decideLTE    Z      y  = Yes LTEZero
decideLTE (S x)     Z  = No  (λ ())
decideLTE (S x)   (S y) with decideLTE x y
...  | Yes prf   = Yes (LTESucc prf)
...  | No contra = No (ltesuccinjective contra)

{- TODO
instance Decidable [Nat,Nat] LTE where
  decide = decideLTE
-}

-- lte : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
-- lte = decideLTE

shift : (m : Nat) -> (n : Nat) -> LTE m n -> LTE (S m) (S n)
shift m n mLTEn = LTESucc mLTEn

{-
instance Ordered Nat LTE where
  order Z      n = Left LTEZero
  order m      Z = Right LTEZero
  order (S k) (S j) with (order {to=LTE} k j)
    order (S k) (S j) | Left  prf = Left  (shift k j prf)
    order (S k) (S j) | Right prf = Right (shift j k prf)
-}

----------------------------------------------------------------------------------
---- Finite numbers
----------------------------------------------------------------------------------

module FinNum (k : Nat) where
  data FinLTE : Fin k -> Fin k -> Type where
    FromNatPrf : {m : Fin k} -> {n : Fin k} -> LTE (finToNat m) (finToNat n) -> FinLTE m n
{-
  instance Preorder (Fin k) FinLTE where
    transitive m n o (FromNatPrf p1) (FromNatPrf p2) =
      FromNatPrf (LTEIsTransitive (finToNat m) (finToNat n) (finToNat o) p1 p2)
    reflexive n = FromNatPrf (LTEIsReflexive (finToNat n))

  instance Poset (Fin k) FinLTE where
    antisymmetric m n (FromNatPrf p1) (FromNatPrf p2) =
      finToNatInjective m n (LTEIsAntisymmetric (finToNat m) (finToNat n) p1 p2)

  instance Decidable [Fin k, Fin k] FinLTE where
    decide m n with (decideLTE (finToNat m) (finToNat n))
      | Yes prf    = Yes (FromNatPrf prf)
      | No  disprf = No (\ (FromNatPrf prf) => disprf prf)

  instance Ordered (Fin k) FinLTE where
    order m n =
      either (Left . FromNatPrf)
             (Right . FromNatPrf)
             (order (finToNat m) (finToNat n))
-}
open FinNum
