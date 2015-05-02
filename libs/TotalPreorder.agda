module TotalPreorder where
open import Idris.Builtins
open import Idris.Prelude.Either public
-- import Preorder -- not used

-- ||| TotalPreorder
record TotalPreorder (A : Type) : Set1 where
  constructor MkTotalPreorder
  field
    R : A -> A -> Type
    reflexive  : (x : A) -> R x x
    transitive : (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z
    totalPre   : (x : A) -> (y : A) -> Either (R x y) (R y x)
