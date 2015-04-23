module Preorder where
open import Idris.Builtins

-- ||| Preorder
record Preorder (A : Type) : Set1 where
  constructor MkPreorder
  field
    R : A -> A -> Type
    reflexive : (x : A) -> R x x
    transitive : (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z
