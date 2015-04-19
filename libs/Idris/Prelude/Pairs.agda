module Idris.Prelude.Pairs where

open import Idris.Builtins

-- %access public
-- %default total

-- ||| Dependent pair where the first field is erased.
record Exists {a : Type} (P : a -> Type) : Type where
  constructor Evidence
  field
     getWitness  : a
     getProof    : P getWitness

-- ||| Dependent pair where the second field is erased.
record Subset (a : Type) (P : a -> Type) : Type where
  constructor Element
  field
    getWitness : a
    getProof   : P getWitness
