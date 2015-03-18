module Syntax.PreorderReasoning where

data _==_ {a : Set} (x : a) : {b : Set} -> (y : b) -> Set where
  Refl : x == x  
