module Util where
open import Idris.Builtins

pair : {a b c : Type} ->
       (a -> b) × (a -> c) -> (a ->   b × c)
pair (f , g) x = (f x , g x)
