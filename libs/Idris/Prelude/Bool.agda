module Idris.Prelude.Bool where

open import Idris.Builtins

-- import Idris.Prelude.Uninhabited

-- ||| Boolean Data Type
data Bool : Type where
  False : Bool
  True  : Bool

-- Connect the Bool type and the builtins
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  True  #-}
{-# BUILTIN FALSE False #-}

-- ||| The underlying implementation of the if ... then ... else ... syntax
-- ||| @ b the condition on the if
-- ||| @ t the value if b is true
-- ||| @ e the falue if b is false
boolElim : {a : Type} ->
           (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
boolElim True  t e = t
boolElim False t e = e

-- Syntactic sugar for boolean elimination.
-- syntax if [test] then [t] else [e] = boolElim test (Delay t) (Delay e)
if_then_else_ : {a : Type} -> (b : Bool) -> (t : Lazy a) -> (e : Lazy a) -> a
if_then_else_ = boolElim

-- Boolean Operator Precedence
infixl 4 _&&_ _||_

-- ||| Boolean OR only evaluates the second argument if the first is `False`.
_||_ : Bool -> Lazy Bool -> Bool
_||_ False x = x
_||_ True _  = True

-- ||| Boolean AND only evaluates the second argument if the first is `True`.
_&&_ : Bool -> Lazy Bool -> Bool
_&&_ True x  = x
_&&_ False _ = False

-- ||| Boolean NOT
not : Bool -> Bool
not True = False
not False = True
