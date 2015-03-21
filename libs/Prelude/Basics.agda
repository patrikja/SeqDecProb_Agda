module Prelude.Basics where

open import Builtins public
open import Syntax.PreorderReasoning public

Not : Type -> Type
Not a = a -> Void

-- ||| Identity function.
id : {a : Type} -> 
     a -> a
id x = x

-- ||| Manually assign a type to an expression.
-- ||| @ a the type to assign
-- ||| @ x the element to get the type
the : (a : Type) -> (x : a) -> a
the _ = id

-- ||| Constant function. Ignores its second argument.
const : {a : Type} -> {b : Type} -> 
        a -> b -> a
const x = \v -> x

-- ||| Return the first element of a pair.
fst : {s : Type} -> {t : Type} -> 
      (s × t) -> s
fst (x , y) = x

-- ||| Return the second element of a pair.
snd : {a : Type} -> {b : Type} -> 
      (a × b) -> b
snd (x , y) = y

infixl 9 _∘_

-- ||| Function composition
_∘_ : {a : Type} -> {b : Type} -> {c : Type} -> 
      (b -> c) -> (a -> b) -> a -> c
_∘_ f g x = f (g x)

-- ||| Takes in the first two arguments in reverse order.
-- ||| @ f the function to flip
flip : {a : Type} -> {b : Type} -> {c : Type} -> 
       (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

-- ||| Function application.
apply : {a : Type} -> {b : Type} -> 
        (a -> b) -> a -> b
apply f a = f a

-- ||| Equality is a congruence.
cong : {t : Type} -> {u : Type} -> 
       {f : t -> u} -> {a : t} -> {b : t} -> 
                       (a == b) -> f a == f b
cong Refl = Refl
-- A stronger heterogenous variant of cong would be useful sometimes.
-- See ../Syntax/PreorderReasoning.agda

-- ||| Decidability. A decidable property either holds or is a contradiction.
data Dec : Type -> Set1 where

  -- ||| The case where the property holds
  -- ||| @ prf the proof
  Yes : {A : Type} -> (prf : A) -> Dec A

  -- ||| The case where the property holding would be a contradiction
  -- ||| @ contra a demonstration that A would be a contradiction
  No  : {A : Type} -> (contra : A -> Void) -> Dec A

