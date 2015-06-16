module Idris.Builtins where
Type = Set
Lazy : Type -> Type
Lazy A = A
Force : {A : Type} -> A -> A
Force x = x
data Void : Set where
void : {a : Type} -> Void -> a
void ()

infixr 2 _×_
infixr 4 _,_
-- data _×_ (a : Set) (b : Set) : Set where
--   _,_ : a -> b -> a × b

record _×_ (a : Set) (b : Set) : Set where
   constructor _,_
   field
     fst : a
     snd : b

record Sigma (a : Type) (P : a -> Type) : Type where
    constructor MkSigma
    field
      getWitness : a
      getProof   : P getWitness

-- data Sigma (a : Type) (P : a -> Type) : Type where
--    MkSigma : (x : a) -> (pf : P x) -> Sigma a P

data Unit : Type where unit : Unit

data _==_  {l} {a : Set l} (x : a) : {b : Set l} -> (y : b) -> Set where
  Refl : x == x

infix 4 _==_
