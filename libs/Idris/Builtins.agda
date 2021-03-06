module Idris.Builtins where
import Agda.Builtin.Nat
open Agda.Builtin.Nat using (Nat)


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

-- This does not quite work with heterogenous equality: {-# BUILTIN EQUALITY _==_ #-}

infix 4 _==_

postulate
  Float  : Type
  Char   : Type
  String : Type

data Int : Set where
  pos    : Nat -> Int
  negsuc : Nat -> Int
{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}


-- Bind the built-in types using the BUILTIN pragma.
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}
{-# BUILTIN STRING  String #-}
