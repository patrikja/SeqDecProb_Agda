module Builtins where
Type = Set
Lazy : Type -> Type
Lazy A = A
Force : {A : Type} -> A -> A
Force x = x
data Void : Set where
void : {a : Type} -> Void -> a
void ()
data _×_ (a : Set) (b : Set) : Set where
  _,_ : a -> b -> a × b
