module Context  where
open import Prelude

{-
In the case of a time-dependent set of states and of a deterministic
transition function, the context of a DP problem can be formalized in
terms of:
-}

record RewProp : Set1 where
  field
    carrier : Type
    0F    : carrier
    _+F_  : carrier -> carrier -> carrier

    _<=F_ : carrier -> carrier -> Set

    reflexive<=F : (x : carrier) -> x <=F x 
   

record Context (Rew : RewProp) : Set1 where
  open RewProp Rew
  field 
    X : Nat -> Type
    Y : (t : Nat) -> X t -> Type
    step :   (t : Nat) -> (x : X t) -> Y t x -> X (S t)
    reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> carrier

    reachable : {t : Nat} -> X t -> Set

  _isPredOf_ : {t : Nat} -> X t -> X (S t) -> Set
  _isPredOf_ {t} x x' = Σ (Y t x) (\y -> (x' ≡ step t x y))

  field 
    reachableSpec0 : {t : Nat} (x : X t) -> reachable x

    reachableSpec1 : {t : Nat} -> (x : X t) -> reachable x ->
                     (y : Y t x) -> reachable (step t x y)
   
    reachableSpec2 : {t : Nat} -> (x' : X (S t)) -> reachable x' -> 
                     Σ (X t) (\x -> (reachable x) × (x isPredOf x'))


    viable : {t : Nat} -> (n : Nat) -> X t -> Set

  -- TODO: Come up with a name indicating there is an "internal" y
  viableStep : {t : Nat} -> (n : Nat) -> X t -> Set
  viableStep {t} n x = Σ (Y t x) (\y -> viable n (step t x y))

  field                  

    viableSpec0 : {t : Nat} (x : X t) -> viable Z x

    viableSpec1 : {t : Nat} -> {n : Nat} -> 
                  (x : X t) -> viable (S n) x -> viableStep n x

    viableSpec2 : {t : Nat} -> {n : Nat} -> 
                  (x : X t) -> viableStep n x -> viable (S n) x

