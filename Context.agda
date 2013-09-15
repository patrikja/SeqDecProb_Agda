module Context  where
open import Prelude
import Relation.Binary
open Relation.Binary using (IsPreorder)

record Max (A B : Set) (_<=B_ : B -> B -> Set) 
           (isPre : IsPreorder _≡_ _<=B_) : Set where
  
  field
    max     : (f : A -> B) -> B
    argmax  : (f : A -> B) -> A
             
    maxSpec     : (f : A -> B) -> (a : A) -> (f a  <=B  max f)
    argmaxSpec  : (f : A -> B) -> f (argmax f) ≡ max f

{-
In the case of a time-dependent set of states and of a deterministic
transition function, the context of a DP problem can be formalized in
terms of:
-}

record RewProp : Set1 where
  field
    carrier : Type  -- was Float
    0F    : carrier
    _+F_  : carrier -> carrier -> carrier

    _<=F_ : carrier -> carrier -> Set
    isPre : IsPreorder _≡_ _<=F_

    monoF  : {a b c : carrier} -> (b <=F c) -> (a +F b) <=F (a +F c)

  reflexive<=F : (x : carrier) -> x <=F x 
  reflexive<=F x = IsPreorder.reflexive isPre refl

  Preorder = record {Carrier = carrier; _≈_ = _≡_; _∼_ = _<=F_; isPreorder = isPre}

  -- We will use the Max specification for different A but for the
  -- same carrier so we introduce a convenient name for that.

  MaxF : Set -> Set
  MaxF A = Max A carrier _<=F_ isPre

record Context (Rew : RewProp) : Set1 where
  open RewProp Rew
  field 
    X : Nat -> Type -- time-dependent state
    Y : (t : Nat) -> X t -> Type -- time dependent, state-dependent control set
    step :   (t : Nat) -> (x : X t) -> Y t x -> X (S t)
    reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> carrier

    reachable : {t : Nat} -> X t -> Set

  _isPredOf_ : {t : Nat} -> X t -> X (S t) -> Set
  _isPredOf_ {t} x x' = Σ (Y t x) (\y -> (x' ≡ step t x y))

  field 
    reachableSpec0 : {t : Nat} (x : X t) -> reachable x

    reachableSpec1 : {t : Nat} -> (x : X t) -> reachable x ->
                     (y : Y t x) -> reachable (step t x y)
   
    reachableSpec2 : {t : Nat} -> (x' : X (S t)) -> reachable {S t} x' -> 
                     Σ (X t) (\x -> (reachable {t} x) × (x isPredOf x'))


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

{-
  field 
    MaxVStep : {t : Nat} ->  (n : Nat) -> 
               (x : X t) -> 
               (r : reachable x) -> 
               (v : viable (S n) x) ->
               MaxF (viableStep n x)
    
  argmax : {t : Nat} -> (n : Nat) ->
           (x : X t) -> 
           (r : reachable x) -> 
           (v : viable (S n) x) ->
           (f : viableStep n x -> carrier) -> 
           viableStep n x
  argmax = {!!} -- Max.argmax ?
  TODO: use the "generic" Max specification instead of the argmax fields
  -}

  field
    argmax : {t : Nat} -> (n : Nat) ->
             (x : X t) -> 
             (r : reachable x) -> 
             (v : viable (S n) x) ->
             (f : viableStep n x -> carrier) -> 
             viableStep n x



{-


TODO:
> max : (n : Nat) ->
>       (x : X t) -> 
>       (r : so (reachable x)) -> 
>       (v : so (viable (S n) x)) ->
>       (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>       Float

> maxSpec : (n : Nat) -> 
>           (x : X t) ->
>           (r : so (reachable x)) -> 
>           (v : so (viable (S n) x)) ->
>           (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>           (yv : (y : Y t x ** so (viable {t = S t} n (step t x y)))) ->
>           so (f yv <= max n x r v f)

> argmaxSpec : (n : Nat) -> 
>              (x : X t) ->
>              (r : so (reachable x)) -> 
>              (v : so (viable (S n) x)) ->
>              (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>              so (f (argmax n x r v f) == max n x r v f)
-}




