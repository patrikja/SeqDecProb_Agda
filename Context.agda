module Context  where
open import Prelude
import Relation.Binary
open Relation.Binary using (IsPreorder)

module Variant where
  record Maxf (A B : Set) (_<=B_ : B -> B -> Set) 
              (isPre : IsPreorder _≡_ _<=B_) 
              (f : A -> B) : Set where
    field  -- "f is maximiseable"
      max         : B
      maxSpec     : (a : A) -> (f a  <=B  max)

      argmax      : A
      argmaxSpec  : f argmax ≡ max

    maxSpec'    : (a : A) -> (f a  <=B  f argmax)  -- derived operator
    maxSpec' a = subst (\ z -> f a <=B z) (sym argmaxSpec) (maxSpec a)

  Max : (A B : Set) (_<=B_ : B -> B -> Set) 
      (isPre : IsPreorder _≡_ _<=B_) -> Set
  Max A B _<=B_ isPre = ∀ (f : A -> B) ->  Maxf A B _<=B_ isPre f

record Max (A B : Set) (_<=B_ : B -> B -> Set) 
           (isPre : IsPreorder _≡_ _<=B_)  : Set where
  field
    max         : (f : A -> B) -> B
    argmax      : (f : A -> B) -> A
             
    maxSpec     : (f : A -> B) -> (a : A) -> (f a  <=B  max f)
    argmaxSpec  : (f : A -> B) -> f (argmax f) ≡ max f

  maxSpec'    : (f : A -> B) -> (a : A) -> (f a  <=B  f (argmax f)) -- derived operator
  maxSpec' f a = subst (\ z -> f a <=B z) (sym (argmaxSpec f)) (maxSpec f a)


-- Note that we don't necessarily need to require a fully general Max
-- record from a user. We could instead specialise it to some A and B
-- for a particular domain.
-- ParticularSpec = Max MyA MyB myorder ...
-- p : ParticularSpec

{-
In the case of a time-dependent set of states and of a deterministic
transition function, the context of a DP problem can be formalized in
terms of:
-}

-- "Rew" = Reward = an abstraction of Float
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

  _isPredOf_ : {t : Nat} -> X t -> X (S t) -> Set
  _isPredOf_ {t} x x' = Σ (Y t x) (\y -> (x' ≡ step t x y))

  field 
    reachable : {t : Nat} -> X t -> Set

    reachableSpec0 : {t : Nat} (x : X t) -> reachable x

    reachableSpec1 : {t : Nat} -> (x : X t) -> reachable x ->
                     (y : Y t x) -> reachable (step t x y)
   
    reachableSpec2 : {t : Nat} -> (x' : X (S t)) -> reachable {S t} x' -> 
                     Σ (X t) (\x -> (reachable {t} x) × (x isPredOf x'))

  field 
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
  argmax n x r v = Max.argmax (MaxVStep n x r v)

  maxSpec' : {t : Nat} -> (n : Nat) -> 
             (x : X t) ->
             (r : reachable x) -> 
             (v : viable (S n) x) ->
             (f : viableStep n x -> carrier) -> 
             (yv : viableStep n x) ->
             f yv <=F f (argmax n x r v f)
  maxSpec'  n x r v = Max.maxSpec' (MaxVStep n x r v)


-- TODO: move to better place
reachableDefault : (r : RewProp) (c : Context r) ->
  let open Context c 
  in  {t : Nat} -> X t -> Set
reachableDefault r c {Z}   _  = ⊤ 
reachableDefault r c {S t} x' = Σ (X t) \ x -> 
                                (reachableDefault r c {t} x) × (x isPredOf x')
  where open Context c

viableDefault : (r : RewProp) (c : Context r) -> 
  let open Context c 
  in  {t : Nat} -> (n : Nat) -> X t -> Set
viableDefault r c {t} Z     x = ⊤
viableDefault r c {t} (S n) x = Σ (X (S t)) \ x' -> 
                                  (x isPredOf x') × (viableDefault r c {S t} n x')
  where open Context c
