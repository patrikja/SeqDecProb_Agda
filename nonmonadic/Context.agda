module Context where
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

-- "RewType" (reward type) contain an abstraction of Float
record RewType : Set1 where
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

-- TODO: Rename ContextType to something better
record ContextType : Set1 where
  field
    X : Nat -> Type -- time-dependent state
    Y    : (t : Nat) -> X t -> Type -- time dependent, state-dependent control set
    step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)

  _isPredOf_ : {t : Nat} -> X t -> X (S t) -> Set
  _isPredOf_ {t} x x' = Σ (Y t x) (\y -> (x' ≡ step t x y))

record ReachableType (Context : ContextType) : Set1 where
  open ContextType Context
  field
    reachable : {t : Nat} -> X t -> Set

    reachableSpec0 : {t : Nat} (x : X t) -> reachable x

    reachableSpec1 : {t : Nat} -> (x : X t) -> reachable x ->
                     (y : Y t x) -> reachable (step t x y)

    reachableSpec2 : {t : Nat} -> (x' : X (S t)) -> reachable {S t} x' ->
                     Σ (X t) (\x -> (reachable {t} x) × (x isPredOf x'))

record ViableType (Context : ContextType) : Set1 where
  open ContextType Context

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

module Defaults (c : ContextType) where
  open ContextType c

  reachableDefault : {t : Nat} -> X t -> Set
  reachableDefault {Z}   _  = ⊤
  reachableDefault {S t} x' = Σ (X t) \ x ->
                                (reachableDefault {t} x) × (x isPredOf x')

  viableDefault : {t : Nat} -> (n : Nat) -> X t -> Set
  viableDefault {t} Z     x = ⊤
  viableDefault {t} (S n) x = Σ (X (S t)) \ x' ->
                                (x isPredOf x') × (viableDefault {S t} n x')

-- Pack it all up
-- TODO: Rename RewardType? FullContextType? ContextType?

record RewardType : Set1 where
  field
    Rew       : RewType
    Context   : ContextType
    Reachable : ReachableType Context
    Viable    : ViableType Context
  open RewType       Rew
  open ContextType   Context
  open ReachableType Reachable
  open ViableType    Viable

  field
    reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> carrier

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

  open RewType       Rew        public
  open ContextType   Context    public
  open ReachableType Reachable  public
  open ViableType    Viable     public

----------------------------------------------------------------
