module Max where
open import Prelude
import Relation.Binary
open Relation.Binary using (IsPreorder; Decidable)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Vec
open import Data.Fin
open import Function

-- Some helper functions:
pairId : {A B : Set} -> (f : A -> B) -> (A -> (A × B))
pairId f a = (a , f a)

tabPair : {n : Nat} -> {B : Set} -> (f : Fin n -> B) -> Vec (Fin n × B) n
tabPair f = tabulate (pairId f)

module Inner (B : Set) (_<=B_ : B -> B -> Set) 
             (isPre : IsPreorder _≡_ _<=B_) where

  -- a specification of "maximisable" A and B
  record Max (A : Set)  : Set where
    field
      max         : (f : A -> B) -> B
      argmax      : (f : A -> B) -> A

      maxSpec     : (f : A -> B) -> (a : A) -> (f a  <=B  max f)
      argmaxSpec  : (f : A -> B) -> f (argmax f) ≡ max f

    maxSpec'    : (f : A -> B) -> (a : A) -> (f a  <=B  f (argmax f)) -- derived operator
    maxSpec' f a = subst (\ z -> f a <=B z) (sym (argmaxSpec f)) (maxSpec f a)


  -- Here comes one way of satisfying the specification:
  --   if A is (non-empty and) finite
  --   and the order on B is decidable
  module Decidable (n : Nat) (smaller : Decidable _<=B_) where
    A = Fin (S n)

    max2 : (A × B) -> (A × B) -> (A × B)  
    max2 ab1 ab2 with smaller (snd ab1) (snd ab2)
    ... | yes _  = ab2
    ... | no  _  = ab1

    maxVecPair : Vec (A × B) (S n) -> (A × B)
    maxVecPair = foldr₁ max2 

    maxPair : (f : Fin (S n) -> B) -> (A × B)
    maxPair = maxVecPair ∘ tabPair

    max    = snd ∘ maxPair
    maxarg = fst ∘ maxPair

--     mymaxSpec : (f : A → B) -> (a : A) -> f a <=B max f
--     mymaxSpec f a = {!!} -- TODO
{-
    myMax : Max A
    myMax = record { max = max; 
                     argmax = fst ∘ maxPair;
                     maxSpec = {!!}; 
                     argmaxSpec = {!!} 
                   }
-}    

  -- TODO: Perhaps change the Max spec to have a set A and a subset
  -- (or predicate) in which to search for the maximum). Easy
  -- conversion between vs : Vec A n and a set (type) of exactly those
  -- elements would be good to have. Assuming (A : Set) (allA : Vec A (S n))
  -- would still allow "junk" in A.
