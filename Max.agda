module Max where
open import Prelude
import Relation.Binary
open Relation.Binary using (IsPreorder)
open import Data.Vec


module Inner (B : Set) (_<=B_ : B -> B -> Set) 
             (isPre : IsPreorder _≡_ _<=B_) where

  record Max (A : Set)  : Set where
    field
      max         : (f : A -> B) -> B
      argmax      : (f : A -> B) -> A

      maxSpec     : (f : A -> B) -> (a : A) -> (f a  <=B  max f)
      argmaxSpec  : (f : A -> B) -> f (argmax f) ≡ max f

    maxSpec'    : (f : A -> B) -> (a : A) -> (f a  <=B  f (argmax f)) -- derived operator
    maxSpec' f a = subst (\ z -> f a <=B z) (sym (argmaxSpec f)) (maxSpec f a)

  -- options: require decidability
  --     require max2 ?

  postulate max2 : {A : Set} -> (A × B)  -> (A × B)  -> (A × B)  
--  max2 ab1 ab2 = if ((snd a) <=B (snd b)) then b else a

  maxP : {A : Set} {n : Nat} -> Vec (A × B) (S n) -> (A × B)
  maxP = foldr₁ max2 
