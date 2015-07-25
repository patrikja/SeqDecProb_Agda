-- Simple probability distributions
module SimpleProb where
open import Function
open import Data.List as L
open import Data.List.Properties as LP
open import Data.Nat
open import Data.Bool
open import Data.Product as P
open import Data.Integer using (+_)
open import Data.Rational as Q
import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning
open PropEq using (_≡_; refl; sym; cong; cong₂)

{-

A finite list of pairs of weights and payloads.

Weights are often real numbers, summing to 1, but in a constructive
setting that is not convenient. It could be implemented with some
other fractional number type (like rationals) and the sum
requirement. Or it could simply be implemented with natural numbers as
weights and no requirement:

-}

SimpleProb : Set -> Set
SimpleProb a = List (ℕ × a)

{-

This may not be the most efficient implementation, but it is really simple.

-}

mapSP : {a b : Set} -> (a -> b) -> SimpleProb a -> SimpleProb b
mapSP f = L.map (\{ (n , a) → (n , f a) })

returnSP : {a : Set} -> a -> SimpleProb a
returnSP a = (1 , a) ∷ []

multAll : {a : Set} -> (ℕ × SimpleProb a) -> SimpleProb a
multAll (n , wxs) = L.map (P.map (_*_ n) (\x -> x)) wxs

joinSP : {a : Set} -> SimpleProb (SimpleProb a) -> SimpleProb a
joinSP = concatMap multAll

bindSP : {a b : Set} -> SimpleProb a -> (a -> SimpleProb b) -> SimpleProb b
bindSP spa f = joinSP (mapSP f spa)

{-

Note that with a completely polymorphic type |joinSP| and |mapSP|
cannot combine equal elements, so there may be duplicate weight
entries for the same payload.

The semantics (or "run-function") must take care of this and restrict
the type properly. For example by requesting an equality test (a -> a
-> Bool) or a "discriminator" (something that groups equal values from
a list into sublists).

-}

postulate
  _+Q_ : ℚ -> ℚ -> ℚ  -- Data.Rational in Agda does not define addition!
  mkQ  : ℕ -> ℕ -> ℚ

zeroQ : ℚ
zeroQ = + 0 ÷ 1

oneQ : ℚ
oneQ = + 1 ÷ 1

sumQ : List ℚ -> ℚ
sumQ = foldr _+Q_ zeroQ

sumOneFst : {a : Set} -> List (ℚ × a) -> Set
sumOneFst wxs =   sumQ (L.map proj₁ wxs) ≡ oneQ

module Lemmas where
  -- not needed after refactoring
  zipMap : {a b c : Set} -> (f : a -> b) -> (g : a -> c) -> (xs : List a) ->
    L.zip (L.map f xs) (L.map g xs) ≡ L.map (\x -> (f x , g x)) xs
  zipMap f g (x ∷ xs) = cong (_∷_ (f x , g x)) (zipMap f g xs)
  zipMap f g []       = refl

  mapMap : {a b c : Set} -> (g : b -> c) -> (f : a -> b) -> (xs : List a) ->
    L.map (g ∘ f) xs ≡ L.map g (L.map f xs)
  mapMap g f xs = LP.map-compose xs

  mapEq : {a b : Set} -> {f g : a -> b} -> (forall x -> f x ≡ g x) ->
    (xs : List a) -> L.map f xs ≡ L.map g xs
  mapEq  f~g []        = refl
  mapEq  f~g (x ∷ xs)  = cong₂ _∷_ (f~g x) (mapEq f~g xs)

  mapPair : {a1 b1 a2 b2 : Set} -> (f1 : a1 -> b1) -> (f2 : a2 -> b2) -> (xy : a1 × a2) ->
    proj₁ (P.map f1 f2 xy) ≡ f1 (proj₁ xy)
  mapPair f1 f2 (x , y) = refl

  sumDist : (f : ℕ -> ℚ) -> (zeroQ ≡ f 0) -> (forall x y -> f x +Q f y ≡ f (x + y) ) ->
    forall xs -> sumQ (L.map f xs) ≡ f (sum xs)
  sumDist f d0 dist [] = d0
  sumDist f d0 dist (x ∷ xs) =
    begin
      sumQ (f x ∷ L.map f xs)
    ≡⟨ refl ⟩
      f x +Q sumQ (L.map f xs)
    ≡⟨ cong (_+Q_ (f x)) (sumDist f d0 dist xs) ⟩
      f x +Q f (sum xs)
    ≡⟨ dist x (sum xs) ⟩
      f (x + sum xs)
    ≡⟨  refl ⟩
      f (sum (x ∷ xs))
    ∎

-- end module

postulate
  _/_ : ℕ -> ℕ -> ℚ  -- TODO: second number should not be zero
  divEq : forall n -> n / n ≡ oneQ
  -- TODO: perhaps change representation to force all weights to be positive (non-zero)
  --   (could just change the interpretation of the natural as "one less than the weight")

SimpleProbSem : Set -> Set
SimpleProbSem a = Σ (List (ℚ × a)) sumOneFst

-- TODO finish the semantics
runBy : {a : Set} -> (_==_ : a -> a -> Bool) -> SimpleProb a -> SimpleProbSem a
runBy {a} _==_ wxs = (L.map (P.map divBySum id) wxs , proof)
  where  weightsN : List ℕ
         weightsN = L.map proj₁ wxs
         sumN : ℕ
         sumN = sum weightsN
         divBySum : ℕ -> ℚ -- divide n by sumN to make a rational.
         divBySum n = n / sumN
         postulate
           divBySumSpec0 : zeroQ ≡ divBySum 0
           divBySumDist : (x y : ℕ) → divBySum x +Q divBySum y ≡ divBySum (x + y)
         newWeights : List (ℚ × a)
         newWeights = L.map (P.map divBySum id) wxs
         weightsQ : List ℚ
         weightsQ = L.map proj₁ newWeights
         proof : sumOneFst newWeights
         proof = begin
                   sumQ (L.map proj₁ (L.map (P.map divBySum id) wxs))
                 ≡⟨ cong sumQ (sym (Lemmas.mapMap proj₁ (P.map divBySum id) wxs)) ⟩
                   sumQ (L.map (proj₁ ∘ P.map divBySum id) wxs)
                 ≡⟨ cong sumQ (Lemmas.mapEq (Lemmas.mapPair divBySum id) wxs) ⟩
                   sumQ (L.map (divBySum ∘ proj₁) wxs)
                 ≡⟨ cong sumQ (Lemmas.mapMap divBySum proj₁ wxs) ⟩
                   sumQ (L.map divBySum weightsN)
                 ≡⟨ Lemmas.sumDist divBySum divBySumSpec0 divBySumDist weightsN ⟩
                   divBySum sumN
                 ≡⟨ divEq sumN ⟩
                   oneQ
                 ∎
