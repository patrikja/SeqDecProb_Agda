-- Simple probability distributions
module SimpleProb where
open import Data.List as L
open import Data.Nat
open import Data.Bool
open import Data.Product as P
open import Data.Integer using (+_)
open import Data.Rational as Q
open import Relation.Binary.PropositionalEquality using (_≡_)

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
returnSP a = [(1 , a)]

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
the type properly.

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

SimpleProbSem : Set -> Set
SimpleProbSem a = Σ (List (ℚ × a)) sumOneFst

-- TODO finish the semantics
runBy : {a : Set} -> (_==_ : a -> a -> Bool) -> SimpleProb a -> SimpleProbSem a
runBy {a} _==_ wxs = (L.zip weightsQ payload , {!!})
  where  payload : List a
         payload = L.map proj₂ wxs
         weightsN : List ℕ
         weightsN = L.map proj₁ wxs
         sumN : ℕ
         sumN = sum weightsN
         divBySum : ℕ -> ℚ
         divBySum n = {!!} -- divide n by sumN to make a rational.
         weightsQ : List ℚ
         weightsQ = L.map divBySum weightsN
