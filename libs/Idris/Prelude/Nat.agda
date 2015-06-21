module Idris.Prelude.Nat where

open import Idris.Builtins

-- import Idris.Prelude.Algebra
open import Idris.Prelude.Basics
open import Idris.Prelude.Bool
-- import Idris.Prelude.Cast
import Idris.Prelude.Classes
open   Idris.Prelude.Classes using (EqDict)
-- import Idris.Prelude.Uninhabited
open import Idris.Syntax.PreorderReasoning

-- %access public
-- %default total

-- ||| Unary natural numbers
data Nat : Type where
  -- ||| Zero
  Z : Nat
  -- ||| Successor
  S : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}


-- name hints for interactive editing
-- %name Nat k,j,i,n,m

{- TODOinst
instance Uninhabited (Z = S n) where
  uninhabited Refl impossible
-}

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isZero : Nat -> Bool
isZero Z     = True
isZero (S n) = False

isSucc : Nat -> Bool
isSucc Z     = False
isSucc (S n) = True

--------------------------------------------------------------------------------
-- Basic arithmetic functions
--------------------------------------------------------------------------------

-- ||| Add two natural numbers.
-- ||| @ n the number to case-split on
-- ||| @ m the other number
plus : (n, m : Nat) -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)

-- ||| Multiply natural numbers
mult : Nat -> Nat -> Nat
mult Z right        = Z
mult (S left) right = plus right (mult left right)

{- TODO Integer
-- ||| Convert an Integer to a Nat, mapping negative numbers to 0
fromIntegerNat : Integer -> Nat
fromIntegerNat 0 = Z
fromIntegerNat n =
  if (n > 0) then
    S (fromIntegerNat (assert_smaller n (n - 1)))
  else
    Z

-- ||| Convert a Nat to an Integer
toIntegerNat : Nat -> Integer
toIntegerNat Z = 0
toIntegerNat (S k) = 1 + toIntegerNat k
-}

-- ||| Subtract natural numbers. If the second number is larger than the first, return 0.
minus : Nat -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

-- ||| Exponentiation of natural numbers
power : Nat -> Nat -> Nat
power base Z       = S Z
power base (S exp) = mult base (power base exp)

hyper : Nat -> Nat -> Nat -> Nat
hyper Z        a b      = S b
hyper (S Z)    a Z      = a
hyper (S(S Z)) a Z      = Z
hyper n        a Z      = S Z
hyper (S pn)   a (S pb) = hyper pn a (hyper (S pn) a pb)


--------------------------------------------------------------------------------
-- Comparisons
--------------------------------------------------------------------------------

-- ||| Proofs that `n` is less than or equal to `m`
-- ||| @ n the smaller number
-- ||| @ m the larger number
data LTE : (n m : Nat) -> Type where
  -- ||| Zero is the smallest Nat
  LTEZero : {right : Nat} -> LTE Z    right
  -- ||| If n <= m, then n + 1 <= m + 1
  LTESucc : {left : Nat} -> {right : Nat} -> LTE left right -> LTE (S left) (S right)

-- ||| Greater than or equal to
GTE : Nat -> Nat -> Type
GTE left right = LTE right left

-- ||| Strict less than
LT : Nat -> Nat -> Type
LT left right = LTE (S left) right

-- ||| Strict greater than
GT : Nat -> Nat -> Type
GT left right = LT right left

-- ||| A successor is never less than or equal zero
succNotLTEzero : {m : Nat} -> Not (LTE (S m) Z)
succNotLTEzero ()

-- ||| If two numbers are ordered, their predecessors are too
fromLteSucc : {m : Nat} -> {n : Nat} -> (LTE (S m) (S n)) -> (LTE m n)
fromLteSucc (LTESucc x) = x

-- ||| A decision procedure for `LTE`
isLTE : (m n : Nat) -> Dec (LTE m n)
isLTE Z n = Yes LTEZero
isLTE (S k) Z = No succNotLTEzero
isLTE (S k) (S j) with (isLTE k j)
isLTE (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
isLTE (S k) (S j) | (No contra) = No (contra ∘ fromLteSucc)

-- ||| `LTE` is reflexive.
lteRefl : {n : Nat} -> LTE n n
lteRefl {n = Z}   = LTEZero
lteRefl {n = S k} = LTESucc lteRefl

-- ||| n < m implies n < m + 1
lteSuccRight : {n m : Nat} -> LTE n m -> LTE n (S m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)

-- ||| Boolean test than one Nat is less than or equal to another
lte : Nat -> Nat -> Bool
lte Z        right     = True
lte left     Z         = False
lte (S left) (S right) = lte left right

-- ||| Boolean test than one Nat is greater than or equal to another
gte : Nat -> Nat -> Bool
gte left right = lte right left

-- ||| Boolean test than one Nat is strictly less than another
lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

-- ||| Boolean test than one Nat is strictly greater than another
gt : Nat -> Nat -> Bool
gt left right = lt right left

-- ||| Find the least of two natural numbers
minimum : Nat -> Nat -> Nat
minimum Z m = Z
minimum (S n) Z = Z
minimum (S n) (S m) = S (minimum n m)

-- ||| Find the greatest of two natural numbers
maximum : Nat -> Nat -> Nat
maximum Z m = m
maximum (S n) Z = S n
maximum (S n) (S m) = S (maximum n m)

{- TODO Int
-- ||| Tail recursive cast Nat to Int
-- ||| Note that this can overflow
toIntNat : Nat -> Int
toIntNat n = toIntNat' n 0 where
        toIntNat' : Nat -> Int -> Int
        toIntNat' Z     x = x
        toIntNat' (S n) x = toIntNat' n (x + 1)
-}
--------------------------------------------------------------------------------
-- Type class instances
--------------------------------------------------------------------------------
eqNat = record { _===_ = _===_} where
  _===_ : Nat -> Nat -> Bool
  Z === Z         = True
  (S l) === (S r) = l === r
  _ === _         = False


{- TODOinst
instance Eq Nat where
  Z == Z         = True
  (S l) == (S r) = l == r
  _ == _         = False

instance Cast Nat Integer where
  cast = toIntegerNat

instance Ord Nat where
  compare Z Z         = EQ
  compare Z (S k)     = LT
  compare (S k) Z     = GT
  compare (S x) (S y) = compare x y
-}

infixl 8 _+_ _-_
infixl 9 _*_

_+_ = plus
_-_ = minus
_*_ = mult

{-
instance Num Nat where
  (+) = plus
  (-) = minus
  (*) = mult

  abs x = x

  fromInteger = fromIntegerNat
-}
{-
instance MinBound Nat where
  minBound = Z

instance Cast Integer Nat where
  cast = fromInteger
-}

-- ||| A wrapper for Nat that specifies the semigroup and monad instances that use (+)
record Multiplicative : Type where
  field
    getMultiplicative : Nat

-- ||| A wrapper for Nat that specifies the semigroup and monad instances that use (*)
record Additive : Type where
  field
    getAdditive : Nat
{-
instance Semigroup Multiplicative where
  (<+>) left right = getMultiplicative $ left' * right'
    where
      left'  : Nat
      left'  =
       case left of
          getMultiplicative m => m

      right' : Nat
      right' =
        case right of
          getMultiplicative m => m

instance Semigroup Additive where
  left <+> right = getAdditive $ left' + right'
    where
      left'  : Nat
      left'  =
        case left of
          getAdditive m => m

      right' : Nat
      right' =
        case right of
          getAdditive m => m

instance Monoid Multiplicative where
  neutral = getMultiplicative $ S Z

instance Monoid Additive where
  neutral = getAdditive Z

instance MeetSemilattice Nat where
  meet = minimum

instance JoinSemilattice Nat where
  join = maximum

instance Lattice Nat where { }

instance BoundedJoinSemilattice Nat where
  bottom = Z


instance Cast Int Nat where
  cast i = fromInteger (cast i)

instance Cast Nat Int where
  cast = toIntNat
-}

--------------------------------------------------------------------------------
-- Auxilliary notions
--------------------------------------------------------------------------------

-- ||| The predecessor of a natural number. `pred Z` is `Z`.
pred : Nat -> Nat
pred Z     = Z
pred (S n) = n

--------------------------------------------------------------------------------
-- Fibonacci and factorial
--------------------------------------------------------------------------------

-- ||| Fibonacci numbers
fib : Nat -> Nat
fib Z         = Z
fib (S Z)     = S Z
fib (S (S n)) = fib (S n) + fib n

-- ||| Factorial function
fact : Nat -> Nat
fact Z     = S Z
fact (S n) = (S n) * fact n

--------------------------------------------------------------------------------
-- Division and modulus
--------------------------------------------------------------------------------

modNat : Nat -> Nat -> Nat
modNat left Z         = left
modNat left (S right) = mod' left left right
  where
    mod' : Nat -> Nat -> Nat -> Nat
    mod' Z        centre right = centre
    mod' (S left) centre right =
      if lte centre right then
        centre
      else
        mod' left (centre - (S right)) right

divNat : Nat -> Nat -> Nat
divNat left Z         = S left               -- div by zero
divNat left (S right) = div' left left right
  where
    div' : Nat -> Nat -> Nat -> Nat
    div' Z        centre right = Z
    div' (S left) centre right =
      if lte centre right then
        Z
      else
        S (div' left (centre - (S right)) right)
{-
instance Integral Nat where
-}
div = divNat
mod = modNat

{- TODOterm convince the termination checker
log2 : Nat -> Nat
log2 Z = Z
log2 (S Z) = Z
log2 n = S (log2 (divNat n 2))
-}

--------------------------------------------------------------------------------
-- GCD and LCM
--------------------------------------------------------------------------------
{- TODOterm convince the termination checker
gcd : Nat -> Nat -> Nat
gcd a Z = a
gcd a b = gcd b (modNat a b)

lcm : Nat -> Nat -> Nat
lcm _ Z = Z
lcm Z _ = Z
lcm x y = divNat (x * y) (gcd x y)
-}


--------------------------------------------------------------------------------
-- An informative comparison view
--------------------------------------------------------------------------------
data CmpNat : Nat -> Nat -> Type where
     CmpLT : {x : Nat} -> (y : _) -> CmpNat x (x + S y)
     CmpEQ : {x : Nat} -> CmpNat x x
     CmpGT : {y : Nat} -> (x : _) -> CmpNat (y + S x) y


cmp : (x y : Nat) -> CmpNat x y
cmp Z Z     = CmpEQ
cmp Z (S k) = CmpLT _
cmp (S k) Z = CmpGT _
cmp (S x) (S y) with (cmp x y)
cmp (S x) (S .(plus x (S y))) | CmpLT y = CmpLT y
cmp (S x) (S .x)              | CmpEQ   = CmpEQ
cmp (S .(plus y (S x))) (S y) | CmpGT x = CmpGT x


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Succ

-- ||| S preserves equality
eqSucc : (left : Nat) -> (right : Nat) -> (p : left == right) ->
  S left == S right
eqSucc left .left Refl = Refl

-- ||| S is injective
succInjective : (left : Nat) -> (right : Nat) -> (p : S left == S right) ->
  left == right
succInjective left .left Refl = Refl

decEqNat : (m n : Nat) -> Dec (m == n)
decEqNat Z     Z     = Yes Refl
decEqNat Z     (S n) = No (λ ())
decEqNat (S m) Z     = No (λ ())
decEqNat (S m) (S n) with decEqNat m n
decEqNat (S m) (S .m) | Yes Refl  = Yes Refl
...                   | No contra = No (contra ∘ succInjective m n)

-- Plus
plusZeroLeftNeutral : (right : Nat) -> (0 + right) == right
plusZeroLeftNeutral right = Refl

plusZeroRightNeutral : (left : Nat) -> (left + 0) == left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) =
  let inductiveHypothesis = plusZeroRightNeutral n in
    cong S inductiveHypothesis -- ?plusZeroRightNeutralStepCase

plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) == (left + S right)
plusSuccRightSucc Z right        = Refl
plusSuccRightSucc (S left) right =
  let inductiveHypothesis = plusSuccRightSucc left right in
    cong S inductiveHypothesis


plusCommutative : (left : Nat) -> (right : Nat) ->
  (left + right) == (right + left)
plusCommutative Z        Z         = Refl
plusCommutative Z        (S right) = trans (     plusZeroLeftNeutral  (S right))
                                           (sym (plusZeroRightNeutral (S right)))
plusCommutative (S left) Z         = plusZeroRightNeutral (S left)
plusCommutative (S left) (S right) = cong S
                                       (left + S right    ==< plusCommutative left (S right) >==
                                        S (right + left)  ==< plusSuccRightSucc right left   >==
                                        right + S left    QED)


plusAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + (centre + right)) == ((left + centre) + right)
plusAssociative Z        centre right = Refl
plusAssociative (S left) centre right = cong S inductiveHypothesis
  where inductiveHypothesis = plusAssociative left centre right


plusConstantRight : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left == right) -> (left + c) == (right + c)
plusConstantRight left .left c Refl = Refl

plusConstantLeft : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left == right) -> (c + left) == (c + right)
plusConstantLeft left .left c Refl = Refl


plusOneSucc : (right : Nat) -> (1 + right) == S right
plusOneSucc n = Refl

plusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (p : (left + right) == (left + right'))  ->  (right == right')
plusLeftCancel Z        right right' p = p
plusLeftCancel (S left) right right' p = plusLeftCancel left right right'
                                           (succInjective (left + right) (left + right') p)

plusRightCancel : (left : Nat) -> (left' : Nat) -> (right : Nat) ->
  (p : (left + right) == (left' + right))  ->  (left == left')
plusRightCancel left left' right p = plusLeftCancel right left left'
                                       (  right + left   ==< plusCommutative right left >==
                                          left  + right  ==< p >==
                                          left' + right  ==< plusCommutative left' right >==
                                          right + left'  QED
                                       )

plusLeftLeftRightZero : (left : Nat) -> (right : Nat) ->
  (p : (left + right) == left)  ->  (right == Z)
plusLeftLeftRightZero Z        right p = p
plusLeftLeftRightZero (S left) right p =
  let inductiveHypothesis = plusLeftLeftRightZero left right in
    inductiveHypothesis (succInjective (plus left right) left p)

-- Mult
multZeroLeftZero : (right : Nat) -> (Z * right) == Z
multZeroLeftZero right = Refl

multZeroRightZero : (left : Nat) -> (left * Z) == Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) =
  let inductiveHypothesis = multZeroRightZero left in
     inductiveHypothesis

multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  (left * (S right)) == (left + (left * right))
multRightSuccPlus Z        right = Refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
     (S left * S right)                ==< Refl >==
     (S right) + (left * S right)      ==< cong ((_+_) (S right)) inductiveHypothesis >==
     (S right) + (left + left * right) ==< Refl >==
     S (right + (left + left * right)) ==< cong S (plusAssociative right left (left * right)) >==
     S ((right + left) + left * right) ==< cong (\x -> S (x + left * right)) (plusCommutative right left) >==
     S ((left + right) + left * right) ==< cong S (sym (plusAssociative left right (left * right))) >==
     S (left + (right + left * right)) ==< Refl >==
     S (left + (S left * right))       ==< Refl >==
     (S left + S left * right)         QED

multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  (S left * right) == (right + (left * right))
multLeftSuccPlus left right = Refl

multCommutative : (left : Nat) -> (right : Nat) ->
  (left * right) == (right * left)
multCommutative Z right        = sym (multZeroRightZero right)
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
    (S left * right)           ==< Refl >==
    (right + left * right)     ==< cong (_+_ right) inductiveHypothesis >==
    (right + right * left)     ==< sym (multRightSuccPlus right left) >==
    (right * S left)           QED

swapMid : (a b c d : Nat) -> ( (a + b) + (c + d) ) == ( (a + c) + (b + d) )
swapMid a b c d =  ((a + b) + (c + d))   ==< sym (plusAssociative a b _) >==
                   (a + (b + (c + d)))   ==< cong (_+_ a) (plusAssociative b c d) >==
                   (a + ((b + c) + d))   ==< cong (\x -> a + (x + d)) (plusCommutative b c) >==
                   (a + ((c + b) + d))   ==< cong (_+_ a) (sym (plusAssociative c b d)) >==
                   (a + (c + (b + d)))   ==< plusAssociative a c _ >==
                   ((a + c) + (b + d))   QED

multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left * (centre + right)) == ((left * centre) + (left * right))
multDistributesOverPlusRight Z        centre right = Refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
     (S left * (centre + right))                  ==< Refl >==
     ((centre + right) + left * (centre + right)) ==< cong (_+_ (centre + right)) inductiveHypothesis >==
     ((centre + right) + (left * centre + left * right)) ==< swapMid centre right _ _ >==
     ((centre + left * centre) + (right + left * right)) ==< Refl >==
     (S left * centre + S left * right) QED


multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + centre) * right  ==  (left * right) + (centre * right)
multDistributesOverPlusLeft Z        centre right = Refl
multDistributesOverPlusLeft (S left) centre right =
  let indHyp = multDistributesOverPlusLeft left centre right in
     (S left + centre) * right            ==< Refl >==
     S (left + centre) * right            ==< Refl >==
     right + (left + centre) * right      ==< cong (_+_ right) indHyp >==
     right + ((left * right) + (centre * right)) ==< plusAssociative right _ _ >==
     (right + (left * right)) + (centre * right) ==< Refl >==
     S left * right + centre * right      QED

multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre * right) == (left * centre) * right
multAssociative Z        centre right = Refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
     S left * (centre * right)                   ==< Refl >==
     centre * right +  left * (centre * right)   ==< cong (_+_ (centre * right)) inductiveHypothesis >==
     centre * right +  (left * centre) * right   ==< sym (multDistributesOverPlusLeft centre (mult left centre) right) >==
     (centre + left * centre) * right            ==< Refl >==
     (S left * centre) * right   QED

multOneLeftNeutral : (right : Nat) -> 1 * right == right
multOneLeftNeutral right =
    1 * right             ==< Refl >==
    right + Z * right     ==< Refl >==
    right + Z             ==< plusZeroRightNeutral (right) >==
    right                 QED
-- Simpler than the Idris lib version (no need to match on right)

multOneRightNeutral : (left : Nat) -> left * 1 == left
multOneRightNeutral left =
  left * 1  ==< multCommutative left 1 >==
  1 * left  ==< multOneLeftNeutral left >==
  left      QED


-- Minus
minusSuccSucc : (left : Nat) -> (right : Nat) ->
  (S left) - (S right) == left - right
minusSuccSucc left right = Refl

minusZeroLeft : (right : Nat) -> 0 - right == Z
minusZeroLeft right = Refl

minusZeroRight : (left : Nat) -> left - 0 == left
minusZeroRight Z        = Refl
minusZeroRight (S left) = Refl

minusZeroN : (n : Nat) -> Z == n - n
minusZeroN Z     = Refl
minusZeroN (S n) = minusZeroN n

minusOneSuccN : (n : Nat) -> S Z == (S n) - n
minusOneSuccN Z     = Refl
minusOneSuccN (S n) = minusOneSuccN n

minusSuccOne : (n : Nat) -> S n - 1 == n
minusSuccOne Z     = Refl
minusSuccOne (S n) = Refl

minusPlusZero : (n : Nat) -> (m : Nat) -> n - (n + m) == Z
minusPlusZero Z     m = Refl
minusPlusZero (S n) m = minusPlusZero n m

minusMinusMinusPlus : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left - centre) - right == left - (centre + right)
minusMinusMinusPlus Z        Z          right = Refl
minusMinusMinusPlus (S left) Z          right = Refl
minusMinusMinusPlus Z        (S centre) right = Refl
minusMinusMinusPlus (S left) (S centre) right = minusMinusMinusPlus left centre right
{- -- Unnecessary, but clarifying:
  let inductiveHypothesis = minusMinusMinusPlus left centre right in
     (S left - S centre) - right    ==< Refl >==
     (left - centre) - right        ==< inductiveHypothesis >==
     left - (centre + right)        ==< Refl >==
     S left - S (centre + right)    ==< Refl >==
     S left - (S centre + right)    QED
-}

plusMinusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (left + right) - (left + right') == right - right'
plusMinusLeftCancel Z right right'        = Refl
plusMinusLeftCancel (S left) right right' = plusMinusLeftCancel left right right'

multDistributesOverMinusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left - centre) * right == (left * right) - (centre * right)
multDistributesOverMinusLeft Z        Z          right = Refl
multDistributesOverMinusLeft (S left) Z          right =
   (S left - Z) * right         ==< Refl >==
   S left * right               ==< sym (minusZeroRight _) >==
   S left * right  -  Z         ==< Refl >==
   S left * right  -  Z * right  QED
multDistributesOverMinusLeft Z        (S centre) right = Refl
multDistributesOverMinusLeft (S left) (S centre) right =
  let inductiveHypothesis = multDistributesOverMinusLeft left centre right in
     (S left - S centre) * right          ==< Refl >==
     (left - centre) * right              ==< inductiveHypothesis >==
     left * right - centre * right        ==< sym (plusMinusLeftCancel right _ _) >==
     (right + left * right) - (right + centre * right)==< Refl >==
     S left * right - S centre * right    QED

multDistributesOverMinusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre - right) == (left * centre) - (left * right)
multDistributesOverMinusRight left centre right =
   left * (centre - right)        ==< multCommutative left _ >==
   (centre - right) * left        ==< multDistributesOverMinusLeft centre right left >==
   centre * left - right * left   ==< cong2 _-_ (multCommutative centre left) (multCommutative right left) >==
   left * centre - left * right   QED


-- Power
powerSuccPowerLeft : (base : Nat) -> (exp : Nat) ->
  power base (S exp) == base * (power base exp)
powerSuccPowerLeft base exp = Refl

multPowerPowerPlus : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  (power base exp) * (power base exp') == power base (exp + exp')
multPowerPowerPlus base Z       exp' = multOneLeftNeutral (power base exp')
multPowerPowerPlus base (S exp) exp' =
  let inductiveHypothesis = multPowerPowerPlus base exp exp' in
     (base * power base exp) * power base exp' ==< sym (multAssociative base _ _) >==
     base * (power base exp * power base exp') ==< cong (_*_ base) inductiveHypothesis >==
     (base * power base (plus exp exp'))  QED

powerZeroOne : (base : Nat) ->     power base 0 == 1
powerZeroOne base = Refl

powerOneNeutral : (base : Nat) ->  power base 1 == base
powerOneNeutral Z        = Refl
powerOneNeutral (S base) = cong S (powerOneNeutral base)

powerOneSuccOne : (exp : Nat) ->   power 1 exp == 1
powerOneSuccOne Z       = Refl
powerOneSuccOne (S exp) =
  let inductiveHypothesis = powerOneSuccOne exp in
     power 1 exp  +  0 ==< plusZeroRightNeutral _ >==
     power 1 exp       ==< inductiveHypothesis    >==
     1  QED

powerSuccSuccMult : (base : Nat) -> power base 2 == base * base
powerSuccSuccMult base = power base 2 ==< Refl >==
                         base * power base 1 ==< Refl >==
                         base * (base * power base 0) ==< Refl >==
                         base * (base * 1) ==< cong (_*_ base) (multOneRightNeutral base) >==
                         base * base  QED
-- Unneccessary case in Idris

powerPowerMultPower : (base : Nat) -> (exp : Nat) -> (exp' : Nat) ->
  power (power base exp) exp' == power base (exp * exp')
powerPowerMultPower base exp Z         =
  power (power base exp) 0  ==< Refl >==
  1                     ==< Refl >==
  power base 0          ==< cong (power base) (sym (multZeroRightZero exp)) >==
  power base (exp * 0)  QED

powerPowerMultPower base exp (S exp')  =
  let inductiveHypothesis = powerPowerMultPower base exp exp' in
     power base exp  *   power (power base exp) exp'  ==< cong (_*_ (power base exp)) inductiveHypothesis >==
     power base exp  *   power base (exp * exp')      ==< multPowerPowerPlus base exp _ >==
     power base (exp + exp * exp')                    ==< cong (power base) (sym (multRightSuccPlus exp exp')) >==
     power base (exp * S exp')    QED

-- Pred
predSucc : (n : Nat) -> pred (S n) == n
predSucc n = Refl

minusSuccPred : (left : Nat) -> (right : Nat) ->
  left - (S right) == pred (left - right)
minusSuccPred Z        right = Refl
minusSuccPred (S left) Z =
     S left - (S Z)     ==< Refl >==
     left - Z           ==< minusZeroRight left >==
     left               ==< Refl >==
     pred (S left)      ==< Refl >==
     pred (S left - Z)   QED
minusSuccPred (S left) (S right) =
  let inductiveHypothesis = minusSuccPred left right in
     S left - S (S right)     ==< Refl >==
     left   - S right         ==< inductiveHypothesis >==
     pred (left - right)      ==< Refl >==
     pred (S left - S right)  QED

-- boolElim
boolElimFun : {A B : Type} -> (fun : A -> B) -> (cond : Bool) -> (t : A) -> (f : A) ->
  fun (boolElim cond t f) == boolElim cond (fun t) (fun f)
boolElimFun fun True  t f = Refl
boolElimFun fun False t f = Refl

boolElimSuccSucc : (cond : Bool) -> (t : Nat) -> (f : Nat) ->
  S (boolElim cond t f) == boolElim cond (S t) (S f)
boolElimSuccSucc = boolElimFun S

boolElimPlusPlusLeft : (cond : Bool) -> (left : Nat) -> (t : Nat) -> (f : Nat) ->
  left + (boolElim cond t f) == boolElim cond (left + t) (left + f)
boolElimPlusPlusLeft cond left = boolElimFun (_+_ left) cond

boolElimPlusPlusRight : (cond : Bool) -> (right : Nat) -> (t : Nat) -> (f : Nat) ->
  (boolElim cond t f) + right == boolElim cond (t + right) (f + right)
boolElimPlusPlusRight cond right = boolElimFun (λ z → z + right) cond


boolElimMultMultLeft : (cond : Bool) -> (left : Nat) -> (t : Nat) -> (f : Nat) ->
  left * (boolElim cond t f) == boolElim cond (left * t) (left * f)
boolElimMultMultLeft cond left = boolElimFun (_*_ left) cond


boolElimMultMultRight : (cond : Bool) -> (right : Nat) -> (t : Nat) -> (f : Nat) ->
  (boolElim cond t f) * right == boolElim cond (t * right) (f * right)
boolElimMultMultRight cond right = boolElimFun (λ z → z * right) cond


-- Orders
lteNTrue : (n : Nat) -> lte n n == True
lteNTrue Z     = Refl
lteNTrue (S n) = lteNTrue n

LTESuccZeroFalse : (n : Nat) -> lte (S n) Z == False
LTESuccZeroFalse Z     = Refl
LTESuccZeroFalse (S n) = Refl

-- Minimum and maximum
maximumAssociative : (l c r : Nat) -> maximum l (maximum c r) == maximum (maximum l c) r
maximumAssociative Z c r = Refl
maximumAssociative (S k) Z r = Refl
maximumAssociative (S k) (S j) Z = Refl
maximumAssociative (S k) (S j) (S i) = eqSucc _ _ (maximumAssociative k j i)

maximumCommutative : (l r : Nat) -> maximum l r == maximum r l
maximumCommutative Z Z = Refl
maximumCommutative Z (S k) = Refl
maximumCommutative (S k) Z = Refl
maximumCommutative (S k) (S j) =  eqSucc _ _ (maximumCommutative k j)

maximumIdempotent : (n : Nat) -> maximum n n == n
maximumIdempotent Z = Refl
maximumIdempotent (S k) = cong S (maximumIdempotent k)

minimumAssociative : (l c r : Nat) -> minimum l (minimum c r) == minimum (minimum l c) r
minimumAssociative Z c r = Refl
minimumAssociative (S k) Z r = Refl
minimumAssociative (S k) (S j) Z = Refl
minimumAssociative (S k) (S j) (S i) =  eqSucc _ _ (minimumAssociative k j i)

minimumCommutative : (l r : Nat) -> minimum l r == minimum r l
minimumCommutative Z Z = Refl
minimumCommutative Z (S k) = Refl
minimumCommutative (S k) Z = Refl
minimumCommutative (S k) (S j) =  eqSucc _ _ (minimumCommutative k j)

minimumIdempotent : (n : Nat) -> minimum n n == n
minimumIdempotent Z = Refl
minimumIdempotent (S k) = cong S (minimumIdempotent k)


minimumZeroZeroRight : (right : Nat) -> minimum 0 right == 0
minimumZeroZeroRight x = Refl
-- Idris uses unnecessary case

minimumZeroZeroLeft : (left : Nat) -> minimum left 0 == 0
minimumZeroZeroLeft Z        = Refl
minimumZeroZeroLeft (S left) = Refl

minimumSuccSucc : (left : Nat) -> (right : Nat) ->
  minimum (S left) (S right) == S (minimum left right)
minimumSuccSucc x y = Refl
-- Idris uses unnecessary case on both x and y

maximumZeroNRight : (right : Nat) -> maximum 0 right == right
maximumZeroNRight x         = Refl
-- Idris uses unnecessary case

maximumZeroNLeft : (left : Nat) -> maximum left 0 == left
maximumZeroNLeft Z        = Refl
maximumZeroNLeft (S left) = Refl

maximumSuccSucc : (left : Nat) -> (right : Nat) ->
  S (maximum left right) == maximum (S left) (S right)
maximumSuccSucc x        y         = Refl
-- Idris uses unnecessary case on both x and y

sucMaxL : (l : Nat) -> maximum (S l) l == (S l)
sucMaxL Z = Refl
sucMaxL (S l) = cong S (sucMaxL l)

sucMaxR : (l : Nat) -> maximum l (S l) == (S l)
sucMaxR Z = Refl
sucMaxR (S l) = cong S (sucMaxR l)

sucMinL : (l : Nat) -> minimum (S l) l == l
sucMinL Z = Refl
sucMinL (S l) = cong S (sucMinL l)

sucMinR : (l : Nat) -> minimum l (S l) == l
sucMinR Z = Refl
sucMinR (S l) = cong S (sucMinR l)

-- div and mod
modZeroZero : (n : Nat) -> mod 0 n == 0
modZeroZero Z     = Refl
modZeroZero (S n) = Refl
