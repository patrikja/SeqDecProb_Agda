module Idris.Prelude.Classes where

open import Idris.Builtins
open import Idris.Prelude.Basics
open import Idris.Prelude.Bool

{- TODO
-- Numerical Operator Precedence
infixl 5 _==_ _/=_
infixl 6 _<_ _<=_ _>_ _>=_
infixl 7 _<<_ _>>_
infixl 8 _+_ _-_
infixl 9 _*_ _/_


-- ------------------------------------------------------------- [ Boolean Ops ]
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

boolOp : (a -> a -> Int) -> a -> a -> Bool
boolOp op x y = intToBool (op x y)

-- ---------------------------------------------------------- [ Equality Class ]
-}
EqDict' : Type -> Type
EqDict' a = a -> a -> Bool

record EqDict (a : Type) : Type where
  field
    _===_ : EqDict' a
  _/=_ : EqDict' a
  x /= y = not (x === y)


{-
||| The Eq class defines inequality and equality.
class Eq a where
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)
-}

eqUnit : EqDict' Unit
eqUnit unit unit = True

eqDictUnit : EqDict Unit
eqDictUnit = record { _===_ = eqUnit }

primitive
  primIntegerEquality : Int -> Int -> Bool

-- instance Eq Int where
eqInt : EqDict' Int
eqInt = primIntegerEquality

eqDictInt : EqDict Int
eqDictInt = record { _===_ = eqInt }

{- TODOinst
instance Eq Integer where
    (==) = boolOp prim__eqBigInt

instance Eq Float where
    (==) = boolOp prim__eqFloat

instance Eq Char where
    (==) = boolOp prim__eqChar

instance Eq String where
    (==) = boolOp prim__eqString
-}

-- instance Eq Bool where
eqBool : EqDict' Bool
eqBool True  True  = True
eqBool True  False = False
eqBool False True  = False
eqBool False False = True

eqDictBool = record { _===_ = eqBool }

-- instance (Eq a, Eq b) => Eq (a, b) where
eqPair : {a : Type} -> {b : Type} ->
         EqDict' a -> EqDict' b -> EqDict' (a × b)
eqPair _==a_ _==b_
       (a , b) (a' , b') = (a ==a a') && (b ==b b')



-- ---------------------------------------------------------- [ Ordering Class ]

data Ordering : Type where
  LT EQ GT : Ordering

-- instance Eq Ordering where
eqOrdering : EqDict' Ordering
eqOrdering LT LT = True
eqOrdering EQ EQ = True
eqOrdering GT GT = True
eqOrdering _  _  = False

eqOrdDict : EqDict Ordering
eqOrdDict = record { _===_ = eqOrdering }

OrdDict' : Type -> Type
OrdDict' a = a -> a -> Ordering

-- ||| The Ord class defines comparison operations on ordered data types.
record OrdDict (a : Type) : Type where
  field
    eqDict  : EqDict a
    compare : OrdDict' a
  open EqDict eqDict public

  -- The rest of the record / module is helper functions
  _<_ : a -> a -> Bool
  x < y with (compare x y)
  x < y | LT = True
  x < y | _  = False

  _>_ : a -> a -> Bool
  x > y with (compare x y)
  x > y | GT = True
  x > y | _  = False

  _<=_ : a -> a -> Bool
  x <= y = x < y || x === y

  _>=_ : a -> a -> Bool
  x >= y = x > y || x === y

  max : a -> a -> a
  max x y = if (x > y) then x else y

  min : a -> a -> a
  min x y = if (x < y) then x else y


-- instance Ord ()
compareUnit : OrdDict' Unit
compareUnit unit unit = EQ
ordDictUnit : OrdDict Unit
ordDictUnit = record { eqDict = eqDictUnit; compare = compareUnit }

{- TODOinst convert to dictionaries

instance Ord Int where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltInt x y) then LT else
                  GT


instance Ord Integer where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltBigInt x y) then LT else
                  GT


instance Ord Float where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltFloat x y) then LT else
                  GT


instance Ord Char where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__sltChar x y) then LT else
                  GT


instance Ord String where
    compare x y = if (x == y) then EQ else
                  if (boolOp prim__ltString x y) then LT else
                  GT
-}

-- instance Ord Bool
compareBool : OrdDict' Bool
compareBool True  True  = EQ
compareBool False False = EQ
compareBool False True  = LT
compareBool True  False = GT

ordDictBool : OrdDict Bool
ordDictBool = record { eqDict = eqDictBool ; compare = compareBool }

{-

instance (Ord a, Ord b) => Ord (a, b) where
  compare (xl, xr) (yl, yr) =
    if xl /= yl
      then compare xl yl
      else compare xr yr

-- --------------------------------------------------------- [ Negatable Class ]
||| The `Neg` class defines unary negation (-).
class Neg a where
    ||| The underlying implementation of unary minus. `-5` desugars to `negate (fromInteger 5)`.
    negate : a -> a

instance Neg Integer where
    negate x = prim__subBigInt 0 x

instance Neg Int where
    negate x = prim__subInt 0 x

instance Neg Float where
    negate x = prim__negFloat x

-- --------------------------------------------------------- [ Numerical Class ]
||| The Num class defines basic numerical arithmetic.
class Num a where
    (+) : a -> a -> a
    (-) : a -> a -> a
    (*) : a -> a -> a
    ||| Absolute value
    abs : a -> a
    ||| Conversion from Integer.
    fromInteger : Integer -> a

instance Num Integer where
    (+) = prim__addBigInt
    (-) = prim__subBigInt
    (*) = prim__mulBigInt

    abs x = if x < 0 then -x else x
    fromInteger = id

instance Num Int where
    (+) = prim__addInt
    (-) = prim__subInt
    (*) = prim__mulInt

    fromInteger = prim__truncBigInt_Int
    abs x = if x < (prim__truncBigInt_Int 0) then -x else x


instance Num Float where
    (+) = prim__addFloat
    (-) = prim__subFloat
    (*) = prim__mulFloat

    abs x = if x < (prim__toFloatBigInt 0) then -x else x
    fromInteger = prim__toFloatBigInt

instance Num Bits8 where
  (+) = prim__addB8
  (-) = prim__subB8
  (*) = prim__mulB8
  abs = id
  fromInteger = prim__truncBigInt_B8

instance Num Bits16 where
  (+) = prim__addB16
  (-) = prim__subB16
  (*) = prim__mulB16
  abs = id
  fromInteger = prim__truncBigInt_B16

instance Num Bits32 where
  (+) = prim__addB32
  (-) = prim__subB32
  (*) = prim__mulB32
  abs = id
  fromInteger = prim__truncBigInt_B32

instance Num Bits64 where
  (+) = prim__addB64
  (-) = prim__subB64
  (*) = prim__mulB64
  abs = id
  fromInteger = prim__truncBigInt_B64

instance Eq Bits8 where
  x == y = intToBool (prim__eqB8 x y)

instance Eq Bits16 where
  x == y = intToBool (prim__eqB16 x y)

instance Eq Bits32 where
  x == y = intToBool (prim__eqB32 x y)

instance Eq Bits64 where
  x == y = intToBool (prim__eqB64 x y)

instance Ord Bits8 where
  (<) = boolOp prim__ltB8
  (>) = boolOp prim__gtB8
  (<=) = boolOp prim__lteB8
  (>=) = boolOp prim__gteB8
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

instance Ord Bits16 where
  (<) = boolOp prim__ltB16
  (>) = boolOp prim__gtB16
  (<=) = boolOp prim__lteB16
  (>=) = boolOp prim__gteB16
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

instance Ord Bits32 where
  (<) = boolOp prim__ltB32
  (>) = boolOp prim__gtB32
  (<=) = boolOp prim__lteB32
  (>=) = boolOp prim__gteB32
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

instance Ord Bits64 where
  (<) = boolOp prim__ltB64
  (>) = boolOp prim__gtB64
  (<=) = boolOp prim__lteB64
  (>=) = boolOp prim__gteB64
  compare l r = if l < r then LT
                else if l > r then GT
                     else EQ

-- ------------------------------------------------------------- [ Bounded ]

class Ord b => MinBound b where
  ||| The lower bound for the type
  minBound : b

class Ord b => MaxBound b where
  ||| The upper bound for the type
  maxBound : b

instance MinBound Bits8 where
  minBound = 0x0

instance MaxBound Bits8 where
  maxBound = 0xff

instance MinBound Bits16 where
  minBound = 0x0

instance MaxBound Bits16 where
  maxBound = 0xffff

instance MinBound Bits32 where
  minBound = 0x0

instance MaxBound Bits32 where
  maxBound = 0xffffffff

instance MinBound Bits64 where
  minBound = 0x0

instance MaxBound Bits64 where
  maxBound = 0xffffffffffffffff


-- ------------------------------------------------------------- [ Fractionals ]

||| Fractional division of two Floats.
(/) : Float -> Float -> Float
(/) = prim__divFloat


-- --------------------------------------------------------------- [ Integrals ]
%default partial

class Integral a where
   div : a -> a -> a
   mod : a -> a -> a

-- ---------------------------------------------------------------- [ Integers ]
divBigInt : Integer -> Integer -> Integer
divBigInt = prim__sdivBigInt

modBigInt : Integer -> Integer -> Integer
modBigInt = prim__sremBigInt

instance Integral Integer where
  div = divBigInt
  mod = modBigInt

-- --------------------------------------------------------------------- [ Int ]

divInt : Int -> Int -> Int
divInt = prim__sdivInt

modInt : Int -> Int -> Int
modInt = prim__sremInt

instance Integral Int where
  div = divInt
  mod = modInt

-- ------------------------------------------------------------------- [ Bits8 ]
divB8 : Bits8 -> Bits8 -> Bits8
divB8 = prim__sdivB8

modB8 : Bits8 -> Bits8 -> Bits8
modB8 = prim__sremB8

instance Integral Bits8 where
  div = divB8
  mod = modB8

-- ------------------------------------------------------------------ [ Bits16 ]
divB16 : Bits16 -> Bits16 -> Bits16
divB16 = prim__sdivB16

modB16 : Bits16 -> Bits16 -> Bits16
modB16 = prim__sremB16

instance Integral Bits16 where
  div = divB16
  mod = modB16

-- ------------------------------------------------------------------ [ Bits32 ]
divB32 : Bits32 -> Bits32 -> Bits32
divB32 = prim__sdivB32

modB32 : Bits32 -> Bits32 -> Bits32
modB32 = prim__sremB32

instance Integral Bits32 where
  div = divB32
  mod = modB32

-- ------------------------------------------------------------------ [ Bits64 ]
divB64 : Bits64 -> Bits64 -> Bits64
divB64 = prim__sdivB64

modB64 : Bits64 -> Bits64 -> Bits64
modB64 = prim__sremB64

instance Integral Bits64 where
  div = divB64
  mod = modB64
-}
