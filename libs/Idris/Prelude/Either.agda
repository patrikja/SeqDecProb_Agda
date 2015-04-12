module Idris.Prelude.Either where

open import Idris.Builtins
open import Idris.Syntax.PreorderReasoning
-- import Idris.Prelude.Basics
open import Idris.Prelude.Bool
-- import Idris.Prelude.Classes
-- import Idris.Prelude.Maybe
-- import Idris.Prelude.List

-- ||| A sum type
data Either (a : Type) (b : Type) : Type where
  -- ||| One possibility of the sum, conventionally used to represent errors
  Left : a -> Either a b
  -- ||| The other possibility, conventionally used to represent success
  Right : b -> Either a b

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

-- ||| True if the argument is Left, False otherwise
isLeft : {a : Type} -> {b : Type} ->
         Either a b -> Bool
isLeft (Left l)  = True
isLeft (Right r) = False

-- ||| True if the argument is Right, False otherwise
isRight : {a : Type} -> {b : Type} ->
          Either a b -> Bool
isRight (Left l)  = False
isRight (Right r) = True

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

-- ||| Simply-typed eliminator for Either
-- ||| @ f the action to take on Left
-- ||| @ g the action to take on Right
-- ||| @ e the sum to analyze
either : {a : Type} -> {b : Type} -> {c : Type} ->
         (f : Lazy (a -> c)) -> (g : Lazy (b -> c)) -> (e : Either a b) -> c
either l r (Left x)  = (Force l) x
either l r (Right x) = (Force r) x

{-
-- ||| Keep the payloads of all Left constructors in a list of Eithers
lefts : {a : Type} -> {b : Type} ->
        List (Either a b) -> List a
lefts []      = []
lefts (x::xs) =
  case x of
    Left  l => l :: lefts xs
    Right r => lefts xs

-- ||| Keep the payloads of all Right constructors in a list of Eithers
rights : List (Either a b) -> List b
rights []      = []
rights (x::xs) =
  case x of
    Left  l => rights xs
    Right r => r :: rights xs

-- ||| Split a list of Eithers into a list of the left elements and a list of the right elements
partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers l = (lefts l, rights l)
-}

-- ||| Remove a "useless" Either by collapsing the case distinction
fromEither : {a : Type} ->
             Either a a -> a
fromEither (Left l)  = l
fromEither (Right r) = r

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

{-
-- ||| Convert a Maybe to an Either by using a default value in case of Nothing
-- ||| @ e the default value
maybeToEither : {a : Type} -> {e : Type} ->
                (def : Lazy e) -> Maybe a -> Either e a
maybeToEither def (Just j) = Right j
maybeToEither def Nothing  = Left  def
-}

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

{-
instance (Eq a, Eq b) => Eq (Either a b) where
  (==) (Left x)  (Left y)  = x == y
  (==) (Right x) (Right y) = x == y
  (==) _         _         = False
-}


--------------------------------------------------------------------------------
-- Injectivity of constructors
--------------------------------------------------------------------------------

-- ||| Left is injective
leftInjective : {a : Type} -> {b : Type} -> {x : a} -> {y : a}
             -> (Left {b = b} x == Left y) -> (x == y)
leftInjective Refl = Refl

-- ||| Right is injective
rightInjective : {a : Type} -> {b : Type} -> {x : b} -> {y : b}
             -> (Right {a = a} x == Right {a = a} y) -> (x == y)
rightInjective Refl = Refl
