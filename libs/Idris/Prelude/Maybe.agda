module Idris.Prelude.Maybe where

open import Idris.Builtins
-- import Idris.Prelude.Algebra
-- import Idris.Prelude.Basics
-- import Idris.Prelude.Bool
-- import Idris.Prelude.Cast
-- import Idris.Prelude.Classes
-- import Idris.Prelude.Foldable

data Maybe (a : Type) : Type where
  Nothing : Maybe a
  Just : a -> Maybe a

{- TODO: the rest of the file!

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just j) = False

isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just j) = True

||| Proof that some `Maybe` is actually `Just`
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just x)

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

maybe : Lazy b -> Lazy (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = (Force j) x

||| Convert a `Maybe a` value to an `a` value by providing a default `a` value
||| in the case that the `Maybe` value is `Nothing`.
fromMaybe : (Lazy a) -> Maybe a -> a
fromMaybe def Nothing  = def
fromMaybe def (Just j) = j

||| Returns `Just` the given value if the conditional is `True`
||| and `Nothing` if the conditional is `False`.
toMaybe : Bool -> Lazy a -> Maybe a
toMaybe True  j = Just j
toMaybe False j = Nothing

justInjective : {x : t} -> {y : t} -> (Just x = Just y) -> x = y
justInjective Refl = Refl

||| Convert a `Maybe a` value to an `a` value, using `neutral` in the case
||| that the `Maybe` value is `Nothing`.
lowerMaybe : Monoid a => Maybe a -> a
lowerMaybe Nothing = neutral
lowerMaybe (Just x) = x

||| Returns `Nothing` when applied to `neutral`, and `Just` the value otherwise.
raiseToMaybe : (Monoid a, Eq a) => a -> Maybe a
raiseToMaybe x = if x == neutral then Nothing else Just x

--------------------------------------------------------------------------------
-- Class instances
--------------------------------------------------------------------------------

maybe_bind : Maybe a -> (a -> Maybe b) -> Maybe b
maybe_bind Nothing  k = Nothing
maybe_bind (Just x) k = k x

instance (Eq a) => Eq (Maybe a) where
  Nothing  == Nothing  = True
  Nothing  == (Just _) = False
  (Just _) == Nothing  = False
  (Just a) == (Just b) = a == b

-- Lift a semigroup into 'Maybe' forming a 'Monoid' according to
-- <http://en.wikipedia.org/wiki/Monoid>: "Any semigroup S may be
-- turned into a monoid simply by adjoining an element i not in S
-- and defining i+i = i and i+s = s = s+i for all s in S."

instance (Semigroup a) => Semigroup (Maybe a) where
  Nothing <+> m = m
  m <+> Nothing = m
  (Just m1) <+> (Just m2) = Just (m1 <+> m2)

instance (Semigroup a) => Monoid (Maybe a) where
  neutral = Nothing

instance (Monoid a, Eq a) => Cast a (Maybe a) where
  cast = raiseToMaybe

instance (Monoid a) => Cast (Maybe a) a where
  cast = lowerMaybe

instance Foldable Maybe where
  foldr _ z Nothing = z
  foldr f z (Just x) = f x z
-}
