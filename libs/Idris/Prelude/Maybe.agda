module Idris.Prelude.Maybe where

open import Idris.Builtins
-- import Idris.Prelude.Algebra
-- import Idris.Prelude.Basics
open import Idris.Prelude.Bool
-- import Idris.Prelude.Cast
open import Idris.Prelude.Classes -- using (EqDict; EqDict')
-- import Idris.Prelude.Foldable

data Maybe (a : Type) : Type where
  Nothing : Maybe a
  Just : a -> Maybe a

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

isNothing : {a : Type} -> Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just j) = False

isJust : {a : Type} -> Maybe a -> Bool
isJust Nothing  = False
isJust (Just j) = True

-- ||| Proof that some `Maybe` is actually `Just`
data IsJust {a : Type} : Maybe a -> Type where
  ItIsJust : {x : a} -> IsJust (Just x)

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

maybe : {a : Type} -> {b : Type} ->
        Lazy b -> Lazy (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = (Force j) x


-- ||| Convert a `Maybe a` value to an `a` value by providing a default `a` value
-- ||| in the case that the `Maybe` value is `Nothing`.
fromMaybe : {a : Type} ->
            (Lazy a) -> Maybe a -> a
fromMaybe def Nothing  = def
fromMaybe def (Just j) = j

-- ||| Returns `Just` the given value if the conditional is `True`
-- ||| and `Nothing` if the conditional is `False`.
toMaybe : {a : Type} ->
          Bool -> Lazy a -> Maybe a
toMaybe True  j = Just j
toMaybe False j = Nothing

justInjective : {t : Type} ->
                {x : t} -> {y : t} -> (Just x == Just y) -> (x == y)
justInjective Refl = Refl

{- TODOclassdict
-- ||| Convert a `Maybe a` value to an `a` value, using `neutral` in the case
-- ||| that the `Maybe` value is `Nothing`.
lowerMaybe : Monoid a => Maybe a -> a
lowerMaybe Nothing = neutral
lowerMaybe (Just x) = x

||| Returns `Nothing` when applied to `neutral`, and `Just` the value otherwise.
raiseToMaybe : (Monoid a, Eq a) => a -> Maybe a
raiseToMaybe x = if x == neutral then Nothing else Just x
-}


--------------------------------------------------------------------------------
-- Class instances
--------------------------------------------------------------------------------

maybe_bind : {a : Type} -> {b : Type} ->
             Maybe a -> (a -> Maybe b) -> Maybe b
maybe_bind Nothing  k = Nothing
maybe_bind (Just x) k = k x

-- instance (Eq a) => Eq (Maybe a) where

eqMaybe : {a : Type} -> EqDict a -> EqDict' (Maybe a)
eqMaybe eqa Nothing  Nothing  = True
eqMaybe eqa Nothing  (Just _) = False
eqMaybe eqa (Just _) Nothing  = False
eqMaybe eqa (Just a) (Just b) = a === b
  where open EqDict eqa

eqDictMaybe : {a : Type} -> EqDict a -> EqDict (Maybe a)
eqDictMaybe eqa = record {_===_ = eqMaybe eqa}

{- TODOinst: the rest of the file!

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
