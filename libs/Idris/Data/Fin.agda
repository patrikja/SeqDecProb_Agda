module Idris.Data.Fin where
open import Idris.Builtins
open import Idris.Prelude.Basics
open import Idris.Prelude.Nat
open import Idris.Prelude.Either
open import Idris.Prelude.Maybe
-- ||| Numbers strictly less than some bound.  The name comes from "finite sets".
-- |||
-- ||| It's probably not a good idea to use `Fin` for arithmetic, and they will be
-- ||| exceedingly inefficient at run time.
-- ||| @ n the upper bound
data Fin : (n : Nat) -> Type where
    FZ : {k : Nat} -> Fin (S k)
    FS : {k : Nat} -> Fin k -> Fin (S k)

{- TODO
instance Uninhabited (Fin Z) where
  uninhabited FZ impossible
  uninhabited (FS f) impossible
-}

FSInjective : {k : Nat} ->
              (m : Fin k) -> (n : Fin k) -> FS m == FS n -> m == n
FSInjective m .m Refl = Refl

{- TODO
instance Eq (Fin n) where
    (==) FZ FZ = True
    (==) (FS k) (FS k') = k == k'
    (==) _ _ = False
-}


-- ||| There are no elements of `Fin Z`
FinZAbsurd : Fin Z -> Void
FinZAbsurd ()

FinZElim : {a : Type} ->
           Fin Z -> a
FinZElim x = void (FinZAbsurd x)

-- ||| Convert a Fin to a Nat
finToNat : {n : Nat} ->
           Fin n -> Nat
finToNat FZ = Z
finToNat (FS k) = S (finToNat k)

-- ||| `finToNat` is injective
finToNatInjective : {k : Nat} ->
                    (fm : Fin k) -> (fn : Fin k) -> (finToNat fm) == (finToNat fn) -> fm == fn
finToNatInjective FZ     FZ     _   = Refl
finToNatInjective FZ     (FS n) ()
finToNatInjective (FS m) FZ     ()
finToNatInjective (FS m) (FS n) prf = cong FS (finToNatInjective m n (succInjective (finToNat m) (finToNat n) prf))
--

{- TODO
instance Cast (Fin n) Nat where
    cast x = finToNat x
-}

{- TODO
-- ||| Convert a Fin to an Integer
finToInteger : {n : Nat} ->
               Fin n -> Integer
finToInteger FZ     = 0
finToInteger (FS k) = 1 + finToInteger k


instance Cast (Fin n) Integer where
    cast x = finToInteger x
-}

-- ||| Weaken the bound on a Fin by 1
weaken : {n : Nat} ->
         Fin n -> Fin (S n)
weaken FZ     = FZ
weaken (FS k) = FS (weaken k)

-- ||| Weaken the bound on a Fin by some amount
weakenN : {m : Nat} ->
          (n : Nat) -> Fin m -> Fin (m + n)
weakenN n FZ = FZ
weakenN n (FS f) = FS (weakenN n f)

-- ||| Attempt to tighten the bound on a Fin.
-- ||| Return `Left` if the bound could not be tightened, or `Right` if it could.
{- TODO
strengthen : {n : Nat} ->
             Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} FZ = Right FZ
strengthen {n = S k} (FS i) with (strengthen i)
strengthen (FS k) | Left x   = Left (FS x)
strengthen (FS k) | Right x  = Right (FS x)
strengthen f = Left f
-}

-- ||| Add some natural number to a Fin, extending the bound accordingly
-- ||| @ n the previous bound
-- ||| @ m the number to increase the Fin by
shift : {n : Nat} ->
        (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift {n = n} (S m) f = FS {k = (m + n)} (shift m f)

-- ||| The largest element of some Fin type
last : {n : Nat} -> Fin (S n)
last {n = Z} = FZ
last {n = S _} = FS last

FSinjective : {n : Nat} ->
              {f : Fin n} -> {f' : Fin n} -> (FS f == FS f') -> f == f'
FSinjective Refl = Refl

{-
instance Ord (Fin n) where
  compare  FZ     FZ    = EQ
  compare  FZ    (FS _) = LT
  compare (FS _)  FZ    = GT
  compare (FS x) (FS y) = compare x y

instance MinBound (Fin (S n)) where
  minBound = FZ

instance MaxBound (Fin (S n)) where
  maxBound = last
-}

{- TODO
-- ||| Add two Fins, extending the bound
_+_ : {m n : Nat} ->
      Fin n -> Fin m -> Fin (n + m)
_+_ {n = S n} {m = m} FZ f' = ? -- rewrite plusCommutative n m in weaken (weakenN n f')
_+_ (FS f) f' = FS (f + f')


-- ||| Substract two Fins, keeping the bound of the minuend
_-_ : {m n : Nat} -> Fin n -> Fin m -> Fin n
FZ - _ = FZ
f - FZ = f
(FS f) - (FS f') = weaken $ f - f'

-- ||| Multiply two Fins, extending the bound
_*_ : {m n : Nat} ->
      Fin n -> Fin m -> Fin (n * m)
_*_ {n=Z} f f' = FinZElim f
_*_ {m=Z} f f' = FinZElim f'
_*_ {n=S n} {m=S m} FZ     f' = FZ
_*_ {n=S n} {m=S m} (FS f) f' = f' + (f * f')
-}

-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just FZ
natToFin (S k) (S j) with (natToFin k j)
...                       | Just k' = Just (FS k')
...                       | Nothing = Nothing
natToFin _ _ = Nothing

{- TODO
integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x Z = Nothing -- make sure 'n' is concrete, to save reduction!
integerToFin x n = if x >= 0 then natToFin (cast x) n else Nothing


-- ||| Allow overloading of Integer literals for Fin.
-- ||| @ x the Integer that the user typed
-- ||| @ prf an automatically-constructed proof that `x` is in bounds
fromInteger : (x : Integer) ->
              {default ItIsJust
               prf : (IsJust (integerToFin x n))} ->
              Fin n
fromInteger {n} x {prf} with (integerToFin x n)
fromInteger {n} x {prf = ItIsJust} | Just y = y


-- %language ErrorReflection


finFromIntegerErrors : Err -> Maybe (List ErrorReportPart)
finFromIntegerErrors (CantUnify x tm `(IsJust (integerToFin ~n ~m)) err xs y)
  = Just [ TextPart "When using", TermPart n
         , TextPart "as a literal for a"
         , TermPart `(Fin ~m)
         , SubReport [ TextPart "Could not show that"
                     , TermPart n
                     , TextPart "is less than"
                     , TermPart m
                     ]
         ]
finFromIntegerErrors _ = Nothing
-}

{- TODO
%error_handlers Data.Fin.fromInteger prf finFromIntegerErrors

instance Enum (Fin (S n)) where
  pred FZ = FZ
  pred (FS n) = weaken n
  succ n = case strengthen (FS n) of
    Left _ => last
    Right k => k
  toNat n = cast n
  fromNat {n=n} m = case natToFin m (S n) of
    Just k => k
    Nothing => last
-}

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

FZNotFS : {n : Nat} ->
          {f : Fin n} -> FZ {k = n} == FS f -> Void
FZNotFS ()

{- TODO
instance DecEq (Fin n) where
  decEq FZ FZ = Yes Refl
  decEq FZ (FS f) = No FZNotFS
  decEq (FS f) FZ = No $ negEqSym FZNotFS
  decEq (FS f) (FS f') with (decEq f f')
    | Yes p = Yes $ cong ? p
    | No p = No $ \h => p $ FSinjective {f = f} {f' = f'} h
-}
