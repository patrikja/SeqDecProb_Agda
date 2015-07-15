module Idris.Prelude.Decidable.Equality where

open import Idris.Builtins
open import Idris.Prelude.Basics
open import Idris.Prelude.Bool
-- import Prelude.Classes
open import Idris.Prelude.Either
-- import Prelude.List
open import Idris.Prelude.Nat
open import Idris.Prelude.Maybe

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

-- ||| The negation of equality is symmetric (follows from symmetry of equality)
negEqSym : {t : Type} ->
           {a : t} -> {b : t} -> (a == b -> Void) -> (b == a -> Void)
negEqSym p h = p (sym h)


--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

DecEqDict' : Type -> Type
DecEqDict' t = (x1 : t) -> (x2 : t) -> Dec (x1 == x2)

record DecEqDict (a : Type) : Type where
  field
    decEq : DecEqDict' a

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

decEqUnit : DecEqDict' Unit
decEqUnit unit unit = Yes Refl

decEqDictUnit : DecEqDict Unit
decEqDictUnit = record { decEq = decEqUnit }

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------
trueNotFalse : True == False -> Void
trueNotFalse ()

-- instance DecEq Bool where

decEqBool : DecEqDict' Bool
decEqBool True  True  = Yes Refl
decEqBool False False = Yes Refl
decEqBool True  False = No trueNotFalse
decEqBool False True  = No (negEqSym trueNotFalse)

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

ZnotS : {n : Nat} ->
        Z == S n -> Void
ZnotS ()


-- instance DecEq Nat where
-- decEqNat already defined in Idris.Prelude.Nat

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

nothingNotJust : {t : Type} ->
                 {x : t} -> (Nothing {a = t} == Just x) -> Void
nothingNotJust ()

-- instance (DecEq t) => DecEq (Maybe t) where
decEqMaybe : {a : Type} -> DecEqDict a -> DecEqDict' (Maybe a)
decEqMaybe _ Nothing Nothing = Yes Refl
decEqMaybe da (Just x') (Just y') with (DecEqDict.decEq da x' y')
... | Yes p  = Yes (cong Just p)
... | No  p  = No (\h -> p (justInjective h))
decEqMaybe _ Nothing (Just _) = No nothingNotJust
decEqMaybe _ (Just _) Nothing = No (negEqSym nothingNotJust)

decEqDictMaybe : {a : Type} -> DecEqDict a -> DecEqDict (Maybe a)
decEqDictMaybe da = record { decEq = decEqMaybe da }


--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

leftNotRight : {a : Type} -> {b : Type} ->
               {x : a} -> {y : b} -> Left {b = b} x == Right {a = a} y -> Void
leftNotRight ()


-- instance (DecEq a, DecEq b) => DecEq (Either a b) where
decEqEither : {a : Type} -> {b : Type} ->
              DecEqDict a -> DecEqDict b -> DecEqDict' (Either a b)
decEqEither da db (Left x') (Left y') with (DecEqDict.decEq da x' y')
... | Yes p = Yes (cong Left p)
... | No p = No (\h -> p (leftInjective h))
decEqEither da db (Right x') (Right y') with (DecEqDict.decEq db x' y')
... | Yes p = Yes (cong Right p)
... | No p = No (\h -> p (rightInjective h))
decEqEither da db (Left x') (Right y') = No leftNotRight
decEqEither da db (Right x') (Left y') = No (negEqSym leftNotRight)


--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

{- TODO: Cleanup this intermediate code and replace with proper solution;-)
helper1 : {a : Type} -> {b : Type} -> (x : a) -> (y : b) -> (x == y) -> (a == b)
helper1 x .x Refl = Refl

helper2 :  {a b a' b' : Type} ->
           (a × b) == (a' × b') ->
           (a == b)
helper2 q = {!q!}

-- hcong' {!!} {!!} {!\ ab -> fst {fst ab} {snd ab}!} q
-- fst (x , y) == fst (x' , y')
-- fst {.a} {.b} (x  , y )  ==  fst {.c} {.d} (x' , y')
-- fst : {a b : Set} -> a × b -> a
mycong : (Q : Set -> Set -> Set) ->
         (f : {a b : Set} -> a × b -> Q a b) ->
         {a b c d : Type} ->
--         {x : a} {y : b} {x' : c} {y' : d} ->
--         (p : (x , y) == (x' , y')) -> (f {a} {b} (x , y) == f {c} {d} (x' , y'))
         {xy : a × b} {xy' : c × d} ->
         (p : xy == xy') -> (f {a} {b} xy == f {c} {d} xy')
mycong Q f p = {!p!}
-}

lemmaFstEq :  {a b c d : Type} ->
                 {x : a} {y : b} {x' : c} {y' : d} ->
                 (x , y) == (x' , y')   ->  (x == x') -- × (y == y')
lemmaFstEq {a} {b} {c} {d} {x} {y} {x'} {y'} q =
                x                      ==< Refl >==
                fst {a} {b} (x  , y )  ==< {!cong fst q!} >==   -- TODO: this is not quite type correct
                fst {c} {d} (x' , y')  ==< Refl >==
                x' QED

lemma_both_neq : {a b c d : Type} ->
                 {x : a} {y : b} {x' : c} {y' : d} ->
                 (x == x' -> Void) -> (y == y' -> Void) -> ((x , y) == (x' , y') -> Void)
lemma_both_neq p_x_not_x' p_y_not_y' q = p_x_not_x' (lemmaFstEq q)

{- TODO rest of the file
lemma_snd_neq : {x : a, y : b, y' : d} -> (x = x) -> (y = y' -> Void) -> ((x, y) = (x, y') -> Void)
lemma_snd_neq Refl p Refl = p Refl

lemma_fst_neq_snd_eq : {x : a, x' : b, y : c, y' : d} ->
                       (x = x' -> Void) ->
                       (y = y') ->
                       ((x, y) = (x', y) -> Void)
lemma_fst_neq_snd_eq p_x_not_x' Refl Refl = p_x_not_x' Refl

instance (DecEq a, DecEq b) => DecEq (a, b) where
  decEq (a, b) (a', b')     with (decEq a a')
    decEq (a, b) (a, b')    | (Yes Refl) with (decEq b b')
      decEq (a, b) (a, b)   | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (a, b) (a, b')  | (Yes Refl) | (No p) = No (\eq => lemma_snd_neq Refl p eq)
    decEq (a, b) (a', b')   | (No p)     with (decEq b b')
      decEq (a, b) (a', b)  | (No p)     | (Yes Refl) =  No (\eq => lemma_fst_neq_snd_eq p Refl eq)
      decEq (a, b) (a', b') | (No p)     | (No p') = No (\eq => lemma_both_neq p p' eq)


--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

lemma_val_not_nil : {x : t, xs : List t} -> ((x :: xs) = Prelude.List.Nil {a = t} -> Void)
lemma_val_not_nil Refl impossible

lemma_x_eq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y) -> (xs = ys -> Void) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_eq_xs_neq Refl p Refl = p Refl

lemma_x_neq_xs_eq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> Void) -> (xs = ys) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_eq p Refl Refl = p Refl

lemma_x_neq_xs_neq : {x : t, xs : List t, y : t, ys : List t} -> (x = y -> Void) -> (xs = ys -> Void) -> ((x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_neq p p' Refl = p Refl

instance DecEq a => DecEq (List a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) [] = No lemma_val_not_nil
  decEq [] (x :: xs) = No (negEqSym lemma_val_not_nil)
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys) | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No p) = No (\eq => lemma_x_eq_xs_neq Refl p eq)
    decEq (x :: xs) (y :: ys) | No p with (decEq xs ys)
      decEq (x :: xs) (y :: xs) | (No p) | (Yes Refl) = No (\eq => lemma_x_neq_xs_eq p Refl eq)
      decEq (x :: xs) (y :: ys) | (No p) | (No p') = No (\eq => lemma_x_neq_xs_neq p p' eq)


-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations.

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

instance DecEq Int where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Char
--------------------------------------------------------------------------------

instance DecEq Char where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void

--------------------------------------------------------------------------------
-- Integer
--------------------------------------------------------------------------------

instance DecEq Integer where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void


--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------

instance DecEq String where
    decEq x y = if x == y then Yes primitiveEq else No primitiveNotEq
       where primitiveEq : x = y
             primitiveEq = believe_me (Refl {x})
             postulate primitiveNotEq : x = y -> Void
-}
