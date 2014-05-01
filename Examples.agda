module Examples where
open import Prelude
open import Context
open import Blt
open import Relation.Binary using (module DecTotalOrder; Decidable)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Vec
open import Data.Fin using (Fin; toℕ; fromℕ; raise) renaming (zero to fZ; suc to fS)
open import Data.String using (String)
-- open import Data.Bool
open import Data.Sum using (_⊎_)
-- open import Data.Nat.Properties
-- open import Data.Float

-- import Util.VectExtensions1
-- import Logic.Postulates
-- import Logic.Properties
-- import Float.Postulates
-- import Float.Properties
-- import Util.Opt
-- import Util.Util
-- import Exists.Ops
-- 
-- import DynamicProgramming.S1202_ReachabilityViability
-- import DynamicProgramming.S1203_OptimalPolicies
-- import DynamicProgramming.S1204_MaxArgmax
-- import DynamicProgramming.S1205_BackwardsInduction
-- import DynamicProgramming.S1202_ReachabilityViabilityDefaults

import BackwardsInduction 

module Example1 where

  monoNat : {a b c : Nat} → b ≤ c  →  a + b ≤ a + c
  monoNat {Z}   b≤c = b≤c
  monoNat {S a} b≤c = s≤s (monoNat {a} b≤c)

  ex1Rew : RewProp
  ex1Rew = record {
            carrier = Nat;
            0F = 0;
            _+F_ = _+_;
            _<=F_ = _≤Nat_;
            isPre = record { isEquivalence = isEquivalenceNat; 
                             reflexive = reflexive; 
                             trans = transNat };
            monoF = monoNat }
    where open DecTotalOrder decTotalOrder 
            renaming (_≤_ to _≤Nat_ ; trans to transNat; isEquivalence to isEquivalenceNat)

  maxColumnO2 : Nat
  maxColumnO2 = 2
  
  maxColumn : Nat
  maxColumn = maxColumnO2 + maxColumnO2
  
  nColumns : Nat
  nColumns = S maxColumn
  
  X : Nat -> Type
  X t = Blt nColumns

  column : {t : Nat} -> X t -> Nat
  column = toℕ
  
  states : (t : Nat) -> Vec (X t) nColumns 
  states t = tabulate (\i -> i)
  
  data Action : Set where 
    Left  : Action
    Ahead : Action
    Right : Action

  show : Action -> String
  show Left = "L"
  show Ahead = "A"
  show Right = "R"
  
  admissible : {t : Nat} -> X t -> Action -> Set
  admissible x Ahead = (column x ≡ Z) ‌⊎ (column x ≡ maxColumn)
  admissible x Left  = column x ≤ maxColumnO2
  admissible x Right = column x ≥ maxColumnO2

  Y : (t : Nat) -> X t -> Type
  Y t x = Σ Action (admissible {t} x)

  lower : ∀ {m} → (x : Fin (S m)) -> (toℕ x < m) → Fin m 
  lower fZ     (s≤s p) = fZ
  lower (fS x) (s≤s p) = fS (lower x p)

--  lower : ∀ {m} n → (x : Fin (n + m)) -> (toℕ x < m) → Fin m 
--  lower = {!!}  TODO

  _<?_ : Decidable _<_
  x <? y = S x ≤? y

  incColWrap : {m : Nat} -> Blt m -> Blt m
  incColWrap {Z} ()
  incColWrap {S m} n with toℕ n <? m 
  ... | yes  p  = lower (fS n) (s≤s p)
  ... | no   _  = fZ

  decColWrap : {m : Nat} -> Blt m -> Blt m
  decColWrap {S m} fZ      = fromℕ m
  decColWrap       (fS n)  = raise 1 n

  -- TODO: think about making this more readable (avoiding fromℕ, raise etc.)
  step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)
  step t n (Left  , _) = decColWrap n
  step t n (Ahead , _) = n
  step t n (Right , _) = incColWrap n

  data Place : Set where 
    First  : Place
    Middle : Place
    Last   : Place

  analyze : (t : Nat) -> (x : X t) -> Place
  analyze t x with toℕ x <? maxColumn
  analyze t fZ     | yes _ = First
  analyze t (fS _) | yes _ = Middle
  analyze t _      | no _  = Last

  reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Nat
  reward t x y x' with analyze (S t) x'
  ... | First   = 1
  ... | Middle  = 0
  ... | Last    = 2


  

-- --------------------------------------------------------------
  -- TODO: remember to explain specialisation of the general
  -- (parameterised) Context to the case for Nat (here) or Float or
  -- ...

  ex1Context : Context ex1Rew
  ex1Context = record { }

  viable : {t : Nat} -> (n : Nat) -> X t -> Set
  viable n x = viableDefault ex1Rew ex1Context n x

  -- Every state is viable
  viability : {t : Nat} -> (n : Nat) -> (x : X t) -> viable {t} n x
  viability n x = {!!}

  reachable : {t : Nat} -> X t -> Set
  reachable {t} x = reachableDefault ex1Rew ex1Context {t} x

  open RewProp ex1Rew
  viableStepex1 : {t : Nat} -> (n : Nat) -> X t -> Set
  viableStepex1 {t} n x = Σ (Y t x) (\y -> viable {S t} n (step t x y))

  ex1maxPair : {t : Nat} ->  (n : Nat) -> 
               (x : X t) -> 
               (r : reachable {S t} x) -> 
               (v : viable {t} (S n) x) ->
               (viableStepex1 {t} n x  ×  Nat) 
  ex1maxPair n x r v = {!!}
  -- max n x r v f = snd (maxP (outr (yfysP n x v f)))

  MaxVStep : {t : Nat} ->  (n : Nat) -> 
             (x : X t) -> 
             (r : reachable x) -> 
             (v : viable (S n) x) ->
             MaxF (Context.viableStep ex1Context n x)

  MaxVStep n x r v = 
    record { max = {!\ f -> ex1max n x r v f!}; 
             argmax = {!!}; 
             maxSpec = {!!}; 
             argmaxSpec = {!!} }


{-
{-
  succsTh : (x : X t) -> so (not (isEmpty (succs {t} x)))
  succsTh x = believe_me oh -- this should be more or less trivial
  
  viability : (n : Nat) -> (x : X t) -> so (viable {t} n x)
  viability {t}    Z x = viableSpec0 {t} x
  viability {t} (S n) k = step3 where  
    step0 : so (not (isEmpty (succs {t} k)))
    step0 = succsTh k
    step1 : (x' : X (S t) ** so (isIn {t = S t} x' (succs {t} k)))
    step1 = lemma2 (succs k) step0
    step2 : so (isAnyBy (viable {t = S t} n) (succs {t} k))
    step2 = lemma3 x' (viable {t = S t} n) (succs k) vnx' x'inCsuccsx where
      x' : X (S t)
      x' = outl step1
      vnx' : so (viable {t = S t} n x')
      vnx' = viability {t = S t} n x' -- induction step
      x'inCsuccsx : so (isIn {t = S t} x' (succs {t} k))
      x'inCsuccsx = outr step1
    step3 : so (viable {t} (S n) k)
    step3 = believe_me step2
  
  Max, argmax
  
  eqeq : Action -> Action -> Bool
  eqeq Left  Left  = True
  eqeq Left  _     = False
  eqeq Ahead Ahead = True
  eqeq Ahead _     = False
  eqeq Right Right = True
  eqeq Right _     = False
  
  eqeqSpec1 : reflexive Action eqeq
  eqeqSpec1 = believe_me oh 
  
  isIn : Action -> (n : Nat ** Vect n Action) -> Bool
  isIn = VectExtensions1.isIn Action eqeq eqeqSpec1
  
  lemma3 : (a : Action) ->
           (p : Action -> Bool) ->
           (as : (n : Nat ** Vect n Action)) ->
           so (p a) ->
           so (a `isIn` as) ->
           so (isAnyBy p as)
  lemma3 = VectExtensions1.lemma3 Action eqeq eqeqSpec1
  
  admissiblesP : (x : X t) -> 
                 (v : so (viable {t} (S n) x)) -> 
                 (k : Nat ** Vect (S k) (Y t x))
  admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where
    s1 : (n : Nat ** Vect n Action)
    s1 = (_ ** [Left, Right, Ahead])
    s2 : (y : Y t x ** so (viable {t = S t} n (step t x y)))
    s2 = viableSpec1 {t} {n} x v 
    -- removing |{t}| and |{n}| from the definition of |s2| makes the
    -- type checker eat-up the whole memory and stall
    s3 : Action
    s3 = outl (outl s2)
    s4 : so (s3 `isIn` s1)
    s4 = believe_me oh 
    -- |Action| should be in |Enum| and |s1| should be set to |[toEnum 0
    -- ..]|. Then |s4| would follow from a lemma of the kind:
    -- (Enum alpha) => (a : alpha) -> so (a `isIn` toVect [toEnum 0 ..])
    s5 : so (admissible {t} x s3)
    s5 = outr (outl s2)
    s6 : so (isAnyBy (admissible {t} x) s1)
    s6 = lemma3 s3 (admissible x) s1 s5 s4 
  
  yfysP : (n : Nat) ->
          (x : X t) -> 
          (v : so (viable {t} (S n) x)) ->
          (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
          (k : Nat 
           ** 
           Vect (S k) ((y : Y t x ** so (viable {t = S t} n (step t x y))), Float)
          )
  yfysP {t} n x v f = fmapP (pair (id,f)) s5 where
    s1 : (k : Nat ** Vect (S k) (Y t x))
    s1 = admissiblesP x v
    s2 : (k : Nat ** Vect k (Y t x))
    s2 = (_ ** outr s1)
    s3 : Y t x -> Bool
    s3 y = viable {t = S t} n (step t x y)
    s4 : so (isAnyBy s3 s2)
    s4 = believe_me oh -- this should be more or less trivial
    s5 : (k : Nat ** Vect (S k) (y : Y t x ** so (s3 y)))
    s5 = filterTagP s3 (outr s2) s4
  
  MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))
  
  MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))
  
  MaxArgmax.maxSpec n x r v f yv = believe_me oh -- this should be
                                                 -- granted by |maxP|
  
  MaxArgmax.argmaxSpec n x r v f = believe_me oh -- this should be
                                                 -- granted by |maxP|
  
  
  The computation:
  
  nSteps : Nat
  nSteps = 8
  
  ps : PolicySeq Z nSteps
  ps = backwardsInduction Z nSteps
  
  controls : (t : Nat) -> 
             (n : Nat) -> 
             (x : X t) -> 
             (r : so (reachable {t} x)) -> 
             (v : so (viable {t} n x)) ->
             PolicySeq t n -> 
             Vect n Action
  controls _ Z _ _ _ _ = Nil
  controls t (S n) x r v (p :: ps) =
    ((outl y) :: (controls (S t) n x' r' v' ps)) where
      yq : (a : Y t x ** so (viable {t = S t} n (step t x a)))
      yq = p x r v
      y : Y t x    
      y = outl yq
      x' : X (S t)
      x' = step t x y
      r' : so (reachable {t = S t} x')
      r' = reachableSpec1 x r y
      v' : so (viable {t = S t} n x')
      v' = outr yq
  
  x0 : X Z
  x0 = (2 ** oh)
  
  r0 : so (reachable {t = Z} x0)
  r0 = oh
  
  v0 : so (viable {t = Z} nSteps x0)
  v0 = viability {t = Z} nSteps x0
  
  as : Vect nSteps Action 
  as = controls Z nSteps x0 r0 v0 ps
  
  main : IO ()
  main = putStrLn (show as)







-}
-}
