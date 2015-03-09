module Examples where
open import Prelude
import Context -- not opened yet to avoid namespace pollution

open import Blt
open import Relation.Binary using (module DecTotalOrder; Decidable)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Vec
open import Data.Fin using (Fin; toℕ; fromℕ; raise) renaming (zero to fZ; suc to fS)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Max

import BackwardsInduction 

module Example1 where

  monoNat : {a b c : Nat} → b ≤ c  →  a + b ≤ a + c
  monoNat {Z}   b≤c = b≤c
  monoNat {S a} b≤c = s≤s (monoNat {a} b≤c)

  ex1Rew : Context.RewType
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

  data Place : Set where 
    First  : Place
    Middle : Place
    Last   : Place

  -- TODO: Move up/out
  _<?_ : Decidable _<_
  x <? y = S x ≤? y

  analyze : (x : Blt nColumns) -> Place
  analyze x with toℕ x <? maxColumn
  analyze fZ     | yes _ = First
  analyze (fS _) | yes _ = Middle
  analyze _      | no _  = Last

  show : Action -> String
  show Left = "L"
  show Ahead = "A"
  show Right = "R"
  
  admissible : {t : Nat} -> X t -> Action -> Set
  admissible x Ahead = (column x ≡ Z) ‌⊎ (column x ≡ maxColumn)
  admissible x Left  = column x ≤ maxColumnO2
  admissible x Right = column x ≥ maxColumnO2 
{-
x  \  y        Ahead     Left    Right
First            X         X
Middle early               X            
Middle late                X       X    -- Note the choice of Left or Right here
Last             X                 X
-}  

  Y : (t : Nat) -> X t -> Type
  Y t x = Σ Action (admissible {t} x)

  alwaysAdmissible : {t : Nat} -> (x : X t) -> Y t x -- Σ Action (admissible x)
  alwaysAdmissible fZ           = (Ahead  , inj₁ refl    )
  alwaysAdmissible (fS fZ)      = (Left   , s≤s z≤n      )
  alwaysAdmissible (fS (fS _))  = (Right  , s≤s (s≤s z≤n))

  lower : ∀ {m} → (x : Fin (S m)) -> (toℕ x < m) → Fin m 
  lower fZ     (s≤s p) = fZ
  lower (fS x) (s≤s p) = fS (lower x p)

--  lower : ∀ {m} n → (x : Fin (n + m)) -> (toℕ x < m) → Fin m 
--  lower = {!!}  TODO

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
  step t x (Left  , _) = decColWrap x
  step t x (Ahead , _) = x
  step t x (Right , _) = incColWrap x

  reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Nat
  reward t x y x' with analyze x'
  ... | First   = 1
  ... | Middle  = 0
  ... | Last    = 2

-- --------------------------------------------------------------
  -- TODO: remember to explain specialisation of the general
  -- (parameterised) ContextType to the case for Nat (here) or Float or
  -- ...

  ex1Context : Context.ContextType
  ex1Context = record { X = X; Y = Y; step = step }

  viable : {t : Nat} -> (n : Nat) -> X t -> Set
  viable {t} n x = viableDefault {t} n x
    where open Context.Defaults ex1Context

  -- Every state is viable
  viability : {t : Nat} -> (n : Nat) -> (x : X t) -> viable {t} n x
  viability {t} Z      x = oh
  viability {t} (S n)  x = (x'  , (( y , refl ) , viability {S t} n x' ))
    where  y : Y t x
           y = alwaysAdmissible {t} x
           x' : X (S t)
           x' = step t x y
{-
-}

  reachable : {t : Nat} -> X t -> Set
  reachable {t} x = reachableDefault {t} x
    where open Context.Defaults ex1Context

  open Context.RewType ex1Rew
  viableStepex1 : {t : Nat} -> (n : Nat) -> X t -> Set
  viableStepex1 {t} n x = Σ (Y t x) (\y -> viable {S t} n (step t x y))

  -- TODO: Move these out to generic library
  module Utils where
    List : Set -> Set
    List A = Σ Nat (Vec A)

    Any : {A : Set} (P : A -> Set) -> List A -> Set
    Any {A} P (n , v) = Σ (Fin n) (\i -> P (lookup i v))

    NonEmpty : Set -> Set
    NonEmpty A = Σ Nat (\n -> Vec A (S n))

    mapNonEmpty : {A B : Set} -> (A -> B) -> NonEmpty A -> NonEmpty B
    mapNonEmpty f (m , v) = (m , Data.Vec.map f v)       

    AnyN : {A : Set} -> (P : A -> Set) -> NonEmpty A -> Set
    AnyN P (n , v) = Σ (Fin (S n)) (\i -> P (lookup i v))

    filterTagP : {A : Set} ->
                 (p  : A -> Set) -> 
                 (as : NonEmpty A) -> 
                 AnyN p as ->
                 NonEmpty (Σ A p)
    filterTagP p (.0 , x ∷ []) (fZ , pHolds) = (0 , ((x , pHolds) ∷ []))
    filterTagP p (.0 , x ∷ []) (fS () , q)   -- cannot happen
    filterTagP p ((S n) , x1 ∷ x2 ∷ v) anyN = {!!}
{-
    filterTagP p (a :: (a' :: as)) q = 
      if (p a) 
      then (_ ** ((a ** believe_me (p a)) 
                  :: 
                  map 
                  (\ a'' => (a'' ** believe_me (p a''))) 
                  (getProof (filter p (a' :: as)))
                 )
           )
      else filterTagP p (a' :: as) (believe_me oh)
-}
  open Utils

  viableSpec1ex1 :  {t : Nat} -> {n : Nat} -> 
                    (x : X t) -> viable (S n) x -> viableStepex1 n x
  viableSpec1ex1 {t} {n} x v = {!!}

{-
The idea:

viable (S n) x
  = { def. }
isAnyBy (viable n) (succs x)  
  => { lemma6 }
(x' : X (S t) ** x' `isIn` (succs x) && viable n x')
  => { succsSpec2 }
(y : Y t x ** x' = step t x y)
  => { viable n x' }
(y : Y t x ** viable n (step t x y))

> ReachabilityViability.viableSpec1 {t} {n} x v = s11 where
>   s1 : so (isAnyBy (viable n) (succs x))
>   s1 = v
>   s2 : (xx : X (S t) ** 
>         (so (viable n xx), 
>          so (xx `isIn` succs x)
>         )
>        )
>   s2 = lemma6 (viable {t = S t} n) (succs x) s1
>   s3 : X (S t)
>   s3 = outl s2
>   s4 : so (s3 `isIn` (succs x))
>   s4 = snd (outr s2)
>   s5 : (yy : Y t x ** s3 = step t x yy)
>   s5 = succsSpec2 x s3 s4
>   s6 : Y t x
>   s6 = outl s5
>   s7 : so (viable n s3)
>   s7 = fst (outr s2)
>   s8 : s3 = step t x s6
>   s8 = outr s5
>   s9 : so (viable {t = S t} n (step t x s6))
>   s9 = leibniz (\ xSt => so (viable {t = S t} n xSt)) s8 s7
>   s11 : (yy : Y t x ** so (viable {t = S t} n (step t x yy)))
>   s11 = (s6 ** s9)

-}

  allCommands : Vec Action 3
  allCommands = Left ∷ Right ∷ Ahead ∷ []

  allCommandsNE : NonEmpty Action
  allCommandsNE = ( 2 ,  allCommands)

  findAllCommands : (a : Action) -> Σ (Fin 3) (\i -> a ≡ lookup i allCommands)
  findAllCommands Left  = ( fZ          , refl )
  findAllCommands Right = ( fS fZ       , refl )
  findAllCommands Ahead = ( fS (fS fZ)  , refl )

  admissiblesP : {t : Nat} -> 
                 (n : Nat) ->
                 (x : X t) -> 
                 (v : viable {t} (S n) x) -> 
                 NonEmpty (Y t x)
  admissiblesP {t} n x v = filterTagP (admissible x) allCommandsNE oneIsAdmissible
    where  isFeasible : viableStepex1 {t} n x -- Σ (Y t x) (\y -> viable n (step t x y))
           isFeasible = viableSpec1ex1 {t} x v 
           a : Action
           a = fst (fst isFeasible)
           p : admissible x a
           p = snd (fst isFeasible)
           isIn : Σ (Fin 3) (\i -> a ≡ lookup i allCommands)
           isIn = findAllCommands a
           oneIsAdmissible : AnyN (admissible x) allCommandsNE
                -- Σ (Fin 3) (λ i → admissible x (lookup i allCommands))
           oneIsAdmissible = (fst isIn , p)

  -- Computes a vector of pairs of "viable" controls and corresponding values of f
  yfysP : {t : Nat} -> 
          (n : Nat) ->
          (x : X t) -> 
          (v : viable {t} (S n) x) -> -- Ensures that the result vector is non-empty
          (f :      viableStepex1 {t} n x  -> Nat) -> 
          NonEmpty (viableStepex1 {t} n x  ×  Nat)
  yfysP {t} n x v f = mapNonEmpty (pairId f) ysP
    where ys : NonEmpty (Y t x)
          ys = {!admissiblesP x v!}
          p : Y t x -> Set
          p y = viable {S t} n (step t x y)
          s4 : {!!}
          s4 = {!!}
          ysP : NonEmpty (Σ (Y t x) p)
                     -- (viableStepex1 {t} n x)
          ysP = filterTagP p ys s4
{--}
  -- Compute a list of all possible commands
  -- filter out only the "viableStep" commands
  -- apply f to compute the second components of the pair

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
             MaxF (viableStepex1 n x)

  MaxVStep n x r v = 
    record { max = {!\ f -> ex1max n x r v f!}; 
             argmax = {!!}; 
             maxSpec = {!!}; 
             argmaxSpec = {!!} }


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
