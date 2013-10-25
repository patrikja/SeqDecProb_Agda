open import Prelude
open import Context
module OptimalControls (Rew : RewProp) (ctxt : Context Rew) where
open RewProp Rew
open Context.Context ctxt

-- This could come in handy: the subset of X t which is viable for n steps
XV : (t : Nat) -> (n : Nat) -> Set
XV t n = Σ (X t) (\x -> viable n x)

{-
data CtrlSeq {t : Nat} (x : X t) : 
             (n : Nat) -> viable n x -> Type where
  Nil  : (v : viable Z x) -> CtrlSeq x Z v
  _::_ : {n : Nat} -> (yv : viableStep n x) -> let (y , v) = yv in
         CtrlSeq  (step t x y)  n      v ->
         CtrlSeq  x             (S n)  (viableSpec2 x yv)
-}

-- CtrlSeq x n is a control path from x of length n
data CtrlSeq {t : Nat} (x : X t) : 
             (n : Nat) -> Type where
  Nil  : CtrlSeq x Z
  _::_ : {n : Nat} -> (yv : viableStep n x) -> let (y , v) = yv in
         CtrlSeq  (step t x y)  n      ->
         CtrlSeq  x             (S n)

viableLemma : {t : Nat} (x : X t) -> (n : Nat) -> CtrlSeq x n -> viable n x
viableLemma x ._ Nil         = viableSpec0 x
viableLemma x ._ (yv :: cs)  = Context.viableSpec2 ctxt x yv

val : {t : Nat} ->
      (x : X t) -> (n : Nat) -> 
      CtrlSeq x n -> carrier
val x ._ (Nil)              = 0F
val {t} x ._ (_::_ {n} (y , v') yvs)  =
  let   x' : X (S t) 
        x' = step t x y
  in   reward t x y x'  +F  val x' n yvs 


OptCtrlSeq : {t : Nat} ->
             (x : X t) -> (n : Nat) ->
             CtrlSeq x n -> Type
OptCtrlSeq x n ys = ∀ ys' ->  val x n ys' <=F val x n ys

-- Sanity check:
nilIsOptCtrlSeq : {t : Nat} -> (x : X t) -> OptCtrlSeq x Z  Nil
nilIsOptCtrlSeq x Nil = reflexive<=F 0F
