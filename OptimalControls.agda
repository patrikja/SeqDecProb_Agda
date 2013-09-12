open import Prelude
open import Context
module OptimalControls (Rew : RewProp) (ctxt : Context Rew) where
open RewProp Rew
open Context.Context ctxt

-- This could come in handy
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

data CtrlSeq {t : Nat} (x : X t) : 
             (n : Nat) -> viable n x -> Type where
  Nil  : (v : viable Z x) -> CtrlSeq x Z v
  _::_ : {n : Nat} -> (yv : viableStep n x) -> let (y , v) = yv in
         CtrlSeq  (step t x y)  n      v ->
         CtrlSeq  x             (S n)  (viableSpec2 x yv)

val : {t : Nat} ->
      (x : X t) -> (n : Nat) -> (v : viable n x) -> 
      CtrlSeq x n v -> carrier
val x ._ ._ (Nil v)              = 0F
val {t} x ._ ._ (_::_ {n} yv yvs)  =
  let   (y , v') = yv
        x' : X (S t) 
        x' = step t x y
  in   reward t x y x'  +F  val x' n v' yvs 


OptCtrlSeq : {t : Nat} ->
             (x : X t) -> (n : Nat) -> (v : viable n x) -> 
             CtrlSeq x n v -> Type
OptCtrlSeq x n v ys = (ys' : CtrlSeq x n v) -> 
                      val x n v ys' <=F val x n v ys

-- Sanity check:

nilIsOptCtrlSeq : {t : Nat} -> 
                  (x : X t) -> OptCtrlSeq x Z (viableSpec0 x) (Nil (viableSpec0 x))
nilIsOptCtrlSeq x (Nil ._) = reflexive<=F 0F
