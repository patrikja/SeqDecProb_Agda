open import Prelude
open import Context
module OptimalPolicies (Rew : RewProp) (ctxt : Context Rew) where
open RewProp Rew
open Context.Context ctxt
open import OptimalControls Rew ctxt renaming (Nil to NilC; _::_ to _::C_)

-- Policy t n is a function from X that generates a "viable" y
Policy : Nat -> Nat -> Type
Policy t Z     = ⊤    -- You can aways take zero steps
Policy t (S n) = (x : X t) -> 
                 (r : reachable x) -> 
                 (v : viable (S n) x) -> 
  -- Could be problematic - (S n) on the LHS is not obviously the same as 
  --   (S n) on the RHS
                 viableStep n x
                 --Σ (Y t x) (\y -> viable n (step t x y))

-- PolicySeq t n is a sequence of policies for n steps from t
data PolicySeq : Nat -> Nat -> Type where
  Nil  : {t : Nat } -> PolicySeq t Z
  _::_ : {t : Nat } -> {n : Nat } -> 
         Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

ctrls :  {t  : Nat} -> 
         (x  : X t) ->
         (n  : Nat) -> 
         (r  : reachable x) -> 
         (v  : viable n x) -> 
         PolicySeq t n -> 
         CtrlSeq x n
ctrls x ._ r _ Nil        = NilC
ctrls x ._ r v (_::_ {t} {n} p ps)  = 
  let yv : viableStep n x
      yv = p x r v
      (y , v') = yv
      x' = step t x y
      r' = reachableSpec1 x r y
      cs : CtrlSeq x' n
      cs = ctrls x' n r' v' ps
  in yv ::C cs


-- TODO: Perhaps introduce a name for the step case in Val

mutual 
  Val : {t : Nat} ->
        (x : X t) -> 
        (n : Nat) ->
        (r : reachable x) -> 
        (v : viable n x) -> 
        PolicySeq t n -> 
        carrier
  Val {t} x .0 r v Nil = 0F
  Val {t} x .(S n) r v (_::_ {.t} {n} p ps) = 
    let yv : viableStep n x
        yv = p x r v
    in ValY t n x r ps yv

  ValY : (t : Nat) -> (n : Nat) -> 
         (x : X t) (r : reachable x) -> 
         (ps : PolicySeq (S t) n) -> 
         viableStep n x -> carrier
  ValY t n x r ps = \yv' -> 
    let (y , v') = yv'              
        x' = step t x y                     
        r' = reachableSpec1 x r y   
    in reward t x y x'  +F  Val x' n r' v' ps       

{-
Val : {t : Nat} ->
      (x : X t) -> 
      (n : Nat) ->
      (r : reachable x) -> 
      (v : viable n x) -> 
      PolicySeq t n -> 
      carrier
Val {t} x .0 r v Nil = 0F
Val {t} x .(S n) r v (_::_ {.t} {n} p ps) = 
  let yv : viableStep n x
      yv = p x r v
      (y , v') = yv
      x' = step t x y 
  in reward t x y x'  +F  Val x' n (reachableSpec1 x r y) v' ps

ValY : (t : Nat) -> (n : Nat) -> 
       (x : X t) (r : reachable x) -> 
       (ps : PolicySeq (S t) n) -> 
       viableStep n x -> carrier
ValY t n x r ps = \yv' -> 
  let (y , v') = yv'                              
      x' = step t x y                             
      r' = reachableSpec1 x r y                   
  in reward t x y x'  +F  Val x' n r' v' ps       
-}

OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
                      (x : X t) ->
                      (r : reachable x) -> 
                      (v : viable n x) -> 
                      (Val x n r v ps') <=F (Val x n r v ps)

nilIsOptPolicySeq : {t : Nat} -> OptPolicySeq t Z Nil
nilIsOptPolicySeq Nil x r v = reflexive<=F 0F

{-

OptLemma :   {t : Nat} ->
             (n : Nat) ->
             (ps : PolicySeq t n) ->
             OptPolicySeq t n ps ->
             (x : X t) ->
             (r : reachable x) ->
             (v : viable n x) ->
             OptCtrlSeq x n (ctrls x n r v ps)
OptLemma .0 Nil x x₁ r v NilC = reflexive<=F 0F
OptLemma {t} .(S n) (_::_ {.t} {n} x ps) x₁ x₂ r v ys' = {!!}  
  -- TODO based on the time-independent case

-}
