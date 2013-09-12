open import Prelude
open import Context
module OptimalPolicies (Rew : RewProp) (ctxt : Context Rew) where
open RewProp Rew
open Context.Context ctxt
open import OptimalControls Rew ctxt renaming (Nil to NilC; _::_ to _::C_)

-- Policy t n is a function from X such Ys that can be used for n steps
Policy : Nat -> Nat -> Type
Policy t Z     = ⊤    -- You can aways take zero steps
Policy t (S n) = (x : X t) -> 
                 (r : reachable x) -> 
                 (v : viable (S n) x) -> 
                 Σ (Y t x) (\y -> viable n (step t x y))


data PolicySeq : Nat -> Nat -> Type where
  Nil  : {t : Nat } -> PolicySeq t Z
  _::_ : {t : Nat } -> {n : Nat } -> 
         Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

ctrls : {t : Nat} -> 
       (x : X t) ->
       (n : Nat) -> 
       (r : reachable x) -> 
       (v : viable n x) -> 
       PolicySeq t n -> 
       CtrlSeq x n v
ctrls {t} x ._ r v Nil        = NilC v   
  -- Had:    NilC : CtrlSeq x Z (viableSpec0 x)
  -- Needed:        CtrlSeq x Z v
  -- but v may be some other value of that type (we have not required it to be a singleton set)

ctrls x ._ r v (p :: ps)  = {!!} -- ? ::C (ctrls ? ? ? ? ps)

{-

> ctrl {t} x _ _ (viableSpec0 x) Nil = Nil

> ctrl {t} x (S n) r v (p :: ps) =
>  leibniz {P = \ via => CtrlSeq x (S n) via} v'' (yv :: ctrl {t = S t} x' n r' v' ps) where
>   yv : (y : Y t x ** so (viable {t = S t} n (step t x y)))
>   yv = p x r v
>   x' : X (S t)
>   x' = step t x (outl yv)
>   r' : so (reachable {t = S t} x')
>   r' = reachableSpec1 x r (outl yv)
>   v' : so (viable {t = S t} n x')
>   v' = outr yv
>   v'' : viableSpec2 x yv = v
>   v'' = believe_me oh

...

> Val : (t : Nat) ->
>       (n : Nat) ->
>       (x : X t) -> 
>       (r : so (reachable x)) -> 
>       (v : so (viable n x)) -> 
>       PolicySeq t n -> 
>       Float
> Val _ Z _ _ _ _ = 0
> Val t (S n) x r v (p :: ps) = reward t x y x' + Val (S t) n x' r' v' ps where
>   y : Y t x
>   y = outl (p x r v)
>   x' : X (S t) 
>   x' = step t x y
>   r' : so (reachable {t = S t} x')
>   r' = reachableSpec1 x r y
>   v' : so (viable {t = S t} n x')
>   v' = outr(p x r v)

The notion of optimal sequence of policies

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
>                       (x : X t) ->
>                       (r : so (reachable x)) -> 
>                       (v : so (viable n x)) -> 
>                       so (Val t n x r v ps' <= Val t n x r v ps)

(Sanity check: Nil is optimal policy sequence                             

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ _ _ = reflexive_Float_lte 0

) is interesting because of the following lemma

> OptLemma :   (n : Nat) -> 
>              (ps : PolicySeq t n) ->                                                                   
>              OptPolicySeq t n ps ->
>              (x : X t) ->
>              (r : so (reachable x)) -> 
>              (v : so (viable n x)) -> 
>              OptCtrlSeq x n v (ctrl x n r v ps)
                                                                                        
> OptLemma Z Nil _ x r (viableSpec0 x) = oneIsOptCtrlSeq x

> OptLemma (S n) (p :: ps) opt_pps x rx vx = believe_me oh

-}
