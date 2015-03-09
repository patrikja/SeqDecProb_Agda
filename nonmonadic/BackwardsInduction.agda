open import Prelude
open import Context
module BackwardsInduction (Reward : RewardType) where
open RewardType Reward
open import OptimalPolicies Reward
import Relation.Binary.PreorderReasoning

OptExtension : (t : Nat) -> (n : Nat) -> 
               PolicySeq (S t) n -> Policy t (S n) -> Type
OptExtension t n ps p = 
  (p' : Policy t (S n)) ->
  (x : X t) ->
  (r : reachable x) -> 
  (v : viable (S n) x) -> 
    (Val x (S n) r v (p' :: ps)) <=F 
    (Val x (S n) r v (p  :: ps))

optExtension : (t : Nat) -> (n : Nat) -> 
               PolicySeq (S t) n -> Policy t (S n)
 -- (x : X t) -> (r : reachable x) -> (v : viable (S n) x) -> viableStep n x
optExtension t n ps = \ x r v -> argmax n x r v (ValY t n x r ps) 

OptExtensionLemma : 
  (t : Nat) -> (n : Nat) -> 
  (ps : PolicySeq (S t) n) -> OptExtension t n ps (optExtension t n ps)
OptExtensionLemma t n ps   p' x r v = 
  let opE = \ x r v -> argmax n x r v (ValY t n x r ps)
      yv : viableStep n x   
      yv = p' x r v         
  in 
  begin
    Val x (S n) r v (p' :: ps)
  ∼⟨ reflexive<=F _ ⟩
    ValY t n x r ps yv
-- Informally: f = ValY t n x r ps
--             o = opE x r v = argmax' f
-- By maxSpec' the order follows
  ∼⟨ maxSpec' n x r v (ValY t n x r ps) yv ⟩
    ValY t n x r ps (opE x r v)
  ∼⟨ reflexive<=F _ ⟩
    Val x (S n) r v (opE :: ps)
  ∼⟨ reflexive<=F _ ⟩
    Val x (S n) r v (optExtension t n ps :: ps)
  ∎ 
  where open Relation.Binary.PreorderReasoning Preorder

Bellman : (t : Nat) -> (n : Nat) ->
          (ps : PolicySeq (S t) n) ->  OptPolicySeq (S t) n ps ->
          (p : Policy t (S n)) ->      OptExtension t n ps p ->
          OptPolicySeq t (S n) (p :: ps)
Bellman t n ps ops p oep (p' :: ps') x r v =
  begin
    Val x (S n) r v (p' :: ps') 
  ∼⟨ reflexive<=F _ ⟩
    let yv : viableStep n x
        yv = p' x r v
        (y , v') = yv
        x' = step t x y
        r' = reachableSpec1 x r y
    in reward t x y x'  +F  Val x' n r' v' ps'
  ∼⟨ monoF (ops ps' x' r' v') ⟩
    reward t x y x'     +F  Val x' n r' v' ps
  ∼⟨ reflexive<=F _ ⟩
    Val x (S n) r v (p' :: ps)
  ∼⟨ oep p' x r v ⟩
    Val x (S n) r v (p  :: ps)
  ∎
  where open Relation.Binary.PreorderReasoning Preorder


backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
backwardsInduction _ Z = Nil
backwardsInduction t (S n) = (optExtension t n ps) :: ps where
  ps : PolicySeq (S t) n
  ps = backwardsInduction (S t) n

BackwardsInductionLemma : (t : Nat) -> (n : Nat) -> 
                          OptPolicySeq t n (backwardsInduction t n)
BackwardsInductionLemma _ Z = nilIsOptPolicySeq
BackwardsInductionLemma t (S n) = 
  Bellman t n ps psIsOptPolicySeq p pIsOptExtension where
    ps : PolicySeq (S t) n
    ps = backwardsInduction (S t) n
    psIsOptPolicySeq : OptPolicySeq (S t) n ps
    psIsOptPolicySeq = BackwardsInductionLemma (S t) n
    p : Policy t (S n)
    p = optExtension t n ps
    pIsOptExtension : OptExtension t n ps p
    pIsOptExtension = OptExtensionLemma t n ps
