module SigmaProperties where
-- import Data.Fin
-- import Data.Vect
open import Control.Isomorphism
open import Builtins
open import Syntax.PreorderReasoning
open import Prelude.Basics

-- import Decidable
-- import Finite
-- import Unique
-- import SigmaOperations
-- import VectOperations
-- import VectProperties
-- import FiniteOperations
-- import FiniteProperties
-- import FinOperations
-- import IsomorphismOperations
-- import IsomorphismProperties
-- import Basics
-- import LambdaPostulates

-- In agda-stdlib we would build this not on Iso but on Inverse (or
-- equivalently Bijection). They are in turn built on Setoids which is
-- more general but also more infrastructure than I'd like to import
-- right now. (I just want to check that the type makes sense and get
-- some hints as to where the Idris development [1] is unnecessarily
-- clumsy.)
-- [1] https://github.com/nicolabotta/SeqDecProbs/blob/b672a327b55b62f19bf967138af975c754a01284/SigmaProperties.lidr

open Iso

sigmaIsoLemma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) ->
                 (isoA : Iso A A') ->
                 (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
                 Iso (Sigma A B) (Sigma A' B')
sigmaIsoLemma A A' B B' isoA isoBa = MkIso toQ fromQ toFromQ fromToQ
   where toQ      : Sigma A  B  -> Sigma A' B'
         toQ (MkSigma x pf) = MkSigma (to isoA x) (to (isoBa x) pf)

         fromQ    : Sigma A' B' -> Sigma A  B
         fromQ (MkSigma a' pf) = MkSigma a (from isoB B'a)
            where  a : A
                   a = from isoA a'
                   isoB : Iso (B a) (B' (to isoA a))
                   isoB = isoBa a
                   B'a : B' (to isoA a)
                   B'a = subst B' (sym (toFrom isoA a')) pf

         toFromQ  : (ab' : Sigma A' B') -> toQ (fromQ ab') == ab'
         toFromQ = {!!}
--          toFromQ  (a' ** b') = trans s1 (trans s2 s3) where
--            s1 : toQ (fromQ (a' ** b'))
--                 =
--                 toQ (from isoA a' ** from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
--            s1 = Refl
--            s2 : toQ (from isoA a' ** from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
--                 =
--                 (to isoA (from isoA a')
--                  **
--                  to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
--                 )
--            s2 = Refl
--            s3 : (to isoA (from isoA a')
--                  **
--                  to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
--                 )
--                 =
--                 (a' ** b')
--            s3 = sigmaEqLemma2 {s1 = (to isoA (from isoA a')
--                                      **
--                                      to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
--                                     )}
--                               {s2 = (a' ** b')}
--                               (toFrom isoA a')
--                               (isoReplaceLemma1 isoA isoBa a' b')

         fromToQ : (ab  : Sigma A  B) -> fromQ (toQ ab) == ab
         fromToQ = {!!}
--          fromToQ (a ** b) = trans s1 (trans s2 s3) where
--            s1 : fromQ (toQ (a ** b))
--                 =
--                 fromQ (to isoA a ** to (isoBa a) b)
--            s1 = Refl
--            s2 : fromQ (to isoA a ** to (isoBa a) b)
--                 =
--                 (from isoA (to isoA a)
--                  **
--                  from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))
--            s2 = Refl
--            s3 : (from isoA (to isoA a)
--                  **
--                  from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))
--                 =
--                 (a ** b)
--            s3 = sigmaEqLemma2 {s1 = (from isoA (to isoA a)
--                                      **
--                                      from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b))
--                                     )}
--                               {s2 = (a ** b)}
--                               (fromTo isoA a)
--                               (isoReplaceLemma2 isoA isoBa a b)
