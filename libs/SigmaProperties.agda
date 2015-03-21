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

{-
sigmaEqA : (A   : Type) ->
           (a : A) -> (a' : A) -> (a == a') ->
           (B   : A → Type) ->
           (b   : B a) -> (b'  : B a') -> (eqb : b == b') ->
           MkSigma {A} {B} a b == MkSigma {A} {B} a' b'
sigmaEqA A a .a Refl B b .b Refl = Refl

sigmaEqB : (A   : Type) -> (a : A) ->
            (B   : A → Type) ->
            (b   : B a) ->
            (b'  : B a) ->
            (eqb : b == b') ->
            MkSigma {A} {B} a b == MkSigma {A} {B} a b'
sigmaEqB A a B b .b Refl = Refl


sigmaEq :  (A : Type) -> (A' : Type) ->
           (a : A) -> (a' : A') -> (eqa : a == a') ->
           -- In the implementation we know that A == A' from here on
           (B : A -> Type) -> (B' : A' -> Type) ->
           (b : B a) -> (b' : B' a') -> (eqb : b == b') ->
           MkSigma {A} {B} a b == MkSigma {A'} {B'} a' b'
sigmaEq A .A a .a Refl B B' b b' eqb = {!!}
-}

sigmaEqLemma2 : {A  : Type} ->
                {P  : A -> Type} ->
                {s1 : Sigma A P} ->
                {s2 : Sigma A P} ->
                Sigma.x s1 == Sigma.x s2 ->
                Sigma.pf s1 == Sigma.pf s2 ->
                s1 == s2
sigmaEqLemma2 {s1 = MkSigma x pf} {MkSigma .x .pf} Refl Refl = Refl

sigmaIsoLemma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) ->
                 (isoA : Iso A A') ->
                 (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
                 Iso (Sigma A B) (Sigma A' B')
sigmaIsoLemma A A' B B' isoA isoBa = MkIso toQ fromQ toFromQ fromToQ
   where toQ      : Sigma A  B  -> Sigma A' B'
         toQ (MkSigma a b) = MkSigma (to isoA a) (to (isoBa a) b)

         fromQ    : Sigma A' B' -> Sigma A  B
         fromQ (MkSigma a' b') = MkSigma a (from isoB B'a)
            where  a : A
                   a = from isoA a'
                   isoB : Iso (B a) (B' (to isoA a))
                   isoB = isoBa a
                   B'a : B' (to isoA a)
                   B'a = subst B' (sym (toFrom isoA a')) b'

         toFromQ  : (ab' : Sigma A' B') -> toQ (fromQ ab') == ab'
         toFromQ (MkSigma a' b') = toQ (fromQ (MkSigma a' b'))  ==< Refl >==
                                   toQ (MkSigma a (fromB B'a))  ==< Refl >==
                                   MkSigma (toA (fromA a'))
                                           (toB (fromB B'a))    ==< sigmaEqLemma2 (toFrom isoA a') toFromb' >==
                                   MkSigma a' b'                QED
                    -- sigmaEqA A' (toA a) a' (toFrom isoA a') B' {!!} b' {!!}
           where   toA    = to    isoA
                   fromA  = from  isoA
                   a : A
                   a = fromA a'
                   isoB : Iso (B a) (B' (toA a))
                   isoB = isoBa a
                   toB    = to    isoB
                   fromB  = from  isoB
                   toFroma' : toA (fromA a') == a'
                   toFroma' = toFrom isoA a'
                   B'a : B' (toA a)
                   B'a = subst B' (sym toFroma') b'
                   toFromb' : toB (fromB B'a) == b'
                   toFromb' = {!!}
--          toFromQ  (a' ** b') = trans s1 (trans s2 s3) where
--            s1 : toQ (fromQ (a' ** b'))
--                 =
--                 toQ (fromA a' ** from (isoBa (fromA a')) (replace (sym (toFrom isoA a')) b'))
--            s1 = Refl
--            s2 : toQ (fromA a' ** from (isoBa (fromA a')) (replace (sym (toFrom isoA a')) b'))
--                 =
--                 (toA (fromA a')
--                  **
--                  to (isoBa (fromA a')) (from (isoBa (fromA a')) (replace (sym (toFrom isoA a')) b'))
--                 )
--            s2 = Refl
--            s3 : (toA (fromA a')
--                  **
--                  to (isoBa (fromA a')) (from (isoBa (fromA a')) (replace (sym (toFrom isoA a')) b'))
--                 )
--                 =
--                 (a' ** b')
--            s3 = sigmaEqLemma2 {s1 = (toA (fromA a')
--                                      **
--                                      to (isoBa (fromA a')) (from (isoBa (fromA a')) (replace (sym (toFrom isoA a')) b'))
--                                     )}
--                               {s2 = (a' ** b')}
--                               (toFrom isoA a')
--                               (isoReplaceLemma1 isoA isoBa a' b')

         fromToQ : (ab  : Sigma A  B) -> fromQ (toQ ab) == ab
         fromToQ = {!!}
--          fromToQ (a ** b) = trans s1 (trans s2 s3) where
--            s1 : fromQ (toQ (a ** b))
--                 =
--                 fromQ (toA a ** to (isoBa a) b)
--            s1 = Refl
--            s2 : fromQ (toA a ** to (isoBa a) b)
--                 =
--                 (fromA (toA a)
--                  **
--                  from (isoBa (fromA (toA a))) (replace (sym (toFrom isoA (toA a))) (to (isoBa a) b)))
--            s2 = Refl
--            s3 : (fromA (toA a)
--                  **
--                  from (isoBa (fromA (toA a))) (replace (sym (toFrom isoA (toA a))) (to (isoBa a) b)))
--                 =
--                 (a ** b)
--            s3 = sigmaEqLemma2 {s1 = (fromA (toA a)
--                                      **
--                                      from (isoBa (fromA (toA a))) (replace (sym (toFrom isoA (toA a))) (to (isoBa a) b))
--                                     )}
--                               {s2 = (a ** b)}
--                               (fromTo isoA a)
--                               (isoReplaceLemma2 isoA isoBa a b)
