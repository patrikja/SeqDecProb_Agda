module SigmaProperties where
-- import Idris.Data.Fin
-- import Idris.Data.Vect
open import Idris.Control.Isomorphism
open import Idris.Builtins
open import Idris.Syntax.PreorderReasoning
open import Idris.Prelude.Basics

-- import Idris.Decidable
-- import Idris.Finite
-- import Idris.Unique
-- import Idris.SigmaOperations
-- import Idris.VectOperations
-- import Idris.VectProperties
-- import Idris.FiniteOperations
-- import Idris.FiniteProperties
-- import Idris.FinOperations
-- import IsomorphismOperations
-- import IsomorphismProperties
-- import Idris.Basics
-- import Idris.LambdaPostulates

-- In agda-stdlib we would build this not on Iso but on Inverse (or
-- equivalently Bijection). They are in turn built on Setoids which is
-- more general but also more infrastructure than I'd like to import
-- right now. (I just want to check that the type makes sense and get
-- some hints as to where the Idris development [1] is unnecessarily
-- clumsy.)
-- [1] https://github.com/nicolabotta/SeqDecProbs/blob/b672a327b55b62f19bf967138af975c754a01284/SigmaProperties.lidr

open Iso

sigmaEqLemma2 : {A : Type} -> {P : A -> Type} ->
                {s1 : Sigma A P} -> {s2 : Sigma A P} ->
                Sigma.getWitness  s1  ==  Sigma.getWitness  s2 ->
                Sigma.getProof s1  ==  Sigma.getProof s2 ->
                s1 == s2
sigmaEqLemma2 {s1 = MkSigma a b} {MkSigma .a .b} Refl Refl = Refl

sigmaIsoLemma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) ->
                 (isoA : Iso A A') ->
                 (isoB : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
                 Iso (Sigma A B) (Sigma A' B')
sigmaIsoLemma A A' B B' isoA isoB = MkIso toAB fromAB toFromAB fromToAB
   where toA    = to    isoA
         fromA  = from  isoA
         toB    = \a -> to   (isoB a)
         fromB  = \a -> from (isoB a)

         toAB      : Sigma A  B  -> Sigma A' B'
         toAB (MkSigma a b) = MkSigma (toA a) (toB a b)

         fromAB    : Sigma A' B' -> Sigma A  B
         fromAB (MkSigma a' b') = MkSigma a (fromB a b'')
            where  a : A
                   a = fromA a'
                   isoBa : Iso (B a) (B' (toA a))
                   isoBa = isoB a
                   b'' : B' (toA a)
                   b'' = subst B' (sym (toFrom isoA a')) b'

         toFromAB  : (ab' : Sigma A' B') -> toAB (fromAB ab') == ab'
         toFromAB (MkSigma a' b') = sigmaEqLemma2 (toFrom isoA a') toFromb'
{-
         toFromAB (MkSigma a' b') = toAB (fromAB (MkSigma a' b'))  ==< Refl >==
                                    toAB (MkSigma a (fromBa b''))  ==< Refl >==
                                    MkSigma (toA (fromA a'))
                                            (toBa (fromBa b''))    ==< sigmaEqLemma2 (toFrom isoA a') toFromb' >==
                                    MkSigma a' b'                QED
-}
           where   a : A
                   a = fromA a'
                   isoBa : Iso (B a) (B' (toA a))
                   isoBa = isoB a
                   toBa    = to    isoBa
                   fromBa  = from  isoBa
                   toFroma' : toA (fromA a') == a'
                   toFroma' = toFrom isoA a'
                   b'' : B' (toA a)
                   b'' = subst B' (sym toFroma') b'
                   toFromb' : toBa (fromBa b'') == b'
                   toFromb' = (toBa (fromBa (subst B' (sym toFroma') b')))
                                ==< toFrom isoBa (subst B' (sym toFroma') b') >==
                              (subst B' (sym toFroma') b')
                                ==< substEq B' (sym toFroma') b' >==
                              b' QED

         fromToAB : (ab  : Sigma A  B) -> fromAB (toAB ab) == ab
         fromToAB (MkSigma a b) = sigmaEqLemma2 (fromTo isoA a) lem
           where a' = toA a
                 b' = toB a b
                 a'' = fromA a'
                 eqa : a'' == a
                 eqa = fromTo isoA a
                 b''    : B' (toA a'')
                 b''    = subst   B' (sym (toFrom isoA a')) b'
                 eqb''  : b'' == b'
                 eqb''  = substEq B' (sym (toFrom isoA a')) b'
                 lem = Sigma.getProof (fromAB (toAB (MkSigma a b)))
                         ==< Refl >==
                       Sigma.getProof (fromAB (MkSigma (toA a) (toB a b)))
                         ==< Refl >==
                       Sigma.getProof (MkSigma {A} {B} a'' (fromB a'' b'') )
                         ==< Refl >==
                       fromB a'' b''
                         ==< cong2' fromB eqa eqb'' >==
                       fromB a b'
                         ==< Refl >==
                       fromB a (toB a b)
                         ==< fromTo (isoB a) b >==
                       b QED
