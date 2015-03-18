module SigmaProperties where
-- import Data.Fin
-- import Data.Vect
open import Control.Isomorphism
-- 
-- 
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

Type = Set

sigmaIsoLemma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) -> 
                 (isoA : Iso A A') -> 
                 (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
                 Iso (Sigma A B) (Sigma A' B')
sigmaIsoLemma = ?
