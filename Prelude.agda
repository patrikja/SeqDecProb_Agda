module Prelude where
import Data.Nat 
open import Data.Unit public using (⊤)
open import Data.Product public
open import Relation.Binary.PropositionalEquality public -- using (_≡_; refl; ≡-Reasoning)


open Data.Nat public renaming (ℕ to Nat; suc to S; zero to Z) 
-- open Data.Nat public 

Type = Set


