module Prelude where
import Data.Nat 
open import Data.Unit public using (⊤; tt)
open import Data.Product public renaming (proj₁ to fst; proj₂ to snd) 
open import Relation.Binary.PropositionalEquality public -- using (_≡_; refl; ≡-Reasoning)
open import Data.Bool public using (Bool; true; false; if_then_else_)
open import Data.Bool using (T)
so = T
oh : so true
oh = tt

open Data.Nat public renaming (ℕ to Nat; suc to S; zero to Z) 
-- open Data.Nat public 

Type = Set


