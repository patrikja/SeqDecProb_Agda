module Idris.Decidable.Decidable where

-- import Data.Rel
-- import Data.Fun

--------------------------------------------------------------------------------
-- Typeclass for decidable n-ary Relations
--------------------------------------------------------------------------------
{-
--  Note: Instance resolution for Decidable is likely to not work in the REPL
--        at the moment.
class Decidable (ts : Vect k Type) (p : Rel ts) where
  total decide : liftRel ts p Dec

-- 'No such variable {k506}'
--decision : Decidable ts p => (ts : Vect k Type) -> (p : Rel ts) -> liftRel ts p Dec
--decision ts p = decide {ts} {p}

using (a : Type, x : a)
  data Given : Dec a -> Type where
    Always : Given (Yes x)
-}
