module Blt where
open import Prelude
open import Data.Fin
-- import Nat.Postulates
-- import Exists.Ops
-- import Logic.Properties

Blt : Nat -> Type
Blt = Fin
-- Blt b = Σ Nat (\ n -> n < b)

{-

> BltLemma0 : Blt Z -> alpha
> BltLemma0 (Z ** p)    =  soFalseElim p 
> BltLemma0 (S n ** p)  =  soFalseElim p 

> toNat : Blt b -> Nat
> toNat = outl

> toFloat : Blt b -> Float
> toFloat = cast . (cast . (cast . Blt.toNat))

-- > (==) : Blt b -> Blt b -> Bool
-- > (==) i j = (toNat i == toNat j)

> using (p : Nat -> Type)
>   instance Show (n : Nat ** p n) where
>     show (n ** _) = show n

> using (p : Nat -> Type)
>   instance Eq (n : Nat ** p n) where
>     (==) (n ** _) (n' ** _) = n == n'

-- > instance Eq (Blt 11) where
-- >   (==) (i ** _) (j ** _) = i == j

> -- partial
> -- decBlt : Blt b -> Blt b
> -- decBlt (S k ** q) = (k ** Sid_preserves_LT q)

> -- decBlt : (i : Blt b) -> {p : Blt.toNat i = S m} -> Blt b
> -- decBlt (S k ** q) = (k ** Sid_preserves_LT q)
> -- decBlt (  Z ** q) {p = refl} impossible

> decBlt : (i : Blt b) -> (p : Blt.toNat i = S m) -> Blt b
> decBlt (S k ** q) refl = (k ** Sid_preserves_LT q)
> decBlt (  Z ** q) refl impossible

> incBlt : (n : Blt b) -> so (S (Blt.toNat n) < b) -> Blt b
> incBlt (k ** _) q = (S k ** q)  

> toVect : {b : Nat} -> (Blt b -> a) -> Vect b a
> toVect {b = Z} _ = Nil
> toVect {b = S b'} {a = a} f = ((f (Z ** oh)) :: toVect f') where
>   f' : Blt b' -> a
>   f' (k ** q) = f (S k ** monotoneS q)  
  
-}
