# For Vectron! (by Matteo Acerbi https://github.com/ma82)

## Base definitions

### Imports

\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Fin
open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Σ renaming (proj₁ to fst ; proj₂ to snd ; curry to cu ; uncurry to uc)
open import Data.Sum as ⊎ renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Vec as V hiding (_∈_)
open import Function
import Level as L
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
\end{code}

### Booleans

\begin{code}
Bool = ⊤ ⊎ ⊤

pattern true  = inl tt
pattern false = inr tt
\end{code}

### Decidable sets and predicates

\begin{code}
Dec : ∀ {a} → Set a → Set _
Dec A = A ⊎ ¬ A

pattern yes p = inl p
pattern no  p = inr p

Dec/ : ∀ {a}{A : Set a}{p} → (A → Set p) → Set _
Dec/ P = ∀ a → Dec (P a)
\end{code}

### Paramorphism and catamorphism for vectors

\begin{code}
module _ {x y}{X : Set x}{Y : ℕ → Set y} where

  para : Y ℕ.zero → (∀ {n} → X → Vec X n → Y n → Y (ℕ.suc n)) → ∀ {n} → Vec X n → Y n
  para nil cons      []  = nil
  para nil cons (x ∷ xs) = cons x xs (para nil cons xs)

  cata : Y ℕ.zero → (∀ {n} → X → Y n → Y (ℕ.suc n)) → ∀ {n} → Vec X n → Y n
  cata nil cons = para nil (const ∘ cons)
\end{code}

## ■

`■ P xs` corresponds to the property that `P (y , ys)` holds on every
element `y` of vector `xs` and the tail `ys` which follows it.

\begin{code}
Pred∷ = λ {a}(A : Set a) l → ∀ {n} → A × Vec A n → Set l

data ■ {a p}{A : Set a}(P : Pred∷ A p) : ∀ {n} → Vec A n → Set (a L.⊔ p) where
  []  :                                               ■ P []
  _∷_ : ∀ {n x}{xs : Vec A n} → P (x , xs) → ■ P xs → ■ P (x ∷ xs)
\end{code}

\begin{code}
◼ : ∀ {a p}{A : Set a}{P : Pred∷ A p}
      (f : ∀ {n} x (xs : Vec A n) → P (x , xs)){n}(xs : Vec A n) → ■ P xs
◼ f ([]    ) = []
◼ f (x ∷ xs) = f x xs ∷ ◼ f xs
\end{code}

`■` is functorial in its first argument.

\begin{code}
map■₁ : ∀ {a}{A : Set a}{p}{P : Pred∷ A p}{q}{Q : Pred∷ A q} →
          (∀ {x n}{xs : Vec A n} → P (x , xs) → Q (x , xs)) →
           ∀ {n}{xs : Vec A n} → ■ P xs → ■ Q xs
map■₁ f      [] = []
map■₁ f (x ∷ p) = f x ∷ map■₁ f p
\end{code}

### `All` and `all`

`□` and `◻` are the versions of `■` and `◼` for predicates that ignore
tails.

\begin{code}
□ : ∀ {a p}{A : Set a}(P : A → Set p) → ∀ {n} → Vec A n → Set (a L.⊔ p)
□ P = ■ (P ∘ fst)

◻ : ∀ {a p}{A : Set a}{P : A → Set p}(f : (x : A) → P x){n}(xs : Vec A n) → □ P xs
◻ f xs = ◼ (λ x _ → f x) xs
\end{code}

### By large elimination

`■` could be defined as a paramorphism, but it would be awkward to use in Agda.

\begin{code}
■AsPara : ∀ {a p}{A : Set a}(P : Pred∷ A p) → ∀ {n} → Vec A n → Set (a L.⊔ p)
■AsPara P = para (L.Lift ⊤) (λ x xs T → P (x , xs) × T)
\end{code}

`□`, on the other hand, corresponds to a catamorphism.

\begin{code}
□AsPara : ∀ {a p}{A : Set a}(P : A → Set p) → ∀ {n} → Vec A n → Set (a L.⊔ p)
□AsPara P = cata (L.Lift ⊤) (λ x T → P x × T)
\end{code}

### `Σ (Vec A n) (□ P) ≅ Vec (Σ A P) n`

This isomorphism holds for any polynomial functor (not just lists or
vectors). I left it because I think it can be useful, however I'm not
using it in this file.

\begin{code}
module Σ□ {a}{A : Set a}{p}{P : A → Set p} where

  to : ∀ {n} → Σ (Vec A n) (□ P) → Vec (Σ A P) n
  to (._  ,     []) = []
  to (._  , p ∷ ps) = (, p) ∷ to (, ps)

  from : ∀ {n} → Vec (Σ A P) n → Σ (Vec A n) (□ P)
  from (          []) = , []
  from ((a , p) ∷ xs) = , p ∷ snd (from xs)

  from∘to≡id : ∀ {n}(xs : Σ (Vec A n) _) → from (to xs) ≡ xs
  from∘to≡id (._  ,     [])                           = refl
  from∘to≡id (._  , p ∷ ps) rewrite from∘to≡id (, ps) = refl

  to∘from≡id : ∀ {n}(xs : Vec (Σ A P) n) → to (from xs) ≡ xs
  to∘from≡id (          [])                       = refl
  to∘from≡id ((a , p) ∷ ps) rewrite to∘from≡id ps = refl
\end{code}

The generalisation to `■` seems trickier, when using vectors as
opposed to lists.

### Selections

`Sel P Q xs` is a type of "selections" of elements of `xs`, guided by
the two predicates `P` and `Q`: if for an element `x` we choose `inl`
(i.e., we "keep" it), we must also provide a proof of `P x`.
Alternatively, if we choose `inr` ("skip"), we must also provide a
proof of `Q x`.

\begin{code}
Sel : ∀ {a}{A : Set a}{p}(P Q : A → Set p){n} → Vec A n → Set _
Sel P Q = □ λ a → P a ⊎ Q a
\end{code}

Maybe a better notation would be the following, but I'm not going to
switch for now.

\begin{code}
_□+_ = Sel
\end{code}

We could give a rich interpretation to a `Sel P Q` of length `n` in
one go, by computing an `m ≤ n`, a vector of `P`s of length `m`, and a
vector of `Q`s of length `n - m`.

The definition (`Rich.⟦_⟧Sel`) is a bit noisy, and using it in
practice would be troublesome because of the internal coercions. Maybe
it could be improved by substituting `Fin (suc n)` with `Σ ℕ (_≥_ n)`,
but it would still not be very nice.

\begin{code}
module Rich {a}{A : Set a}{p}{P Q : A → Set p} where

  lem : (n : ℕ)(i : Fin (ℕ.suc n)) → ℕ.suc (n ℕ.∸ toℕ i) ≡ ℕ.suc n ℕ.∸ toℕ i
  lem (ℕ.zero ) (zero  ) = refl
  lem (ℕ.zero ) (suc ())
  lem (ℕ.suc n) (zero  ) = refl
  lem (ℕ.suc n) (suc i ) = lem n i

  toℕ≡toℕ∘inject₁ : ∀ n (i : Fin n) → toℕ i ≡ toℕ (inject₁ i)
  toℕ≡toℕ∘inject₁ ._ zero = refl
  toℕ≡toℕ∘inject₁ ._ (suc i) = cong ℕ.suc (toℕ≡toℕ∘inject₁ _ i)

  ⟦_⟧Sel : ∀ {n}{xs : Vec A n} →
             Sel P Q xs → Σ (Fin (ℕ.suc n)) λ m → Vec (Σ A P) (toℕ m) × Vec (Σ A Q) (n ℕ.∸ toℕ m)
  ⟦_⟧Sel                           (         []) = _ , [] , []
  ⟦_⟧Sel {n = ℕ.suc n}{xs = x ∷ xs}(inl p ∷ ss) = Σ.map _ (Σ.map (_∷_ (, p)) id) ⟦ ss ⟧Sel
  ⟦_⟧Sel {n = ℕ.suc n}{xs = x ∷ xs}(inr q ∷ ss) =
    Σ.map inject₁
         (λ {m} → Σ.map (subst (Vec _) (toℕ≡toℕ∘inject₁ _ _))
                        (subst (Vec _) (trans (lem n m) (cong (ℕ._∸_ _) (toℕ≡toℕ∘inject₁ _ m)))
                         ∘ _∷_ (, q)))
          ⟦ ss ⟧Sel

  module _ {n}{xs : Vec A n} where

    ⟦_⟧Sel₁ = fst ∘ ⟦_⟧Sel {n}{xs}
    ⟦_⟧Sel₂ = fst ∘ snd ∘ ⟦_⟧Sel {n}{xs}
    ⟦_⟧Sel₃ = snd ∘ snd ∘ ⟦_⟧Sel {n}{xs}
\end{code}

The above code would be much nicer for lists. For now I'll stay with
the following semantics:

\begin{code}
⟦_⟧Sel : ∀ {a}{A : Set a}{p}{P Q : A → Set p}{n}{xs : Vec A n} → Sel P Q xs → Σ ℕ (Vec (Σ A P))
⟦ []         ⟧Sel = ℕ.zero , []
⟦ inl p ∷ ss ⟧Sel = Σ.map _ (_∷_ (, p)) ⟦ ss ⟧Sel
⟦ inr q ∷ ss ⟧Sel = ⟦ ss ⟧Sel

module _ {a}{A : Set a}{p}{P Q : A → Set p}{n}{xs : Vec A n} where

  ⟦_⟧Sel₁ = fst ∘ ⟦_⟧Sel {a}{A}{p}{P}{Q}{n}{xs}
  ⟦_⟧Sel₂ = snd ∘ ⟦_⟧Sel {a}{A}{p}{P}{Q}{n}{xs}
\end{code}

In "some" sense, the above interpretation allows to express that `■`
is functorial in its second argument as well.

\begin{code}
module _ {a}{A : Set a}{p}{P Q : A → Set p}{c}{C : Pred∷ A c}
         (k : ∀ {x n}{xs : Vec A n}(s : Sel P Q xs) → C (x , xs) → C (x , V.map fst ⟦ s ⟧Sel₂)) where

  map■₂ : ∀ {n}{xs : Vec A n}(s : Sel P Q xs) → ■ C xs → ■ C (V.map fst ⟦ s ⟧Sel₂)
  map■₂           []       cs = cs
  map■₂ (inl p ∷ ss) (c ∷ cs) = k ss c ∷ map■₂ ss cs
  map■₂ (inr q ∷ ss) (c ∷ cs) = map■₂ ss cs
\end{code}

The definition of `Sel` came to me from the attempt to find a common
implementation for what I call "free selections" (`□ (const Bool)`)
and "decisive selections" (`□ (Dec ∘ P)`) in the following.

#### Free selections

We can put no restrictions to the selection process, obtaining "free
selections":

\begin{code}
FreeSel : ∀ {a}{A : Set a}{n} → Vec A n → Set _
FreeSel = Sel (const ⊤) (const ⊤)
\end{code}

We can check that `FreeSel` is the family we wanted.

\begin{code}
private FreeSel≡□Bool : ∀ {a}{A}{n} → FreeSel {a}{A}{n} ≡ □ (const Bool)
        FreeSel≡□Bool = refl
\end{code}

Free selections are essentially "order-preserving embeddings"
(http://sneezy.cs.nott.ac.uk/fplunch/weblog/?p=91): more precisely, I
think OPEs can be thought as "algebraic ornaments" of free selections
wrt the algebra underlying `⟦_⟧Sel` (as specialised to `FreeSel`).

As it doesn't make sense to build the algebraic ornaments machinery
for a single datatype, in [my older
code](https://github.com/ma82/adapter/blob/master/AD/OPE.lagda) I
defined OPEs for lists by "refinement" (in the sense of `Σ`) from a
type akin to `FreeSel`.

The idea of "algebraic ornament" and its relation to refinements is
explained in
[1](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf)
and [2](http://bentnib.org/inductive-refinement.pdf).

#### "Decisive" selections

In this case `P` must hold for the kept elements and be refutable for
the skipped ones. `DecSel P` is what is obtained by "mapping" (`◻`) a
decision function over a vector.

\begin{code}
DecSel : ∀ {a}{A : Set a}{n p} → (A → Set p) → Vec A n → Set _
DecSel P = Sel P (¬_ ∘ P)
\end{code}

We can check that `DecSel` is the family we wanted.

\begin{code}
private DecSel≡□Dec∘ : ∀ {a A n p P} → DecSel {a}{A}{n}{p} P ≡ □ (Dec ∘ P)
        DecSel≡□Dec∘ = refl
\end{code}

### "No duplicates"

`■` and `□` can be used to encode the property that a vector does not
contain a same element twice.

\begin{code}
_∉_ : ∀ {a}{A : Set a}{n} → A → Vec A n → Set a
_∉_ a = □ (_≢_ a)

NoDups : ∀ {a}{A : Set a}{n} → Vec A n → Set a
NoDups = ■ (uc _∉_)
\end{code}

## ◆

`◆ P xs` corresponds to the property that `P (y , ys)` holds on some
element `y` of vector `xs` and its tail `ys`.

\begin{code}
data ◆ {a p}{A : Set a}(P : Pred∷ A p) : ∀ {n} → Vec A n → Set (a L.⊔ p) where
  here  : ∀ {x n}{xs : Vec A n} → P (x , xs) → ◆ P (x ∷ xs)
  there : ∀ {x n}{xs : Vec A n} → ◆ P xs     → ◆ P (x ∷ xs)

⬩ : ∀ {a p}{A : Set a}{P : Pred∷ A p} →
    ∀ {n}{xs : Vec A n} → ◆ P xs → Σ A λ x → Σ ℕ λ n → Σ (Vec A n) (P ∘ _,_ x)
⬩ (here  x) = , , , x
⬩ (there p) = ⬩ p
\end{code}

It is also "functorial" in both arguments, but "contravariant" wrt the
second.

\begin{code}
map◆₁ : ∀ {a}{A : Set a}{p}{P : Pred∷ A p}{q}{Q : Pred∷ A q} →
        (∀ {x n}{xs : Vec A n} → P (x , xs) → Q (x , xs)) →
         ∀ {n}{xs : Vec A n} → ◆ P xs → ◆ Q xs
map◆₁ f (here  p) = here  (f p)
map◆₁ f (there i) = there (map◆₁ f i)

map◆₂ : ∀ {a}{A : Set a}{p}{P Q : A → Set p}{c}{C : Pred∷ A c} →
          (∀ {x n}{xs : Vec A n}(s : Sel P Q xs) → C (x , V.map fst ⟦ s ⟧Sel₂) → C (x , xs)) →
           ∀ {n}{xs : Vec A n}(s : Sel P Q xs) → ◆ C (V.map fst ⟦ s ⟧Sel₂) → ◆ C xs
map◆₂ k (       [])       ()
map◆₂ k (inl y ∷ s) (here  p) = here (k s p)
map◆₂ k (inl y ∷ s) (there i) = there (map◆₂ k s i)
map◆₂ k (inr n ∷ s)        i  = there (map◆₂ k s i)
\end{code}

### `Any` and `any`

`◇` and `⋄` are the versions of `◆` and `⬩` for predicates that ignore
the tails.

\begin{code}
◇ : ∀ {a p}{A : Set a}(P : A → Set p) → ∀ {n} → Vec A n → Set (a L.⊔ p)
◇ P = ◆ (P ∘ fst)

⋄ : ∀ {a p}{A : Set a}{P : A → Set p} → ∀ {n}{xs : Vec A n} → ◇ P xs → Σ A λ x → P x
⋄ = Σ.map id (snd ∘ snd) ∘ ⬩
\end{code}

### By large elimination

Again, we have ◆ : ◇ = paramorphism : catamorphism.

\begin{code}
◆AsPara : ∀ {a p}{A : Set a}(P : Pred∷ A p) → ∀ {n} → Vec A n → Set (a L.⊔ p)
◆AsPara P = para (L.Lift ⊥) (λ x xs T → P (x , xs) ⊎ T)
\end{code}

\begin{code}
◇AsPara : ∀ {a p}{A : Set a}(P : A → Set p) → ∀ {n} → Vec A n → Set (a L.⊔ p)
◇AsPara P = cata (L.Lift ⊥) (λ x T → P x ⊎ T)
\end{code}

### ◆-alt

The following is an isomorphic encoding of `◆` (at least under UIP):

\begin{code}
_!!_ : ∀ {a n} {A : Set a} → Vec A n → (i : Fin n) → Vec A (toℕ i) × A × Vec A (n ℕ.∸ ℕ.suc (toℕ i))
(x ∷ xs) !! zero    =                                  [] , x , xs
(x ∷ xs) !! (suc i) = let ls , y , rs = xs !! i in x ∷ ls , y , rs

◆-alt : ∀ {a p}{A : Set a}(P : Pred∷ A p) → ∀ {n} → Vec A n → Set p
◆-alt P {n} xs = Σ (Fin n) (P ∘ snd ∘ _!!_ xs)
\end{code}

See also [this code](https://github.com/ma82/adapter/blob/master/AD/Ix.lagda).

This encoding has the advantage of not hiding the `P _` under a useless spine.

For example, `⬩` and `map◆₁` are now O(1).

\begin{code}
⬩-alt : ∀ {a p}{A : Set a}{P : Pred∷ A p} →
          ∀ {n}{xs : Vec A n} → ◆-alt P xs → Σ A λ x → Σ ℕ λ n → Σ (Vec A n) (P ∘ _,_ x)
⬩-alt = ,_ ∘ ,_ ∘ ,_ ∘ snd

map◆-alt₁ : ∀ {a}{A : Set a}{p}{P : Pred∷ A p}{q}{Q : Pred∷ A q} →
              (∀ {x n}{xs : Vec A n} → P (x , xs) → Q (x , xs)) →
               ∀ {n}{xs : Vec A n} → ◆-alt P xs → ◆-alt Q xs
map◆-alt₁ f = Σ.map id f
\end{code}

We won't use this alternative encoding for clarity.

Also, Ulf Norell didn't like it! :-(

### `_∈_` (elem)

We can use `◇` to encode `_∈_`

\begin{code}
_∈_ : ∀ {a}{A : Set a}{n} → A → Vec A n → Set a
_∈_ a = ◇ (_≡_ a)
\end{code}

The `decSel∈` lemma says that if we have a selection `DecSel P xs` and
an element `a` of `xs` for which `P a` holds, we have that `a` is also
an element of the vector denoted by the selection.

\begin{code}
decSel∈ : ∀ {a}{A : Set a}{p}{P : A → Set p}{n}{xs : Vec A n} →
            (s : DecSel P xs) → ∀ {a} → a ∈ xs → P a → a ∈ V.map fst ⟦ s ⟧Sel₂
decSel∈ (inl q ∷ r) (here     h) p = here h
decSel∈ (inl q ∷ r) (there    j) p = there (decSel∈ r j p)
decSel∈ (inr q ∷ r) (here  refl) p = ⊥-elim (q p)
decSel∈ (inr q ∷ r) (there    j) p = decSel∈ r j p
\end{code}

Using the `Rich` semantics, one could get a stronger result for `Sel P Q`.

\begin{code}
module Rich2 (⊘ : ∀ {x}{X : Set x} → X) where

  sel∈ : ∀ {a}{A : Set a}{p}{P Q : A → Set p}{n}{xs : Vec A n} →
           (s : Sel P Q xs) → ∀ {a} → a ∈ xs →   (P a × a ∈ V.map fst Rich.⟦ s ⟧Sel₂)
                                               ⊎ (Q a × a ∈ V.map fst Rich.⟦ s ⟧Sel₃)
  sel∈ (inl p ∷ s) (here refl) = inl (p , here refl)
  sel∈ (inr q ∷ s) (here refl) = inr (q , ⊘)
  sel∈ (inl p ∷ s) (there   i) = ⊎.map (Σ.map id there) id (sel∈ s i)
  sel∈ (inr q ∷ s) (there   i) = ⊎.map ⊘ (Σ.map id ⊘) (sel∈ s i)
\end{code}

I'm leaving the holes as an exercise in circumventing horrible
coercions which I really prefer not to do myself. :-) They would not
be there if, for instance, we had used lists (I haven't tried,
though).

## Negation vs `■` and `◆`

We can prove some results about the interaction of negation `¬_` with
`■` and `◆`: modal logic is the *informal* inspiration.

1. `■¬` is logically equivalent to `¬◆`.

Note that assuming extensionality they would both be propositional,
and the logical equivalence would extend to an isomorphism.

\begin{code}
module _ {a}{A : Set a}{p}{P : Pred∷ A p} where

  ■¬→¬◆ : ∀ {n}{xs : Vec A n} → ■ (¬_ ∘ P) xs → ¬ (◆ P) xs
  ■¬→¬◆ (¬p ∷ ps) (here  p) = ¬p p
  ■¬→¬◆ (¬p ∷ ps) (there i) = ■¬→¬◆ ps i

  ¬◆→■¬ : ∀ {n}{xs : Vec A n} → ¬ (◆ P) xs → ■ (¬_ ∘ P) xs
  ¬◆→■¬ {xs =     []} f = []
  ¬◆→■¬ {xs = x ∷ xs} f = (f ∘ here) ∷ ¬◆→■¬ (f ∘ there)
\end{code}

We can use the above correspondence to obtain two more equivalent
definitions of `NoDups`.

\begin{code}
module NoDupsAlternatives {a}{A : Set a}{n} where

  NoDups1 NoDups2 : Vec A n → Set a
  NoDups1 = ■ (¬_ ∘ uc _∈_)
  NoDups2 = ¬_ ∘ ◆ (uc _∈_)

  0to1 : ∀ {xs} → NoDups  xs → NoDups1 xs ; 0to1 = map■₁ ■¬→¬◆
  1to0 : ∀ {xs} → NoDups1 xs → NoDups  xs ; 1to0 = map■₁ ¬◆→■¬
  1to2 : ∀ {xs} → NoDups1 xs → NoDups2 xs ; 1to2 = ■¬→¬◆
  2to1 : ∀ {xs} → NoDups2 xs → NoDups1 xs ; 2to1 = ¬◆→■¬
\end{code}

2. `◆¬` implies `¬■`.

\begin{code}
module _ {a}{A : Set a}{p}{P : Pred∷ A p} where

  ◆¬→¬■ : ∀ {n}{xs : Vec A n} → ◆ (¬_ ∘ P) xs → ¬ ■ P xs
  ◆¬→¬■ (here ¬p) (p ∷ ps) = ¬p p
  ◆¬→¬■ (there i) (p ∷ ps) = ◆¬→¬■ i ps
\end{code}

The missing

    ¬■→◆¬ : ∀ {n}{xs : Vec A n} → ¬ ■ P xs → ◆ (¬_ ∘ P) xs

, similarly to

    ¬ (A × B) → ¬ A ⊎ ¬ B

, does not have constructive implementations.

## `filter`

The names `filterTag` and `filter` are taken from the code related to
Botta et al's "Sequential decision problems, dependently typed
solutions" and subsequent paper.

I tried to simplify the code by

1. defining `filterTag` in terms of the `DecSel` "view": we first
   build a `DecSel P` by calling `◻ dec`, then we interpret it using
   `⟦_⟧Sel`;

2. defining `filter` in terms of `filterTag`.

\begin{code}
module _ {a}{A : Set a}{p}{P : A → Set p}(dec : Dec/ P){n} where

  filterTag : Vec A n → Σ ℕ (Vec (Σ A P))
  filterTag = ⟦_⟧Sel ∘ ◻ dec

  filterTag₁ = fst ∘ filterTag ; filterTag₂ = snd ∘ filterTag

  filter : Vec A n → Σ ℕ (Vec A)
  filter = Σ.map id (V.map fst) ∘ filterTag

  filter₁ = fst ∘ filter ; filter₂ = snd ∘ filter
\end{code}

`filterTagNoDups`'s proof relies on `map■₂`, while `filterTag-Lemma`
is a direct consequence of `decSel∈`.

\begin{code}
  filterTagNoDups : ∀ {xs} → NoDups xs → NoDups (V.map fst (filterTag₂ xs))
  filterTagNoDups = map■₂ (map■₂ (const id)) (◻ dec _)

  filterTagLemma : ∀ {x xs} → x ∈ xs → (p : P x) → x ∈ V.map fst (filterTag₂ xs)
  filterTagLemma = decSel∈ (◻ dec _)
\end{code}

`filterNoDups` and `filterLemma` are redundant, but are left for clarity.

\begin{code}
  filterNoDups : ∀ {xs} → NoDups xs → NoDups (filter₂ xs)
  filterNoDups = filterTagNoDups

  filterLemma : ∀ {xs x} → x ∈ xs → (p : P x) → x ∈ filter₂ xs
  filterLemma = filterTagLemma
\end{code}

### NoDups ↔ Injective1

See `Injective1` from Botta et al's code
(https://github.com/nicolabotta/SeqDecProbs/blob/master/VectProperties.lidr).

\begin{code}
Injective1 : ∀ {a}{A : Set a}{n} → Vec A n → Set a
Injective1 xs = ∀ i j → lookup i xs ≡ lookup j xs → i ≡ j
\end{code}

We can prove that `Injective1` is logically equivalent to
`NoDups`. Note that under functional extensionality they would both be
propositional, and the logical equivalence would extend to an
isomorphism.

(If you find a better proof than the one below please let me know :-) )

\begin{code}
module NoDups↔Injective1 {a}{A : Set a} where

  lem1 : ∀ {n x} j {xs : Vec A n} → x ≡ lookup j xs → ¬ x ∉ xs
  lem1 (zero ) h (p ∷ ps) = p h
  lem1 (suc j) h (p ∷ ps) = lem1 j h ps

  suc-inj : ∀ {n}{i j : Fin n} → suc i ≡ suc j → i ≡ j
  suc-inj refl = refl

  zero≢suc : ∀ {n}{i : Fin n} → ¬ zero ≡ suc i
  zero≢suc ()

  lem2 : ∀ {n x1 x2}{xs : Vec A n} → Injective1 (x1 V.∷ x2 ∷ xs) → Injective1 (x1 ∷ xs)
  lem2 p zero zero h = refl
  lem2 p zero (suc j) = ⊥-elim ∘ zero≢suc ∘ p zero (suc (suc j))
  lem2 p (suc i) zero = ⊥-elim ∘ zero≢suc ∘ p zero (suc (suc i)) ∘ sym
  lem2 p (suc i) (suc j) = suc-inj ∘ p _ _

  lem3 : ∀ {n x}{xs : Vec A n} → Injective1 (x ∷ xs) → x ∉ xs
  lem3 {xs =    []} ns = []
  lem3 {xs = _ ∷ _} ns = (λ h → case ns zero (suc zero) h of λ ()) ∷ lem3 (lem2 ns)

  to : ∀ {n}{xs : Vec A n} → NoDups xs → Injective1 xs
  to (n ∷ ns) zero zero p = refl
  to (n ∷ ns) zero (suc j) p = ⊥-elim $ lem1 j      p  n
  to (n ∷ ns) (suc i) zero p = ⊥-elim $ lem1 i (sym p) n
  to (n ∷ ns) (suc i) (suc j) p = cong suc (to ns i j p)

  from : ∀ {n}{xs : Vec A n} → Injective1 xs → NoDups xs
  from {xs =     []} ns = []
  from {xs = x ∷ xs} ns = lem3 ns ∷ from λ _ _ → suc-inj ∘ ns _ _
\end{code}

`filter` preserves `Injective1`.

\begin{code}
filterInjective1 : ∀ {a p}{A : Set a}{P : A → Set p}{dec : Dec/ P}{n}{xs : Vec A n} →
                     Injective1 xs → Injective1 (filter₂ dec xs)
filterInjective1 = to ∘ filterNoDups _ ∘ from where open NoDups↔Injective1
\end{code}

### Another example: `_⊆_`

`xs ⊆ ys` means that all the elements in `xs` are in `ys`.

We can use `map■₂` to prove that `filter` preserves `_⊆_`.

\begin{code}
_⊆_ : ∀ {A : Set}{m n} → Vec A m → Vec A n → Set
xs ⊆ ys = □ (λ y → y ∈ ys) xs

⊆-refl : ∀ {A n}{xs : Vec A n} → xs ⊆ xs
⊆-refl {xs = []    } = []
⊆-refl {xs = x ∷ xs} = here refl ∷ map■₁ there ⊆-refl

filter-⊆ : ∀ {A}{P : A → Set}{dec : Dec/ P}{n}{xs : Vec A n} →
             filter₂ dec xs ⊆ xs
filter-⊆ = map■₂ (const id) (◻ _ _) ⊆-refl
\end{code}

## Comments

- This file was motivated by [a
  conversation](https://groups.google.com/forum/#!topic/idris-lang/2ixyGmYPD9o)
  with Nicola Botta on `Idris-dev`. Nicola asked a question about
  proving properties of `filter` for Nat-indexed vectors. I used
  vectors for this reason, but I think it might be useful to rewrite
  these definitions for lists.

- Some definitions have decent datatype-generic versions, for some
  universe of datatypes depending on the definition.

- For what concerns `map■₂` and `map◆₂`, it might be interesting to
  rigorously identify the source/target categories and the functor:
  the morphism which is being mapped is the selection, which I think
  should be put in "relational" (OPE-like) form.

- Defining the components of the output of `⟦_⟧Sel` separately should
  lead to faster compiled programs. It probably differs between Idris
  and Agda and between backends. I don't know whether this is always
  the case in lazy languages, but it should never harm.

- I defined `filterTag` and `filter` by composing `foldr`s. I am not
  sure about what this means space-wise in call-by-value languages
  such as Idris.

Matteo Acerbi <matteo.acerbi@gmail.com>
