module Data.VectType where
open import Builtins
open import Data.Bool
open import Idris.Data.Nat
open import Syntax.PreorderReasoning
-- TODO: pick a good naming for Idris' = and ==: Currently we have renamed = in Idris to == in Agda (because = is reserved) but not figured out another name for ==
open import Idris.Data.Fin using (Fin; FZ; FS)

-- %access public
-- %default total

module Vect where

  infixr 7 _::_

  data Vect : Nat -> Type -> Type where
    Nil  : {a : Type} -> Vect Z a
    _::_ : {a : Type} -> {n : Nat} -> (x : a) -> (xs : Vect n a) -> Vect (S n) a

  [] = Nil

  -- Hints for interactive editing
--  %name Vect xs,ys,zs,ws

  --------------------------------------------------------------------------------
  -- Length
  --------------------------------------------------------------------------------

  -- ||| Calculate the length of a `Vect`.
  -- |||
  -- ||| **Note**: this is only useful if you don't already statically know the length
  -- ||| and you want to avoid matching the implicit argument for erasure reasons.
  -- ||| @ n the length (provably equal to the return value)
  -- ||| @ xs the vector
  length : {a : Type} -> {n : Nat} ->
           (xs : Vect n a) -> Nat
  length [] = 0
  length (x :: xs) = 1 + length xs

  -- ||| Show that the length function on vectors in fact calculates the length
  private lengthCorrect : {a : Type} -> {n : Nat} -> (n : Nat) -> (xs : Vect n a) -> length xs == n
  lengthCorrect Z     []        = Refl
  lengthCorrect (S n) (x :: xs) = {! rewrite lengthCorrect n xs in Refl !}

  --------------------------------------------------------------------------------
  -- Indexing into vectors
  --------------------------------------------------------------------------------

  -- ||| All but the first element of the vector
  tail : {a : Type} -> {n : Nat} ->
         Vect (S n) a -> Vect n a
  tail (x :: xs) = xs

  -- ||| Only the first element of the vector
  head : {a : Type} -> {n : Nat} ->
         Vect (S n) a -> a
  head (x :: xs) = x

  -- ||| The last element of the vector
  last : {a : Type} -> {n : Nat} ->
         Vect (S n) a -> a
  last (x :: [])    = x
  last (x :: y :: ys) = last (y :: ys)

  -- ||| All but the last element of the vector
  init : {a : Type} -> {n : Nat} ->
         Vect (S n) a -> Vect n a
  init (x :: [])    = []
  init (x :: y :: ys) = x :: init (y :: ys)

  -- ||| Extract a particular element from a vector
  index : {a : Type} -> {n : Nat} ->
          Fin n -> Vect n a -> a
  index FZ     (x :: xs) = x
  index (FS k) (x :: xs) = index k xs


  -- ||| Insert an element at a particular index
  insertAt : {a : Type} -> {n : Nat} ->
             Fin (S n) -> a -> Vect n a -> Vect (S n) a
  insertAt FZ     y xs        = y :: xs
  insertAt (FS k) y (x :: xs) = x :: insertAt k y xs
  insertAt (FS k) y []        = void k -- TODO absurd k

  -- ||| Construct a new vector consisting of all but the indicated element
  deleteAt : {a : Type} -> {n : Nat} ->
             Fin (S n) -> Vect (S n) a -> Vect n a
  deleteAt           FZ     (x :: xs) = xs
  deleteAt {n = S m} (FS k) (x :: xs) = x :: deleteAt k xs
  deleteAt {n = Z}   (FS k) (x :: xs) = void k -- TODO absurd k
  deleteAt           _      []      impossible

  -- ||| Replace an element at a particlar index with another
  replaceAt : {t : Type} -> {n : Nat} ->
              Fin n -> t -> Vect n t -> Vect n t
  replaceAt FZ     y (x :: xs) = y :: xs
  replaceAt (FS k) y (x :: xs) = x :: replaceAt k y xs

  -- ||| Replace the element at a particular index with the result of applying a function to it
  -- ||| @ i the index to replace at
  -- ||| @ f the update function
  -- ||| @ xs the vector to replace in
  updateAt : {t : Type} -> {n : Nat} ->
             (i : Fin n) -> (f : t -> t) -> (xs : Vect n t) -> Vect n t
  updateAt FZ     f (x :: xs) = f x :: xs
  updateAt (FS k) f (x :: xs) = x :: updateAt k f xs

  --------------------------------------------------------------------------------
  -- Subvectors
  --------------------------------------------------------------------------------

  -- ||| Get the first m elements of a Vect
  -- ||| @ m the number of elements to take
  take : {a : Type} -> {m : Nat} ->
         (n : Nat) -> Vect (n + m) a -> Vect n a
  take Z     xs        = []
  take (S k) (x :: xs) = x :: take k xs

  -- ||| Remove the first m elements of a Vect
  -- ||| @ m the number of elements to remove
  drop : {a : Type} -> {m : Nat} ->
         (n : Nat) -> Vect (n + m) a -> Vect m a
  drop Z     xs        = xs
  drop (S k) (x :: xs) = drop k xs

  -- ||| Take the longest prefix of a Vect such that all elements satisfy some
  -- ||| Boolean predicate.
  -- |||
  -- ||| @ p the predicate

  takeWhile : {a : Type} -> {n : Nat} ->
              (p : a -> Bool) -> Vect n a -> Sigma Nat (\q -> Vect q a)
  takeWhile p []      = MkSigma _ []
  takeWhile p (x :: xs) =
    let MkSigma len ys = takeWhile p xs
    in if p x then
        MkSigma (S len) (x :: ys)
      else
        MkSigma _ []

  -- ||| Remove the longest prefix of a Vect such that all removed elements satisfy some
  -- ||| Boolean predicate.
  -- |||
  -- ||| @ p the predicate
  dropWhile : {a : Type} -> {n : Nat} ->
              (p : a -> Bool) -> Vect n a -> Sigma Nat (\q -> Vect q a)
  dropWhile p [] = MkSigma _ []
  dropWhile p (x :: xs) =
    if p x then
      dropWhile p xs
    else
      MkSigma _ (x :: xs)

  --------------------------------------------------------------------------------
  -- Transformations
  --------------------------------------------------------------------------------

  -- ||| Reverse the order of the elements of a vector
  reverse : {a : Type} -> {n : Nat} ->
            Vect n a -> Vect n a
  reverse xs = go [] xs
    where go : {a : Type} -> {n : Nat} -> {m : Nat} ->
               Vect n a -> Vect m a -> Vect (n + m) a
          go {n}           acc []        = {! rewrite plusZeroRightNeutral n in acc !}
          go {n} {m = S m} acc (x :: xs) = {! rewrite sym $ plusSuccRightSucc n m
                                         in go (x :: acc) xs !}

  -- ||| Alternate an element between the other elements of a vector
  -- ||| @ sep the element to intersperse
  -- ||| @ xs the vector to separate with `sep`
  intersperse : {a : Type} -> {n : Nat} ->
                (sep : a) -> (xs : Vect n a) -> Vect (n + pred n) a
  intersperse sep []      = []
  intersperse sep (x :: xs) = x :: intersperse' sep xs
    where
      intersperse' : {a : Type} -> {n : Nat} ->
                     a -> Vect n a -> Vect (n + n) a
      intersperse'           sep []      = []
      intersperse' {n = S n} sep (x :: xs) = {! rewrite sym $ plusSuccRightSucc n n
                                         in sep :: x :: intersperse' sep xs !}

  --------------------------------------------------------------------------------
  -- Conversion from list (toList is provided by Foldable)
  --------------------------------------------------------------------------------

{- TODO
  fromList' : {a : Type} -> {n : Nat} ->
              Vect n a -> (l : List a) -> Vect (length l + n) a
  fromList' ys [] = ys
  fromList' {n} ys (x :: xs) =
    {! rewrite (plusSuccRightSucc (length xs) n) ==>
            Vect (plus (length xs) (S n)) a in
    fromList' (x :: ys) xs !}

  -- ||| Convert a list to a vector.
  -- |||
  -- ||| The length of the list should be statically known.
  fromList : (l : List a) -> Vect (length l) a
  fromList l =
    {! rewrite (sym $ plusZeroRightNeutral (length l)) in
    reverse $ fromList' [] l !}
-}

  --------------------------------------------------------------------------------
  -- Building (bigger) vectors
  --------------------------------------------------------------------------------

  -- ||| Append two vectors
  _++_ : {a : Type} -> {m : Nat} -> {n : Nat} -> Vect m a -> Vect n a -> Vect (m + n) a
  _++_ []      ys = ys
  _++_ (x :: xs) ys = x :: xs ++ ys

  -- ||| Repeate some value n times
  -- ||| @ n the number of times to repeat it
  -- ||| @ x the value to repeat
  replicate : {a : Type} ->
              (n : Nat) -> (x : a) -> Vect n a
  replicate Z     x = []
  replicate (S k) x = x :: replicate k x

  --------------------------------------------------------------------------------
  -- Zips and unzips
  --------------------------------------------------------------------------------

  -- ||| Combine two equal-length vectors pairwise with some function
  zipWith : {a : Type} -> {b : Type} -> {c : Type} -> {n : Nat} ->
            (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
  zipWith f []      []      = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  -- ||| Combine three equal-length vectors into a vector with some function
  zipWith3 : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
  zipWith3 f []      []      []      = []
  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

  -- ||| Combine two equal-length vectors pairwise
  zip : Vect n a -> Vect n b -> Vect n (a, b)
  zip = zipWith (\x y -> (x,y))

  -- ||| Combine three equal-length vectors elementwise into a vector of tuples
  zip3 : Vect n a -> Vect n b -> Vect n c -> Vect n (a, b, c)
  zip3 = zipWith3 (\x y z -> (x,y,z))

  -- ||| Convert a vector of pairs to a pair of vectors
  unzip : Vect n (a, b) -> (Vect n a, Vect n b)
  unzip []           = ([], [])
  unzip ((l, r) :: xs) with (unzip xs)
  ... | (lefts, rights) = (l :: lefts, r :: rights)

  -- ||| Convert a vector of three-tuples to a triplet of vectors
  unzip3 : Vect n (a, b, c) -> (Vect n a, Vect n b, Vect n c)
  unzip3 []            = ([], [], [])
  unzip3 ((l,c,r) :: xs) with (unzip3 xs)
  ...  | (lefts, centers, rights) = (l :: lefts, c :: centers, r :: rights)

  --------------------------------------------------------------------------------
  -- Equality
  --------------------------------------------------------------------------------
{- TODO
  instance (Eq a) => Eq (Vect n a) where
    _==_ []      []      = True
    _==_ (x :: xs) (y :: ys) =
      if x == y then
        xs == ys
      else
        False
-}

  --------------------------------------------------------------------------------
  -- Order
  --------------------------------------------------------------------------------
{- TODO

  instance Ord a => Ord (Vect n a) where
    compare []      []      = EQ
    compare (x :: xs) (y :: ys) =
      if x /= y then
        compare x y
      else
        compare xs ys
-}


  --------------------------------------------------------------------------------
  -- Maps
  --------------------------------------------------------------------------------
{- TODO

  instance Functor (Vect n) where
    map f []        = []
    map f (x :: xs) = f x  ::  map f xs
-}

  -- ||| Map a partial function across a vector, returning those elements for which
  -- ||| the function had a value.
  -- |||
  -- ||| The first projection of the resulting pair (ie the length) will always be
  -- ||| at most the length of the input vector. This is not, however, guaranteed
  -- ||| by the type.
  -- |||
  -- ||| @ f the partial function (expressed by returning `Maybe`)
  -- ||| @ xs the vector to check for results
  mapMaybe : (f : a -> Maybe b) -> (xs : Vect n a) -> (Sigma Nat (\m -> Vect m b))
  mapMaybe f []      = MkSigma _ []
  mapMaybe f (x :: xs) =
    let MkSigma len ys = mapMaybe f xs
    in case f x of
         Just y  -> MkSigma (S len) (y :: ys)
         Nothing -> MkSigma (  len) (     ys)


  --------------------------------------------------------------------------------
  -- Folds
  --------------------------------------------------------------------------------

  foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> Vect n t -> acc
  foldrImpl f e go [] = go e
  foldrImpl f e go (x :: xs) = foldrImpl f e (go . (f x)) xs

{- TODO
  instance Foldable (Vect n) where
    foldr f e xs = foldrImpl f e id xs
-}

  --------------------------------------------------------------------------------
  -- Special folds
  --------------------------------------------------------------------------------

  -- ||| Flatten a vector of equal-length vectors
  concat : Vect m (Vect n a) -> Vect (m * n) a
  concat []      = []
  concat (v :: vs) = v ++ concat vs

  -- ||| Foldr without seeding the accumulator
  foldr1 : (t -> t -> t) -> Vect (S n) t -> t
  foldr1 f (x :: xs) = foldr f x xs

  -- ||| Foldl without seeding the accumulator
  foldl1 : (t -> t -> t) -> Vect (S n) t -> t
  foldl1 f (x :: xs) = foldl f x xs
  --------------------------------------------------------------------------------
  -- Scans
  --------------------------------------------------------------------------------

  scanl : (b -> a -> b) -> b -> Vect n a -> Vect (S n) b
  scanl f q []      = [q]
  scanl f q (x :: xs) = q :: scanl f (f q x) xs

  --------------------------------------------------------------------------------
  -- Membership tests
  --------------------------------------------------------------------------------

  -- ||| Search for an item using a user-provided test
  -- ||| @ p the equality test
  -- ||| @ e the item to search for
  -- ||| @ xs the vector to search in
  elemBy : (p : a -> a -> Bool) -> (e : a) -> (xs : Vect n a) -> Bool
  elemBy p e []      = False
  elemBy p e (x :: xs) with (p e x)
  ...  | True  = True
  ...  | False = elemBy p e xs

  -- ||| Use the default Boolean equality on elements to search for an item
  -- ||| @ x what to search for
  -- ||| @ xs where to search
{- TODO
  elem : Eq a => (x : a) -> (xs : Vect n a) -> Bool
  elem = elemBy (==)
-}
  -- ||| Find the association of some key with a user-provided comparison
  -- ||| @ p the comparison operator for keys (True if they match)
  -- ||| @ e the key to look for
  lookupBy : (p : a -> a -> Bool) -> (e : a) -> (xs : Vect n (a, b)) -> Maybe b
  lookupBy p e []           = Nothing
  lookupBy p e ((l, r) :: xs) with (p e l)
  ... | True  = Just r
  ... | False = lookupBy p e xs

  -- ||| Find the assocation of some key using the default Boolean equality test
{- TODO
  lookup : Eq a => a -> Vect n (a, b) -> Maybe b
  lookup = lookupBy _==_
-}

  -- ||| Check if any element of xs is found in elems by a user-provided comparison
  -- ||| @ p the comparison operator
  -- ||| @ elems the vector to search
  -- ||| @ xs what to search for
  hasAnyBy : (p : a -> a -> Bool) -> (elems : Vect m a) -> (xs : Vect n a) -> Bool
  hasAnyBy p elems []      = False
  hasAnyBy p elems (x :: xs) with (elemBy p x elems)
  ... | True  = True
  ... | False = hasAnyBy p elems xs

  -- ||| Check if any element of xs is found in elems using the default Boolean equality test
{- TODO
  hasAny : Eq a => Vect m a -> Vect n a -> Bool
  hasAny = hasAnyBy (==)
-}
  --------------------------------------------------------------------------------
  -- Searching with a predicate
  --------------------------------------------------------------------------------

  -- ||| Find the first element of the vector that satisfies some test
  -- ||| @ p the test to satisfy
  find : (p : a -> Bool) -> (xs : Vect n a) -> Maybe a
  find p []      = Nothing
  find p (x :: xs) with (p x)
  ... | True  = Just x
  ... | False = find p xs

  -- ||| Find the index of the first element of the vector that satisfies some test
  findIndex : (a -> Bool) -> Vect n a -> Maybe Nat
  findIndex = findIndex' 0
    where
      findIndex' : Nat -> (a -> Bool) -> Vect n a -> Maybe Nat
      findIndex' cnt p []      = Nothing
      findIndex' cnt p (x :: xs) with (p x)
        | True  = Just cnt
        | False = findIndex' (S cnt) p xs

  -- ||| Find the indices of all elements that satisfy some test
  findIndices : (a -> Bool) -> Vect m a -> (p ** Vect p Nat)
  findIndices = findIndices' 0
    where
      total findIndices' : Nat -> (a -> Bool) -> Vect m a -> (p ** Vect p Nat)
      findIndices' cnt p []      = (_ ** [])
      findIndices' cnt p (x :: xs) with (findIndices' (S cnt) p xs)
        | (_ ** tail) =
         if p x then
          (_ ** cnt :: tail)
         else
          (_ ** tail)

  elemIndexBy : (a -> a -> Bool) -> a -> Vect m a -> Maybe Nat
  elemIndexBy p e = findIndex $ p e

{- TODO
  elemIndex : Eq a => a -> Vect m a -> Maybe Nat
  elemIndex = elemIndexBy (==)
-}

  elemIndicesBy : (a -> a -> Bool) -> a -> Vect m a -> (p ** Vect p Nat)
  elemIndicesBy p e = findIndices $ p e

{- TODO
  elemIndices : Eq a => a -> Vect m a -> (p ** Vect p Nat)
  elemIndices = elemIndicesBy (==)
-}

  --------------------------------------------------------------------------------
  -- Filters
  --------------------------------------------------------------------------------

  -- ||| Find all elements of a vector that satisfy some test
  filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)
  filter p [] = ( _ ** [] )
  filter p (x :: xs) with (filter p xs)
  ... | (_ ** tail) =
      if p x then
        (_ ** x :: tail)
      else
        (_ ** tail)

  -- ||| Make the elements of some vector unique by some test
  nubBy : (a -> a -> Bool) -> Vect n a -> (p ** Vect p a)
  nubBy = nubBy' []
    where
      nubBy' : Vect m a -> (a -> a -> Bool) -> Vect n a -> (p ** Vect p a)
      nubBy' acc p []      = (_ ** [])
      nubBy' acc p (x :: xs) with (elemBy p x acc)
      ...  | True  = nubBy' acc p xs
      ...  | False with (nubBy' (x :: acc) p xs)
      ...    | (_ ** tail) = (_ ** x :: tail)

  -- ||| Make the elements of some vector unique by the default Boolean equality
  nub : Eq a => Vect n a -> (p ** Vect p a)
  nub = nubBy (==)

  deleteBy : (a -> a -> Bool) -> a -> Vect n a -> (p ** Vect p a)
  deleteBy _  _ []      = (_ ** [])
  deleteBy eq x (y :: ys) =
    let (len ** zs) = deleteBy eq x ys
    in if x `eq` y then (_ ** ys) else (S len ** y  :: zs)

  delete : (Eq a) => a -> Vect n a -> (p ** Vect p a)
  delete = deleteBy (==)

  --------------------------------------------------------------------------------
  -- Splitting and breaking lists
  --------------------------------------------------------------------------------

  -- ||| A tuple where the first element is a Vect of the n first elements and
  -- ||| the second element is a Vect of the remaining elements of the original Vect
  -- ||| It is equivalent to (take n xs, drop n xs)
  -- ||| @ m   the index to split at
  -- ||| @ xs  the Vect to split in two
  splitAt : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect m a)
  splitAt n xs = (take n xs, drop n xs)

  partition : (a -> Bool) -> Vect n a -> ((p ** Vect p a), (q ** Vect q a))
  partition p []      = ((_ ** []), (_ ** []))
  partition p (x :: xs) =
    let ((leftLen ** lefts), (rightLen ** rights)) = partition p xs in
      if p x then
        ((S leftLen ** x :: lefts), (rightLen ** rights))
      else
        ((leftLen ** lefts), (S rightLen ** x :: rights))

  --------------------------------------------------------------------------------
  -- Predicates
  --------------------------------------------------------------------------------

  isPrefixOfBy : (a -> a -> Bool) -> Vect m a -> Vect n a -> Bool
  isPrefixOfBy p [] right        = True
  isPrefixOfBy p left []         = False
  isPrefixOfBy p (x :: xs) (y :: ys) with (p x y)
  ... | True  = isPrefixOfBy p xs ys
  ... | False = False

  isPrefixOf : Eq a => Vect m a -> Vect n a -> Bool
  isPrefixOf = isPrefixOfBy (==)

  isSuffixOfBy : (a -> a -> Bool) -> Vect m a -> Vect n a -> Bool
  isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

  isSuffixOf : Eq a => Vect m a -> Vect n a -> Bool
  isSuffixOf = isSuffixOfBy (==)

  --------------------------------------------------------------------------------
  -- Conversions
  --------------------------------------------------------------------------------

  maybeToVect : Maybe a -> (p ** Vect p a)
  maybeToVect Nothing  = (_ ** [])
  maybeToVect (Just j) = (_ ** [j])

  vectToMaybe : Vect n a -> Maybe a
  vectToMaybe []      = Nothing
  vectToMaybe (x :: xs) = Just x

  --------------------------------------------------------------------------------
  -- Misc
  --------------------------------------------------------------------------------

  catMaybes : Vect n (Maybe a) -> (p ** Vect p a)
  catMaybes []             = (_ ** [])
  catMaybes (Nothing :: xs)  = catMaybes xs
  catMaybes ((Just j) :: xs) with (catMaybes xs)
  ... | (_ ** tail) = (_ ** j :: tail)

  diag : Vect n (Vect n a) -> Vect n a
  diag []             = []
  diag ((x :: xs) :: xss) = x :: diag (map tail xss)

  range : Vect n (Fin n)
  range {n=Z}   = []
  range {n=S _} = FZ :: map FS range

  -- ||| Transpose a Vect of Vects, turning rows into columns and vice versa.
  -- |||
  -- ||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
  transpose : Vect m (Vect n a) -> Vect n (Vect m a)
  transpose []        = replicate _ []
  transpose (x :: xs) = zipWith (::) x (transpose xs)

  --------------------------------------------------------------------------------
  -- Applicative/Monad/Traversable
  --------------------------------------------------------------------------------
{- TODO
  instance Applicative (Vect k) where
      pure = replicate _

      fs <*> vs = zipWith apply fs vs

  instance Monad (Vect n) where
      m >>= f = diag (map f m)

  instance Traversable (Vect n) where
      traverse f [] = pure Vect.Nil
      traverse f (x :: xs) = [| Vect.( :: ) (f x) (traverse f xs) |]
-}

  --------------------------------------------------------------------------------
  -- Show
  --------------------------------------------------------------------------------
{- TODO
  instance Show a => Show (Vect n a) where
      show = show . toList
-}
  --------------------------------------------------------------------------------
  -- Properties
  --------------------------------------------------------------------------------

  vectConsCong : (x : a) -> (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> (x :: xs = x :: ys)
  vectConsCong x xs xs Refl = Refl

  vectNilRightNeutral : (xs : Vect n a) -> xs ++ [] = xs
  vectNilRightNeutral [] = Refl
  vectNilRightNeutral (x :: xs) =
    vectConsCong _ _ _ (vectNilRightNeutral xs)

  vectAppendAssociative : (x : Vect xLen a) -> (y : Vect yLen a) -> (z : Vect zLen a) -> x ++ (y ++ z) = (x ++ y) ++ z
  vectAppendAssociative [] y z = Refl
  vectAppendAssociative (x :: xs) ys zs =
    vectConsCong _ _ _ (vectAppendAssociative xs ys zs)

-- end of local module (namespace) Vect

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

total
vectInjective1 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> x = y
vectInjective1 {x=x} {y=x} {xs=xs} {ys=xs} Refl = Refl

total
vectInjective2 : {xs, ys : Vect n a} -> {x, y : a} -> x :: xs = y :: ys -> xs = ys
vectInjective2 {x=x} {y=x} {xs=xs} {ys=xs} Refl = Refl

{- TODO
instance DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys)   | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (x :: xs) (x :: ys) | Yes Refl | No  neq  = No (neq . vectInjective2)
    decEq (x :: xs) (y :: ys)   | No  neq             = No (neq . vectInjective1)
-}

{- The following definition is elaborated in a wrong case-tree. Examination pending.
instance DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y, decEq xs ys)
    decEq (x :: xs) (x :: xs) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (x :: xs) (y :: ys) | (_, No nEqTl) = No (\p => nEqTl (vectInjective2 p))
    decEq (x :: xs) (y :: ys) | (No nEqHd, _) = No (\p => nEqHd (vectInjective1 p))
-}

-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations.
