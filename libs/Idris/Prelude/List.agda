module Idris.Prelude.List where

open import Idris.Builtins

-- import Idris.Prelude.Algebra
open import Idris.Prelude.Basics
open import Idris.Prelude.Bool
open import Idris.Prelude.Classes
-- import Idris.Prelude.Foldable
-- import Idris.Prelude.Functor
open import Idris.Prelude.Maybe
open import Idris.Prelude.Nat

-- %access public
-- %default total

-- infix 5 _\\_
infixr 7 _::_
infixr 7 _++_

-- ||| Linked lists
data List (a : Type) : Type where
  -- ||| The empty list
  [] : List a
  -- ||| Cons cell
  _::_ : a -> List a -> List a

Nil : {a : Type} -> List a
Nil = []

-- Name hints for interactive editing
-- %name List xs, ys, zs, ws

--------------------------------------------------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

-- ||| Returns `True` iff the argument is empty
isNil : {a : Type} ->
        List a -> Bool
isNil []      = True
isNil (x::xs) = False

-- ||| Returns `True` iff the argument is not empty
isCons : {a : Type} ->
         List a -> Bool
isCons []      = False
isCons (x::xs) = True

--------------------------------------------------------------------------------
-- Length
--------------------------------------------------------------------------------

-- ||| Compute the length of a list.
-- |||
-- ||| Runs in linear time
length : {a : Type} ->
         List a -> Nat
length []      = 0
length (x :: xs) = 1 + length xs

--------------------------------------------------------------------------------
-- Indexing into lists
--------------------------------------------------------------------------------

-- ||| Find a particular element of a list.
-- |||
-- ||| @ ok a proof that the index is within bounds
index : {a : Type} ->
        (n : Nat) -> (l : List a) -> (ok : lt n (length l) == True) -> a
index Z     (x :: xs) p    = x
index (S n) (x :: xs) p    = index n xs p
index n     []        ()



-- ||| Attempt to find a particular element of a list.
-- |||
-- ||| If the provided index is out of bounds, return Nothing.
index' : {a : Type} ->
         (n : Nat) -> (l : List a) -> Maybe a
index' Z     (x :: xs) = Just x
index' (S n) (x :: xs) = index' n xs
index' _     []        = Nothing


-- ||| Get the first element of a non-empty list
-- ||| @ ok proof that the list is non-empty
head : {a : Type} ->
       (l : List a) -> {ok : isCons l == True} -> a
head []         {ok = ()}
head (x :: xs)  {ok = p}    = x


-- ||| Attempt to get the first element of a list. If the list is empty, return
-- ||| `Nothing`.
head' : {a : Type} ->
        (l : List a) -> Maybe a
head' []        = Nothing
head' (x :: xs) = Just x


-- ||| Get the tail of a non-empty list.
-- ||| @ ok proof that the list is non-empty
tail : {a : Type} ->
       (l : List a) -> {ok : isCons l == True} -> List a
tail []        {ok = ()}
tail (x :: xs) {ok = p}    = xs


-- ||| Attempt to get the tail of a list.
-- |||
-- ||| If the list is empty, return `Nothing`.
tail' : {a : Type} ->
        (l : List a) -> Maybe (List a)
tail' []        = Nothing
tail' (x :: xs) = Just xs

-- ||| Retrieve the last element of a non-empty list.
-- ||| @ ok proof that the list is non-empty
last : {a : Type} ->
       (l : List a) -> {ok : isCons l == True} -> a
last []              {ok = ()}
last ( x :: [])      {ok = p}    = x
last ( x :: y :: ys) {ok = p}    = last (y :: ys) {ok = Refl}


-- ||| Attempt to retrieve the last element of a non-empty list.
-- |||
-- ||| If the list is empty, return `Nothing`.
last' : {a : Type} ->
        (l : List a) -> Maybe a
last' []        = Nothing
last' (x :: []) = Just x
last' (x :: xs) = last' xs

-- ||| Return all but the last element of a non-empty list.
-- ||| @ ok proof that the list is non-empty
init : {a : Type} ->
       (l : List a) -> {ok : isCons l == True} -> List a
init []             {ok = ()}
init (x :: [])      {ok = p}    = []
init (x :: y :: ys) {ok = p}    = x :: init (y :: ys) {ok = Refl}

-- ||| Attempt to Return all but the last element of a list.
-- |||
-- ||| If the list is empty, return `Nothing`.
init' : {a : Type} ->
        (l : List a) -> Maybe (List a)
init' []        = Nothing
init' (x :: []) = Just []
init' (x :: xs) with init' xs
... | Nothing = Nothing
... | Just j  = Just (x :: j)

--------------------------------------------------------------------------------
-- Sublists
--------------------------------------------------------------------------------

-- ||| Take the first `n` elements of `xs`
-- |||
-- ||| If there are not enough elements, return the whole list.
-- ||| @ n how many elements to take
-- ||| @ xs the list to take them from
take : {a : Type} ->
       (n : Nat) -> (xs : List a) -> List a
take Z     xs        = []
take (S n) []        = []
take (S n) (x :: xs) = x :: take n xs

-- ||| Drop the first `n` elements of `xs`
-- |||
-- ||| If there are not enough elements, return the empty list.
-- ||| @ n how many elements to drop
-- ||| @ xs the list to drop them from
drop : {a : Type} ->
       (n : Nat) -> (xs : List a) -> List a
drop Z     xs      = xs
drop (S n) []      = []
drop (S n) (x :: xs) = drop n xs

-- ||| Take the longest prefix of a list such that all elements satisfy some
-- ||| Boolean predicate.
-- |||
-- ||| @ p the predicate
takeWhile : {a : Type} ->
            (p : a -> Bool) -> List a -> List a
takeWhile p []        = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

-- ||| Remove the longest prefix of a list such that all removed elements satisfy some
-- ||| Boolean predicate.
-- |||
-- ||| @ p the predicate
dropWhile : {a : Type} ->
            (p : a -> Bool) -> List a -> List a
dropWhile p []      = []
dropWhile p (x :: xs) = if p x then dropWhile p xs else (x :: xs)

--------------------------------------------------------------------------------
-- Misc.
--------------------------------------------------------------------------------

-- ||| Simply-typed recursion operator for lists.
-- |||
-- ||| @ nil what to return at the end of the list
-- ||| @ cons what to do at each step of recursion
-- ||| @ xs the list to recurse over
list : {a : Type} -> {b : Type} ->
       (nil : Lazy b) -> (cons : Lazy (a -> List a -> b)) -> (xs : List a) -> b
list nil cons []        = nil
list nil cons (x :: xs) = (Force cons) x xs

--------------------------------------------------------------------------------
-- Building (bigger) lists
--------------------------------------------------------------------------------

-- ||| Append two lists
_++_ : {a : Type} ->
       List a -> List a -> List a
_++_ []        right = right
_++_ (x :: xs) right = x :: (xs ++ right)

-- ||| Construct a list with `n` copies of `x`
-- ||| @ n how many copies
-- ||| @ x the element to replicate
replicate : {a : Type} ->
            (n : Nat) -> (x : a) -> List a
replicate Z     x = []
replicate (S n) x = x :: replicate n x

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------
eqList : {a : Type} -> EqDict a -> EqDict' (List a)
eqList eqa []        []        = True
eqList eqa []        (x :: ys) = False
eqList eqa (x :: xs) []        = False
eqList eqa (x :: xs) (y :: ys) = if x === y then eqList eqa xs ys else False
  where open EqDict eqa

eqDictList : {a : Type} -> EqDict a -> EqDict (List a)
eqDictList eqa = record {_===_ = eqList eqa}

compareList : {a : Type} -> OrdDict a -> OrdDict' (List a)
compareList orda [] [] = Ordering.EQ
compareList orda [] _ = Ordering.LT
compareList orda _ [] = Ordering.GT
compareList orda (x :: xs) (y :: ys) =
    if (x /= y) then  compare x y
    else              compareList orda xs ys
  where open OrdDict orda

ordDictList : {a : Type} -> OrdDict a -> OrdDict (List a)
ordDictList orda = record {eqDict = eqDictList eqDict; compare = compareList orda}
  where open OrdDict orda

-- instance Ord a => Ord (List a) where

{- TODOinst
instance Semigroup (List a) where
  (<+>) = (++)

instance Monoid (List a) where
  neutral = []

instance Functor List where

-}

map : {a : Type} -> {b : Type} ->
      (a -> b) -> List a -> List b
map f []        = []
map f (x :: xs) = f x :: map f xs



--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------


-- ||| Combine two lists of the same length elementwise using some function.
-- ||| @ f the function to combine elements with
-- ||| @ l the first list
-- ||| @ r the second list
-- ||| @ ok a proof that the lengths of the inputs are equal
zipWith : {a : Type} -> {b : Type} -> {c : Type} ->
          (f : a -> b -> c) -> (l : List a) -> (r : List b) ->
  (ok : length l == length r) -> List c
zipWith f []        (y :: ys) ()
zipWith f (x :: xs) []        ()
zipWith f []        []        p    = []
zipWith f (x :: xs) (y :: ys) p    = f x y :: (zipWith f xs ys zipWithTailProof)
  where  zipWithTailProof = succInjective (length xs) (length ys) p


-- ||| Combine three lists of the same length elementwise using some function.
-- ||| @ f the function to combine elements with
-- ||| @ x the first list
-- ||| @ y the second list
-- ||| @ z the third list
-- ||| @ ok a proof that the lengths of the first two inputs are equal
-- ||| @ ok' a proof that the lengths of the second and third inputs are equal
zipWith3 : {a : Type} -> {b : Type} -> {c : Type} -> {d : Type} ->
           (f : a -> b -> c -> d) ->
           (x : List a) -> (y : List b) -> (z : List c) ->
           (ok : length x == length y) ->
           (ok' : length y == length z) -> List d
zipWith3 f x         []        (z :: zs) p    ()
zipWith3 f _         (y :: ys) []        p    ()
zipWith3 f []        (y :: ys) _         ()   q
zipWith3 f (x :: xs) []        _         ()   q
zipWith3 f []        []        []        p    q    = []
zipWith3 f (x :: xs) (y :: ys) (z :: zs) p    q    =
  f x y z :: (zipWith3 f xs ys zs zipWith3TailProof zipWith3TailProof')
    where zipWith3TailProof  = succInjective (length xs) (length ys) p
          zipWith3TailProof' = succInjective (length ys) (length zs) q

-- ||| Combine two lists elementwise into pairs
zip : {a : Type} -> {b : Type} ->
      (l : List a) -> (r : List b) -> (length l == length r) -> List (a × b)
zip = zipWith (\x y -> (x , y))

-- ||| Combine three lists elementwise into tuples
zip3 : {a : Type} -> {b : Type} -> {c : Type} ->
       (x : List a) -> (y : List b) -> (z : List c) ->
       (length x == length y) -> (length y == length z) -> List (a × b × c)
zip3 = zipWith3 (\x y z -> (x , y , z))

-- ||| Split a list of pairs into two lists
unzip : {a : Type} -> {b : Type} ->
        List (a × b) -> (List a × List b)
unzip []           = ([] , [])
unzip ((l , r) :: xs) with (unzip xs)
... | (lefts , rights) = (l :: lefts , r :: rights)


-- ||| Split a list of triples into three lists
unzip3 : {a : Type} -> {b : Type} -> {c : Type} ->
         List (a × b × c) -> (List a × List b × List c)
unzip3 []              = ([] , [] , [])
unzip3 ((l , c , r) :: xs) with (unzip3 xs)
...  | (lefts , centres , rights) = (l :: lefts , c :: centres , r :: rights)

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

-- ||| Apply a partial function to the elements of a list, keeping the ones at which
-- ||| it is defined.
mapMaybe : {a : Type} -> {b : Type} ->
           (a -> Maybe b) -> List a -> List b
mapMaybe f []      = []
mapMaybe f (x :: xs) with f x
... | Nothing = mapMaybe f xs
... | Just j  = j :: mapMaybe f xs


--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

-- ||| A tail recursive right fold on Lists.
foldrImpl : {t : Type} -> {acc : Type} ->
            (t -> acc -> acc) -> acc -> (acc -> acc) -> List t -> acc
foldrImpl f e go [] = go e
foldrImpl f e go (x :: xs) = foldrImpl f e (go ∘ (f x)) xs
{-
instance Foldable List where
-}
foldr : {t : Type} -> {acc : Type} ->
        (t -> acc -> acc) -> acc -> List t -> acc
foldr f e xs = foldrImpl f e id xs

-- concat : (Foldable t, Monoid a) => t a -> a
concat : {a : Type} ->
         List (List a) -> List a
concat = foldr _++_ []

foldl : {acc : Type} -> {elt : Type} ->
        (acc -> elt -> acc) -> acc -> List elt -> acc
foldl f z t = foldr (flip _∘_ ∘ flip f) id t z


--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

{- TODO
-- ||| Convert any Foldable structure to a list.
toList : Foldable t => t a -> List a
toList = foldr _::_ []
-}


--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

-- ||| Return the elements of a list in reverse order.
reverse : {a : Type} ->
          List a -> List a
reverse = reverse' []
  where
    reverse' : {a : Type} ->
               List a -> List a -> List a
    reverse' acc []        = acc
    reverse' acc (x :: xs) = reverse' (x :: acc) xs

-- ||| Insert some separator between the elements of a list.
-- |||
-- ||| ````idris example
-- ||| with List (intersperse ',' ['a', 'b', 'c', 'd', 'e'])
-- ||| ````
-- |||
intersperse : {a : Type} ->
              a -> List a -> List a
intersperse sep []        = []
intersperse sep (x :: xs) = x :: intersperse' sep xs
  where
    intersperse' : {a : Type} ->
                   a -> List a -> List a
    intersperse' sep []        = []
    intersperse' sep (y :: ys) = sep :: y :: intersperse' sep ys

intercalate : {a : Type} ->
              List a -> List (List a) -> List a
intercalate sep l = concat (intersperse sep l)

-- ||| Transposes rows and columns of a list of lists.
-- |||
-- ||| ```idris example
-- ||| with List transpose [[1, 2], [3, 4]]
-- ||| ```
-- |||
-- ||| This also works for non square scenarios, thus
-- ||| involution does not always hold:
-- |||
-- |||     transpose [[], [1, 2]] = [[1], [2]]
-- |||     transpose (transpose [[], [1, 2]]) = [[1, 2]]
-- |||

{-
-- ||| TODO: Solution which satisfies the totality checker?
-- %assert_total
transpose : {a : Type} ->
            List (List a) -> List (List a)
transpose [] = []
transpose ([] :: xss) = transpose xss
transpose ((x :: xs) :: xss) = (x :: (mapMaybe head' xss)) :: (transpose (xs :: (map (drop 1) xss)))
-}

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

-- ||| Check if something is a member of a list using a custom comparison.
elemBy : {a : Type} ->
         (a -> a -> Bool) -> a -> List a -> Bool
elemBy p e []        = False
elemBy p e (x :: xs) =
  if p e x then
    True
  else
    elemBy p e xs

-- ||| Check if something is a member of a list using the default Boolean equality.

elem : {a : Type} -> {{eqd : EqDict a}} -> a -> List a -> Bool
elem {a} {{eqd}} = elemBy _===_
  where open EqDict eqd

-- ||| Find associated information in a list using a custom comparison.
lookupBy : {a : Type} -> {b : Type} ->
           (a -> a -> Bool) -> a -> List (a × b) -> Maybe b
lookupBy p e []      = Nothing
lookupBy p e ((l , r) :: xs) =
    if p e l then
      Just r
    else
      lookupBy p e xs

-- ||| Find associated information in a list using Boolean equality.

lookup : {a b : Type} -> {{eqd : EqDict a}} -> a -> List (a × b) -> Maybe b
lookup {a} {b} {{eqd}} = lookupBy _===_
  where open EqDict eqd


-- ||| Check if any elements of the first list are found in the second, using
-- ||| a custom comparison.
hasAnyBy : {a : Type} ->
           (a -> a -> Bool) -> List a -> List a -> Bool
hasAnyBy p elems []        = False
hasAnyBy p elems (x :: xs) =
  if elemBy p x elems then
    True
  else
    hasAnyBy p elems xs


-- ||| Check if any elements of the first list are found in the second, using
-- ||| Boolean equality.

hasAny : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a -> Bool
hasAny {a} {{eqd}} = hasAnyBy _===_
  where open EqDict eqd


--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

-- ||| Find the first element of a list that satisfies a predicate, or `Nothing` if none do.
find : {a : Type} ->
       (a -> Bool) -> List a -> Maybe a
find p []        = Nothing
find p (x :: xs) =
  if p x then
    Just x
  else
    find p xs

-- ||| Find the index of the first element of a list that satisfies a predicate, or
-- ||| `Nothing` if none do.
findIndex : {a : Type} ->
            (a -> Bool) -> List a -> Maybe Nat
findIndex = findIndex' Z
  where
    findIndex' : {a : Type} ->
                 Nat -> (a -> Bool) -> List a -> Maybe Nat
    findIndex' cnt p []        = Nothing
    findIndex' cnt p (x :: xs) =
      if p x then
        Just cnt
      else
        findIndex' (S cnt) p xs

-- ||| Find the indices of all elements that satisfy some predicate.
findIndices : {a : Type} ->
              (a -> Bool) -> List a -> List Nat
findIndices = findIndices' Z
  where
    findIndices' : {a : Type} ->
                   Nat -> (a -> Bool) -> List a -> List Nat
    findIndices' cnt p []      = []
    findIndices' cnt p (x :: xs) =
      if p x then
        cnt :: findIndices' (S cnt) p xs
      else
        findIndices' (S cnt) p xs

elemIndexBy : {a : Type} ->
              (a -> a -> Bool) -> a -> List a -> Maybe Nat
elemIndexBy p e = findIndex (p e)


elemIndex : {a : Type} -> {{eqd : EqDict a}} -> a -> List a -> Maybe Nat
elemIndex {a} {{eqd}} = elemIndexBy _===_
  where open EqDict eqd


elemIndicesBy : {a : Type} ->
                (a -> a -> Bool) -> a -> List a -> List Nat
elemIndicesBy p e = findIndices (p e)


elemIndices : {a : Type} -> {{eqd : EqDict a}} -> a -> List a -> List Nat
elemIndices {a} {{eqd}} = elemIndicesBy _===_
  where open EqDict eqd


--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

-- ||| filter, applied to a predicate and a list, returns the list of those elements that satisfy the predicate; e.g.,
-- |||
-- ||| ````idris example
-- ||| filter (< 3) [Z, S Z, S (S Z), S (S (S Z)), S (S (S (S Z)))]
-- ||| ````
-- |||
filter : {a : Type} ->
         (a -> Bool) -> List a -> List a
filter p []        = []
filter p (x :: xs) =
  if p x then
    x :: filter p xs
  else
    filter p xs

-- ||| The nubBy function behaves just like nub, except it uses a user-supplied equality predicate instead of the overloaded == function.
nubBy : {a : Type} ->
        (a -> a -> Bool) -> List a -> List a
nubBy = nubBy' []
  where
    nubBy' : {a : Type} ->
             List a -> (a -> a -> Bool) -> List a -> List a
    nubBy' acc p []        = []
    nubBy' acc p (x :: xs) =
      if elemBy p x acc then
        nubBy' acc p xs
      else
        (x :: nubBy' (x :: acc) p xs)

-- ||| O(n^2). The nub function removes duplicate elements from a list. In
-- ||| particular, it keeps only the first occurrence of each element. It is a
-- ||| special case of nubBy, which allows the programmer to supply their own
-- ||| equality test.
-- |||
-- ||| ```idris example
-- ||| nub (the (List _) [1,2,1,3])
-- ||| ```

nub : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a
nub {a} {{eqd}} = nubBy _===_
  where open EqDict eqd


-- ||| The deleteBy function behaves like delete, but takes a user-supplied equality predicate.
deleteBy : {a : Type} ->
           (a -> a -> Bool) -> a -> List a -> List a
deleteBy _  _ []        = []
deleteBy eq x (y :: ys) = if eq x y then ys else (y :: deleteBy eq x ys)

-- ||| `delete x` removes the first occurrence of `x` from its list argument. For
-- ||| example,
-- |||
-- |||````idris example
-- |||delete 'a' ['b', 'a', 'n', 'a', 'n', 'a']
-- |||````
-- |||
-- ||| It is a special case of deleteBy, which allows the programmer to supply
-- ||| their own equality test.

delete : {a : Type} -> {{eqd : EqDict a}} -> a -> List a -> List a
delete {a} {{eqd}} = deleteBy _===_
  where open EqDict eqd


-- ||| The `\\` function is list difference (non-associative). In the result of
-- ||| `xs \\ ys`, the first occurrence of each element of ys in turn (if any) has
-- ||| been removed from `xs`, e.g.,
-- |||
-- ||| ```idris example
-- ||| (([1,2] ++ [2,3]) \\ [1,2])
-- ||| ```
_\\_ : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a -> List a
_\\_ =  foldl (flip delete)


unionBy : {a : Type} ->
          (a -> a -> Bool) -> List a -> List a -> List a
unionBy eq xs ys =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

-- ||| The union function returns the list union of the two lists. For example,
-- |||
-- ||| ```idris example
-- ||| union ['d', 'o', 'g'] ['c', 'o', 'w']
-- ||| ```
-- |||

union : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a -> List a
union {a} {{eqd}} = unionBy _===_
  where open EqDict eqd


--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

-- ||| Given a list and a predicate, returns a pair consisting of the longest
-- ||| prefix of the list that satisfies a predicate and the rest of the list.
-- |||
-- ||| ```idris example
-- ||| span (<3) [1,2,3,2,1]
-- ||| ```
span : {a : Type} ->
       (a -> Bool) -> List a -> (List a × List a)
span p []      = ([] , [])
span p (x :: xs) =
  if p x then
    (let (ys , zs) = span p xs in
      (x :: ys , zs))
  else
    ([] , x :: xs)

-- ||| Given a list and a predicate, returns a pair consisting of the longest
-- ||| prefix of the list that does not satisfy a predicate and the rest of the
-- ||| list.
-- |||
-- ||| ```idris example
-- ||| break (>=3) [1,2,3,2,1]
-- ||| ```
break : {a : Type} ->
        (a -> Bool) -> List a -> (List a × List a)
break p = span (not ∘ p)

-- ||| Split on any elements that satisfy the given predicate.
-- |||
-- ||| ```idris example
-- ||| split (<2) [2,0,3,1,4]
-- ||| ```
{- TODO termination
split : {a : Type} ->
        (a -> Bool) -> List a -> List (List a)
split p xs with break p xs
... | (chunk , [])          = chunk :: []
... | (chunk , (c :: rest)) = chunk :: split p rest
-}

-- ||| A tuple where the first element is a List of the n first elements and
-- ||| the second element is a List of the remaining elements of the list
-- ||| It is equivalent to (take n xs, drop n xs)
-- ||| @ n   the index to split at
-- ||| @ xs  the list to split in two
splitAt : {a : Type} ->
          (n : Nat) -> (xs : List a) -> (List a × List a)
splitAt n xs = (take n xs , drop n xs)

-- ||| The partition function takes a predicate a list and returns the pair of lists of elements which do and do not satisfy the predicate, respectively; e.g.,
-- |||
-- ||| ```idris example
-- ||| partition (<3) [0, 1, 2, 3, 4, 5]
-- ||| ```
partition : {a : Type} ->
            (a -> Bool) -> List a -> (List a × List a)
partition p []        = ([] , [])
partition p (x :: xs) =
  let (lefts , rights) = partition p xs in
    if p x then
      (x :: lefts , rights)
    else
      (lefts , x :: rights)

-- ||| The inits function returns all initial segments of the argument, shortest
-- ||| first. For example,
-- |||
-- ||| ```idris example
-- ||| inits [1,2,3]
-- ||| ```

inits : {a : Type} ->
        List a -> List (List a)
inits []         = [] :: []
inits (x :: xs') = map (_::_ x) (inits xs')


-- ||| The tails function returns all final segments of the argument, longest
-- ||| first. For example,
-- |||
-- ||| ```idris example
-- ||| tails [1,2,3] == [[1,2,3], [2,3], [3], []]
-- |||```
mutual
  tails : {a : Type} ->
          List a -> List (List a)
  tails xs = xs :: tailshelp xs

  tailshelp : {a : Type} ->
              List a -> List (List a)
  tailshelp []          = []
  tailshelp (_ :: xs')  = tails xs'


-- ||| Split on the given element.
-- |||
-- ||| ```idris example
-- ||| splitOn 0 [1,0,2,0,0,3]
-- ||| ```
-- |||
{- TODO termination for split (above)
splitOn : {a : Type} -> {{eqd : EqDict a}} -> a -> List a -> List (List a)
splitOn {{eqd}} a = split (_===_ a)
  where open EqDict eqd
-}


-- ||| Replaces all occurences of the first argument with the second argument in a list.
-- |||
-- ||| ```idris example
-- ||| replaceOn '-' ',' ['1', '-', '2', '-', '3']
-- ||| ```
-- |||

replaceOn : {a : Type} -> {{eqd : EqDict a}} -> a -> a -> List a -> List a
replaceOn {{eqd}} a b l = map (\c -> if c === a then b else c) l
  where open EqDict eqd



--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

isPrefixOfBy : {a : Type} ->
               (a -> a -> Bool) -> List a -> List a -> Bool
isPrefixOfBy p [] right            = True
isPrefixOfBy p left []             = False
isPrefixOfBy p (x :: xs) (y :: ys) =
  if p x y then
    isPrefixOfBy p xs ys
  else
    False


-- ||| The isPrefixOf function takes two lists and returns True iff the first list is a prefix of the second.

isPrefixOf : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a -> Bool
isPrefixOf {{eqd}} = isPrefixOfBy _===_
  where open EqDict eqd



isSuffixOfBy : {a : Type} ->
               (a -> a -> Bool) -> List a -> List a -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)


-- ||| The isSuffixOf function takes two lists and returns True iff the first list is a suffix of the second.

isSuffixOf : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a -> Bool
isSuffixOf {{eqd}} = isSuffixOfBy _===_
  where open EqDict eqd



-- ||| The isInfixOf function takes two lists and returns True iff the first list is contained, wholly and intact, anywhere within the second.
-- |||
-- ||| ```idris example
-- ||| isInfixOf ['b','c'] ['a', 'b', 'c', 'd']
-- ||| ```
-- ||| ```idris example
-- ||| isInfixOf ['b','d'] ['a', 'b', 'c', 'd']
-- ||| ```
-- |||
{- TODO  missing Foldable.agda
isInfixOf : {a : Type} -> {{eqd : EqDict a}} -> List a -> List a -> Bool
isInfixOf n h = any (isPrefixOf n) (tails h)
-}


--------------------------------------------------------------------------------
-- Sorting
--------------------------------------------------------------------------------


sorted : {a : Type} -> {{ordd : OrdDict a}} -> List a -> Bool
sorted          []              = True
sorted          (x :: [])       = True
sorted {{ordd}} (x :: y :: ys)  = x <= y && sorted (y :: ys)
  where open OrdDict ordd


mergeBy : {a : Type} ->
          (a -> a -> Ordering) -> List a -> List a -> List a
mergeBy order []        right     = right
mergeBy order left      []        = left
mergeBy order (x :: xs) (y :: ys) with order x y
... | Ordering.LT = x :: mergeBy order xs (y :: ys)
... | _           = y :: mergeBy order (x :: xs) ys

merge : {a : Type} -> {{ordd : OrdDict a}} -> List a -> List a -> List a
merge {{ordd}} = mergeBy compare
  where open OrdDict ordd


{-# NO_TERMINATION_CHECK #-}
sort : {a : Type} -> {{ordd : OrdDict a}} -> List a -> List a
sort []         = []
sort (x :: [])  = x :: []
sort {a} xs     = let (x , y) = split xs in merge (sort x) (sort y)
  where
    splitRec : List a -> List a -> (List a -> List a) -> (List a × List a)
    splitRec (_ :: _ :: xs) (y :: ys) zs = splitRec xs ys (zs ∘ (_::_ y))
    splitRec  _              ys       zs = (zs [] , ys)

    split : List a -> (List a × List a)
    split xs = splitRec xs xs id

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

-- ||| Either return the head of a list, or `Nothing` if it is empty.
listToMaybe : {a : Type} ->
              List a -> Maybe a
listToMaybe []        = Nothing
listToMaybe (x :: xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

catMaybes : {a : Type} ->
            List (Maybe a) -> List a
catMaybes []      = []
catMaybes (Nothing :: xs) =      catMaybes xs
catMaybes (Just j  :: xs) = j :: catMaybes xs

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- ||| The empty list is a right identity for append.
appendNilRightNeutral : {a : Type} ->
                        (l : List a) ->
  l ++ [] == l
appendNilRightNeutral []        = Refl
appendNilRightNeutral (x :: xs) =
  let inductiveHypothesis = appendNilRightNeutral xs in
    cong (_::_ x) inductiveHypothesis

-- ||| Appending lists is associative.
appendAssociative : {a : Type} ->
                    (l : List a) -> (c : List a) -> (r : List a) ->
  l ++ (c ++ r) == (l ++ c) ++ r
appendAssociative []        c r = Refl
appendAssociative (x :: xs) c r =
  let inductiveHypothesis = appendAssociative xs c r in
    cong (_::_ x) inductiveHypothesis

-- ||| The length of two lists that are appended is the sum of the lengths
-- ||| of the input lists.
lengthAppend : {a : Type} ->
               (left : List a) -> (right : List a) ->
  length (left ++ right) == length left + length right
lengthAppend []        right = Refl
lengthAppend (x :: xs) right =
  let inductiveHypothesis = lengthAppend xs right in
    cong S inductiveHypothesis

-- ||| Mapping a function over a list doesn't change its length.
mapPreservesLength : {a : Type} -> {b : Type} ->
                     (f : a -> b) -> (l : List a) ->
  length (map f l) == length l
mapPreservesLength f []        = Refl
mapPreservesLength f (x :: xs) =
  let inductiveHypothesis = mapPreservesLength f xs in
    cong (_+_ 1) inductiveHypothesis

-- ||| Mapping a function over two lists and appending them is equivalent
-- ||| to appending them and then mapping the function.
mapDistributesOverAppend : {a : Type} -> {b : Type} ->
                           (f : a -> b) -> (l : List a) -> (r : List a) ->
  map f (l ++ r) == map f l ++ map f r
mapDistributesOverAppend f []        r = Refl
mapDistributesOverAppend f (x :: xs) r =
  let inductiveHypothesis = mapDistributesOverAppend f xs r in
    cong (_::_ (f x)) inductiveHypothesis

-- ||| Mapping two functions is the same as mapping their composition.
mapFusion : {a : Type} -> {b : Type} -> {c : Type} ->
            (f : b -> c) -> (g : a -> b) -> (l : List a) ->
  map f (map g l) == map (f ∘ g) l
mapFusion f g []        = Refl
mapFusion f g (x :: xs) =
  let inductiveHypothesis = mapFusion f g xs in
    cong (_::_ (f (g x))) inductiveHypothesis

-- ||| No list contains an element of the empty list by any predicate.
hasAnyByNilFalse : {a : Type} ->
                   (p : a -> a -> Bool) -> (l : List a) ->
  hasAnyBy p [] l == False
hasAnyByNilFalse p []        = Refl
hasAnyByNilFalse p (x :: xs) = hasAnyByNilFalse p xs


-- ||| No list contains an element of the empty list.
hasAnyNilFalse : {a : Type} -> {{eqd : EqDict a}} -> (l : List a) -> hasAny [] l == False
hasAnyNilFalse []        = Refl
hasAnyNilFalse (x :: xs) = hasAnyNilFalse xs

{- TODOinst
instance VerifiedSemigroup (List a) where
  semigroupOpIsAssociative = appendAssociative

instance VerifiedMonoid (List a) where
  monoidNeutralIsNeutralL = appendNilRightNeutral
  monoidNeutralIsNeutralR xs = Refl
-}
