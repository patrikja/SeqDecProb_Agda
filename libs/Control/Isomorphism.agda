module Control.Isomorphism where
open import Prelude.Basics
open import Syntax.PreorderReasoning
open import Prelude.Either
import Data.Fin
-- %default total

-- ||| An isomorphism between two types
{-
data Iso : Type -> Type -> Set1 where
  MkIso : {a : Type} -> {b : Type} ->
          (to : a -> b) ->
          (from : b -> a) ->
          (toFrom : (y : b) -> to (from y) == y) ->
          (fromTo : (x : a) -> from (to x) == x) ->
          Iso a b
-}

record Iso (a : Type) (b : Type) : Set1 where
  constructor MkIso
  field
    to : a -> b
    from : b -> a
    toFrom : (y : b) -> to (from y) == y
    fromTo : (x : a) -> from (to x) == x

-- Isomorphism properties

-- ||| Isomorphism is Reflexive
isoRefl : {a : Type} -> Iso a a
isoRefl = MkIso id id (\x -> Refl) (\x -> Refl)


-- ||| Isomorphism is transitive
isoTrans : {a : Type} -> {b : Type} -> {c : Type} ->
           Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso to from toFrom fromTo) (MkIso to' from' toFrom' fromTo') =
  MkIso (\x -> to' (to x))
        (\y -> from (from' y))
        (\y -> (to' (to (from (from' y))))  ==< cong {f = to'} (toFrom (from' y)) >==
               ((to' (from' y))             ==< toFrom' y >==
               y                            QED))
        (\x -> (from (from' (to' (to x))))  ==< cong {f = from} (fromTo' (to x)) >==
              ((from (to x))                ==< fromTo x  >==
               x                            QED) )

-- ||| Isomorphism is symmetric
isoSym : {a : Type} -> {b : Type} ->
         Iso a b -> Iso b a
isoSym (MkIso to from toFrom fromTo) = MkIso from to fromTo toFrom

-- Isomorphisms over sums

-- ||| Disjunction is commutative
eitherComm : {a : Type} -> {b : Type} ->
             Iso (Either a b) (Either b a)
eitherComm = MkIso swap swap swapSwap swapSwap
  where swap : {a : Type} -> {b : Type} ->
               Either a b -> Either b a
        swap (Left x) = Right x
        swap (Right x) = Left x
        swapSwap : {a : Type} -> {b : Type} ->
                   (e : Either a b) -> swap (swap e) == e
        swapSwap (Left x) = Refl
        swapSwap (Right x) = Refl

-- ||| Disjunction is associative
eitherAssoc : {a : Type} -> {b : Type} -> {c : Type} ->
              Iso (Either (Either a b) c) (Either a (Either b c))
eitherAssoc = MkIso eitherAssoc1 eitherAssoc2 ok1 ok2
  where eitherAssoc1 : {a : Type} -> {b : Type} -> {c : Type} ->
                       Either (Either a b) c -> Either a (Either b c)
        eitherAssoc1 (Left (Left x)) = Left x
        eitherAssoc1 (Left (Right x)) = Right (Left x)
        eitherAssoc1 (Right x) = Right (Right x)

        eitherAssoc2 : {a : Type} -> {b : Type} -> {c : Type} ->
                       Either a (Either b c) -> Either (Either a b) c
        eitherAssoc2 (Left x) = Left (Left x)
        eitherAssoc2 (Right (Left x)) = Left (Right x)
        eitherAssoc2 (Right (Right x)) = Right x

        ok1 : {a : Type} -> {b : Type} -> {c : Type} ->
              (x : Either a (Either b c)) -> eitherAssoc1 (eitherAssoc2 x) == x
        ok1 (Left x) = Refl
        ok1 (Right (Left x)) = Refl
        ok1 (Right (Right x)) = Refl

        ok2 : {a : Type} -> {b : Type} -> {c : Type} ->
              (x : Either (Either a b) c) -> eitherAssoc2 (eitherAssoc1 x) == x
        ok2 (Left (Left x)) = Refl
        ok2 (Left (Right x)) = Refl
        ok2 (Right x) = Refl

-- ||| Disjunction with false is a no-op
eitherBotLeft : {a : Type} ->
                Iso (Either Void a) a
eitherBotLeft = MkIso to from ok1 ok2
  where to : {a : Type} ->
             Either Void a -> a
        to (Left x) = void x
        to (Right x) = x
        from : {a : Type} ->
               a -> Either Void a
        from = Right
        ok1 : {a : Type} ->
              (x : a) -> to (from x) == x
        ok1 x = Refl
        ok2 : {a : Type} ->
              (x : Either Void a) -> from (to x) == x
        ok2 (Left x) = void x
        ok2 (Right x) = Refl

-- ||| Disjunction with false is a no-op
eitherBotRight : {a : Type} ->
                 Iso (Either a Void) a
eitherBotRight = isoTrans eitherComm eitherBotLeft

-- ||| Isomorphism is a congruence with regards to disjunction
eitherCong : {a : Type} -> {a' : Type} -> {b : Type} -> {b' : Type} ->
             Iso a a' -> Iso b b' -> Iso (Either a b) (Either a' b')
eitherCong {a = a} {a' = a'} {b = b} {b' = b'}
           (MkIso to from toFrom fromTo)
           (MkIso to' from' toFrom' fromTo') =
  MkIso (eitherMap to to') (eitherMap from from') ok1 ok2
    where eitherMap : {a : Type} -> {a' : Type} -> {b : Type} -> {b' : Type} ->
                      (a -> a') -> (b -> b') -> Either a b -> Either a' b'
          eitherMap f g (Left x)  = Left (f x)
          eitherMap f g (Right x) = Right (g x)
          ok1 : (x : Either a' b') -> eitherMap to to' (eitherMap from from' x) == x
          ok1 (Left x)  = cong {f = Left}  (toFrom x)
          ok1 (Right x) = cong {f = Right} (toFrom' x)
          ok2 : (x : Either a b) -> eitherMap from from' (eitherMap to to' x) == x
          ok2 (Left x)  = cong {f = Left}  (fromTo x)
          ok2 (Right x) = cong {f = Right} (fromTo' x)

-- ||| Isomorphism is a congruence with regards to disjunction on the left
eitherCongLeft : {a : Type} -> {a' : Type} -> {b : Type} -> {b' : Type} ->
                 Iso a a' -> Iso (Either a b) (Either a' b)
eitherCongLeft i = eitherCong i isoRefl

-- ||| Isomorphism is a congruence with regards to disjunction on the right
eitherCongRight : {a : Type} -> {a' : Type} -> {b : Type} -> {b' : Type} ->
                  Iso b b' -> Iso (Either a b) (Either a b')
eitherCongRight i = eitherCong isoRefl i

-- Isomorphisms over products
-- ||| Conjunction is commutative
pairComm : {a : Type} -> {b : Type} ->
           Iso (a × b) (b × a)
pairComm = MkIso swap swap swapSwap swapSwap
  where swap : {a : Type} -> {b : Type} ->
               (a × b) -> (b × a)
        swap (x , y) = (y , x)

        swapSwap : {a : Type} -> {b : Type} ->
                   (x : (a × b)) -> swap (swap x) == x
        swapSwap (x , y) = Refl

{-
-- ||| Conjunction is associative
pairAssoc : Iso (a × (b × c)) ((a × b) × c)
pairAssoc = MkIso to from ok1 ok2
  where
    to : (a × (b × c)) -> ((a × b) × c)
    to (x, (y, z)) = ((x, y), z)
    from : ((a × b) × c) -> (a × (b × c))
    from ((x, y), z) = (x, (y, z))
    ok1 : (x : ((a × b) × c)) -> to (from x) == x
    ok1 ((x, y), z) = Refl
    ok2 : (x : (a × (b × c))) -> from (to x) == x
    ok2 (x, (y, z)) = Refl

-- ||| Conjunction with truth is a no-op
pairUnitRight : Iso (a × ()) a
pairUnitRight = MkIso fst (\x -> (x, ())) (\x -> Refl) ok
  where ok : (x : (a × ())) -> (fst x, ()) == x
        ok (x, ()) = Refl

-- ||| Conjunction with truth is a no-op
pairUnitLeft : Iso (() × a) a
pairUnitLeft = isoTrans pairComm pairUnitRight

-- ||| Conjunction preserves falsehood
pairBotLeft : Iso (Void × a) Void
pairBotLeft = MkIso fst void (\x -> void x) (\y -> void (fst y))

-- ||| Conjunction preserves falsehood
pairBotRight : Iso (a × Void) Void
pairBotRight = isoTrans pairComm pairBotLeft

-- ||| Isomorphism is a congruence with regards to conjunction
pairCong : Iso a a' -> Iso b b' -> Iso (a × b) (a' × b')
pairCong {a = a} {a' = a'} {b = b} {b' = b'}
         (MkIso to from toFrom fromTo)
         (MkIso to' from' toFrom' fromTo') =
  MkIso to'' from'' iso1 iso2
    where to'' : (a × b) -> (a' × b')
          to'' (x, y) = (to x, to' y)
          from'' : (a' × b') -> (a × b)
          from'' (x, y) = (from x, from' y)
          iso1 : (x : (a' × b')) -> to'' (from'' x) == x
          iso1 (x, y) = {! rewrite toFrom x in
                           rewrite toFrom' y in
                           Refl !}
          iso2 : (x : (a × b)) -> from'' (to'' x) == x
          iso2 (x, y) = {! rewrite fromTo x in
                           rewrite fromTo' y in
                           Refl !}

-- ||| Isomorphism is a congruence with regards to conjunction on the left
pairCongLeft : Iso a a' -> Iso (a × b) (a' × b)
pairCongLeft i = pairCong i isoRefl

-- ||| Isomorphism is a congruence with regards to conjunction on the right
pairCongRight : Iso b b' -> Iso (a × b) (a × b')
pairCongRight = pairCong isoRefl

-- Distributivity of products over sums
-- ||| Products distribute over sums
distribLeft : Iso (Either a b × c) (Either (a × c) (b × c))
distribLeft = MkIso to from toFrom fromTo
  where to : (Either a b × c) -> Either (a × c) (b × c)
        to (Left x, y) = Left (x, y)
        to (Right x, y) = Right (x, y)
        from : Either (a × c) (b × c) -> (Either a b × c)
        from (Left (x, y)) = (Left x, y)
        from (Right (x, y)) = (Right x, y)
        toFrom : (x : Either (a × c) (b × c)) -> to (from x) == x
        toFrom (Left (x, y)) = Refl
        toFrom (Right (x, y)) = Refl
        fromTo : (x : (Either a b × c)) -> from (to x) == x
        fromTo (Left x, y) = Refl
        fromTo (Right x, y) = Refl

-- ||| Products distribute over sums
distribRight : Iso (a × Either b c) (Either (a × b) (a × c))
distribRight {a} {b} {c} = (pairComm `isoTrans` distribLeft) `isoTrans` eitherCong pairComm pairComm


-- Enable preorder reasoning syntax over isomorphisms
-- ||| Used for preorder reasoning syntax. Not intended for direct use.
qed : (a : Type) -> Iso a a
qed a = isoRefl

-- ||| Used for preorder reasoning syntax. Not intended for direct use.
step : (a : Type) -> Iso a b -> Iso b c -> Iso a c
step a iso1 iso2 = isoTrans iso1 iso2



-- Isomorphisms over Maybe
-- ||| Isomorphism is a congruence with respect to Maybe
maybeCong : Iso a b -> Iso (Maybe a) (Maybe b)
maybeCong {a} {b} (MkIso to from toFrom fromTo) = MkIso (map to) (map from) ok1 ok2
  where ok1 : (y : Maybe b) -> map to (map from y) == y
        ok1 Nothing = Refl
        ok1 (Just x) = (Just (to (from x))) ={ cong (toFrom x) }= (Just x) QED
        ok2 : (x : Maybe a) -> map from (map to x) == x
        ok2 Nothing = Refl
        ok2 (Just x) = (Just (from (to x))) ={ cong (fromTo x) }= (Just x) QED

-- ||| `Maybe a` is the same as `Either a ()`
maybeEither : Iso (Maybe a) (Either a ())
maybeEither = MkIso to from iso1 iso2
  where to : Maybe a -> Either a ()
        to Nothing  = Right ()
        to (Just x) = Left x
        from : Either a () -> Maybe a
        from (Left x)   = Just x
        from (Right ()) = Nothing
        iso1 : (x : Either a ()) -> to (from x) == x
        iso1 (Left x) = Refl
        iso1 (Right ()) = Refl
        iso2 : (y : Maybe a) -> from (to y) == y
        iso2 Nothing = Refl
        iso2 (Just x) = Refl

-- ||| Maybe of void is just unit
maybeVoidUnit : Iso (Maybe Void) ()
maybeVoidUnit = (Maybe Void)     ={ maybeEither   }=
                (Either Void ()) ={ eitherBotLeft }=
                ()              QED

eitherMaybeLeftMaybe : Iso (Either (Maybe a) b) (Maybe (Either a b))
eitherMaybeLeftMaybe {a} {b} =
  (Either (Maybe a) b)     ={ eitherCongLeft maybeEither }=
  (Either (Either a ()) b) ={ eitherAssoc                }=
  (Either a (Either () b)) ={ eitherCongRight eitherComm }=
  (Either a (Either b ())) ={ isoSym eitherAssoc         }=
  (Either (Either a b) ()) ={ isoSym maybeEither         }=
  (Maybe (Either a b))     QED


eitherMaybeRightMaybe : Iso (Either a (Maybe b)) (Maybe (Either a b))
eitherMaybeRightMaybe {a} {b} =
  (Either a (Maybe b)) ={ eitherComm           }=
  (Either (Maybe b) a) ={ eitherMaybeLeftMaybe }=
  (Maybe (Either b a)) ={ maybeCong eitherComm }=
  (Maybe (Either a b)) QED


-- Isomorphisms over Fin

maybeIsoS : Iso (Maybe (Fin n)) (Fin (S n))
maybeIsoS = MkIso forth back fb bf
  where forth : Maybe (Fin n) -> Fin (S n)
        forth Nothing = FZ
        forth (Just x) = FS x
        back : Fin (S n) -> Maybe (Fin n)
        back FZ = Nothing
        back (FS x) = Just x
        bf : (x : Maybe (Fin n)) -> back (forth x) == x
        bf Nothing = Refl
        bf (Just x) = Refl
        fb : (y : Fin (S n)) -> forth (back y) == y
        fb FZ = Refl
        fb (FS x) = Refl

finZeroBot : Iso (Fin 0) Void
finZeroBot = MkIso (\x -> void (uninhabited x))
                   (\x -> void x)
                   (\x -> void x)
                   (\x -> void (uninhabited x))

eitherFinPlus : Iso (Either (Fin m) (Fin n)) (Fin (m + n))
eitherFinPlus {m = Z} {n=n} =
  (Either (Fin 0) (Fin n)) ={ eitherCongLeft finZeroBot }=
  (Either Void (Fin n))     ={ eitherBotLeft             }=
  (Fin n)                  QED
eitherFinPlus {m = S k} {n=n} =
  (Either (Fin (S k)) (Fin n))     ={ eitherCongLeft (isoSym maybeIsoS) }=
  (Either (Maybe (Fin k)) (Fin n)) ={ eitherMaybeLeftMaybe              }=
  (Maybe (Either (Fin k) (Fin n))) ={ maybeCong eitherFinPlus           }=
  (Maybe (Fin (k + n)))            ={ maybeIsoS                         }=
  (Fin (S (k + n)))                QED


finPairTimes : Iso (Fin m × Fin n) (Fin (m * n))
finPairTimes {m = Z} {n=n} =
  (Fin Z, Fin n) ={ pairCongLeft finZeroBot }=
  (Void, Fin n)   ={ pairBotLeft             }=
  Void            ={ isoSym finZeroBot       }=
  (Fin Z)        QED
finPairTimes {m = S k} {n=n} =
  (Fin (S k), Fin n)                  ={ pairCongLeft (isoSym maybeIsoS)      }=
  (Maybe (Fin k), Fin n)              ={ pairCongLeft maybeEither             }=
  (Either (Fin k) (), Fin n)          ={ distribLeft                          }=
  (Either (Fin k, Fin n) ((), Fin n)) ={ eitherCong finPairTimes pairUnitLeft }=
  (Either (Fin (k * n)) (Fin n))      ={ eitherComm                           }=
  (Either (Fin n) (Fin (k * n)))      ={ eitherFinPlus                        }=
  (Fin (n + (k * n)))                 QED
-}
