module Controls
import Util.VectExtensions1
import DynamicProgramming.S1201_Context

eqeq : Y t x -> Y t x -> Set
eqeqSpec1 : (y : Y t x) -> eqeq y y

isIn : Y t x -> (n : Nat ** Vect n (Y t x)) -> Bool
isIn {t} {x} = VectExtensions1.isIn (Y t x) eqeq eqeqSpec1

lemma3 : (y : Y t x) ->
         (p : Y t x -> Bool) ->
         (ys : (n : Nat ** Vect n (Y t x))) ->
         so (p y) ->
         so (y `isIn` ys) ->
         so (isAnyBy p ys)
lemma3 {t} {x} = VectExtensions1.lemma3 (Y t x) eqeq eqeqSpec1

whole : (n : Nat ** Vect n (Y t x)) -> Type
whole {t} {x} = VectExtensions1.whole (Y t x) eqeq eqeqSpec1 
