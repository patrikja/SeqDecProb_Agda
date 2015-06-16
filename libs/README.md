A port to Agda of a small subset of the Idris libraries distributed
with the Idris compiler.

Aim: make it easy to check Idris-code with Agda (and to improve both
the Idris and the Agda libraries by comparing and contrasting).

This directory contains a libs from both "base" and "prelude".

TODO: It might be easier to add syntax compatibility layers to Agda or
Idris instead of doing this by hand.

(This code is derived from the
[Idris-dev git-repo](https://github.com/idris-lang/Idris-dev) with the
following [License](Idris/LICENSE).)

Some differences:

| Idris | Agda | Comment |
| ----- | ---- | ------- |
| \ =>  | \ -> |         |
| (.)   | _∘_  | The period is a reserved character in Agda. I follow the agda-stdlib and use the unicode RING OPERATOR here. (An alternative would be the middle dot which on my keyboard is AltGr-.) |
| Implicitly implicit lower case arguments | Explicitly implicit arguments! |
| (a,b) | a × b | The tuple type syntax in Agda is not the same as the tuple value syntax |
| Nil   | []   | The empty vector (Nil) in Idris seems to have built-in syntactic sugar so that [] can be used as a pattern. |
| (a, b) | (a , b) | The pair constructor _,_ in Agda needs space before on both sides |
| (a : A ** B) | Sigma A (\a -> B) | No built-in syntactic sugar for the dependent sum type in Agda. |
| (a ** b) | MkSigma a b | No built-in syntactic sugar for dependent sum values in Agda. |

----------------------------------------------------------------

# Matching Idris and Agda files

``` Shell
find . -name '*.agda'
find . -name '*.lidr'
```

* Agda files here: https://github.com/patrikja/SeqDecProb_Agda/tree/master/libs
* Idris files here: https://github.com/nicolabotta/SeqDecProbs/tree/master/frameworks/14-

| Agda                                           | Idris |
| ----------                                     | ----- |
| ./Decidable.agda                               | ./Decidable.lidr |
| ./NatProperties.agda                           | ./NatProperties.lidr |
| ./Preorder.agda                                | ./Preorder.lidr |
| ./Pro.agda                                     | ./Prop.lidr |
| ./SigmaProperties.agda                         | ./SigmaProperties.lidr |
| ./TotalPreorder.agda                           | ./TotalPreorder.lidr |
| ./Util.agda                                    | ./Util.lidr |
| ./VectOperations.agda                          | ./VectOperations.lidr |
| ./VectProperties.agda                          | ./VectProperties.lidr |

Idris "standard library" files here: https://github.com/idris-lang/Idris-dev/tree/master/libs

| Agda                                           | Idris |
| -----                                          | ----- |
| ./Idris/Builtins.agda                          | prelude/Builtins.idr |
| ./Idris/Prelude/Nat.agda                       | prelude/Prelude/Nat.idr                     |
| ./Idris/Prelude/Bool.agda                      | prelude/Prelude/Bool.idr                    |
| ./Idris/Prelude/Either.agda                    | prelude/Prelude/Either.idr                  |
| ./Idris/Prelude/Maybe.agda                     | prelude/Prelude/Maybe.idr                   |
| ./Idris/Prelude/List.agda                      | prelude/Prelude/List.idr                    |
| ./Idris/Prelude/Classes.agda                   | prelude/Prelude/Classes.idr                 |
| ./Idris/Prelude/Basics.agda                    | prelude/Prelude/Basics.idr                  |
| ./Idris/Prelude/Pairs.agda                     | prelude/Prelude/Pairs.idr                   |
| ./Idris/Data/Vect.agda                         | base/Data/Vect.idr |
| ./Idris/Data/VectType.agda                     | base/Data/VectType.idr |
| ./Idris/Data/Fin.agda                          | base/Data/Fin.idr |
| ./Idris/Data/Vect/Quantifiers.agda             | base/Data/Vect/Quantifiers.idr |
| ./Idris/Control/Isomorphism.agda               | base/Control/Isomorphism.idr |
| ./Idris/Syntax/PreorderReasoning.agda          | base/Syntax/PreorderReasoning.idr |
| ./Idris/Decidable/Decidable.agda               | contrib/Decidable/Decidable.idr |
| ./Idris/Decidable/Order.agda                   | contrib/Decidable/Order.idr |


## Not yet ported

./Basics.lidr
./BoundedNat.lidr
./BoundedNatOperations.lidr
./BoundedNatProperties.lidr
./ClassContainerMonad.lidr
./ContainerMonad.lidr
./DecidableProperties.lidr
./EffectException.lidr
./EffectStdIO.lidr
./EmbProj.lidr
./EqualityProperties.lidr
./FinOperations.lidr
./FinProperties.lidr
./Finite.lidr
./FiniteOperations.lidr
./FiniteProperties.lidr
./FiniteSubType.lidr
./FiniteSubTypeOperations.lidr
./FiniteSubTypeProperties.lidr
./FunOperations.lidr
./FunProperties.lidr
./IdentityOperations.lidr
./IdentityProperties.lidr
./IsomorphismOperations.lidr
./IsomorphismProperties.lidr
./LambdaPostulates.lidr
./Opt.lidr
./Order.lidr
./OrderOperations.lidr
./OrderProperties.lidr
./PreorderOperations.lidr
./RelFloat.lidr
./RelFloatPostulates.lidr
./RelFloatProperties.lidr
./RelSyntax.lidr
./SeqDecProbMonadic.lidr
./SeqDecProbMonadicExample2.lidr
./SeqDecProbMonadicSmallTheory.lidr
./SeqDecProbMonadicSmallTheoryExample2.lidr
./SeqDecProbMonadicTheory.lidr
./SeqDecProbMonadicTheoryExample2.1.lidr
./SeqDecProbMonadicTheoryExample2.lidr
./SigmaOperations.lidr
./SingletonProperties.lidr
./SoProperties.lidr
./SubType.lidr
./SubsetOperations.lidr
./SubsetProperties.lidr
./TotalPreorderOperations.lidr
./Unique.lidr
./UniqueProperties.lidr
./funprogintro.lidr
./tagging.lidr

----------------------------------------------------------------

## Fixities

When in doubt I have looked up fixities in the Agda stdlib.

```Shell
find . -type f -exec grep -nH -e infix {} +
./Idris/Builtins.agda:11:infixr 2 _×_
./Idris/Builtins.agda:12:infixr 4 _,_
./Idris/Builtins.agda:36:infix 4 _==_
./Idris/Prelude/Nat.agda:214:infixl 8 _+_ _-_
./Idris/Prelude/Nat.agda:215:infixl 9 _*_
./Idris/Prelude/Bool.agda:27:infixl 4 _&&_ _||_
./Idris/Prelude/List.agda:17:-- infix 5 _\\_
./Idris/Prelude/List.agda:18:infixr 7 _::_
./Idris/Prelude/List.agda:19:infixr 7 _++_
./Idris/Prelude/Classes.agda:9:infixl 5 _==_ _/=_
./Idris/Prelude/Classes.agda:10:infixl 6 _<_ _<=_ _>_ _>=_
./Idris/Prelude/Classes.agda:11:infixl 7 _<<_ _>>_
./Idris/Prelude/Classes.agda:12:infixl 8 _+_ _-_
./Idris/Prelude/Classes.agda:13:infixl 9 _*_ _/_
./Idris/Prelude/Basics.agda:35:infixl 9 _∘_
./Idris/Syntax/PreorderReasoning.agda:22:infixr 2 _==<_>==_
./Idris/Syntax/PreorderReasoning.agda:26:infix  2 _QED
./Idris/Data/VectType.agda:16:  infixr 7 _::_
```
