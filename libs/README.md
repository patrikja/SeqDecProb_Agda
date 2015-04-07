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
