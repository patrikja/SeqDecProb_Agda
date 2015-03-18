A port to Agda of a small subset of the Idris libraries distributed
with the Idris compiler.

Aim: make it easy to check Idris-code with Agda (and to improve both
the Idris and the Agda libraries by comparing and contrasting).

This directory contains a libs from both "base" and "prelude".

TODO: It might be easier to add syntax compatibility layers to Agda or
Idris instead of doing this by hand.

Some differences:
| Idris | Agda | Comment |
| ----- | ---- | ------- |
| \ =>  | \ -> |         |
| (.)   | _·_  | The period is a reserved character in Agda. The middle dot is on my keyboard AltGr-. |
| Implicitly implicit lower case arguments | Explicitly implicit arguments. |
