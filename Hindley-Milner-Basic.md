# Hindley Milner Basic type inference

This is an implementation of the Hindley Milner type checking algorithm based on the Scala code by Andrew Forrest, the Perl code by Nikita Borisov and the paper "Basic Polymorphic Typechecking" by Luca Cardelli.  

This was the very first version that I came across and is served as a good introduction to the algorithms as the terms in the code match the terms described in the paper mentioned above.  

One thing I don't particularly like about this implementation is the injected environment where function constants are defined such as `pair`, `true`, `cond`, `zero`, `pred` and `times`.  Although this allows the AST and type checking implementation to remain fairly simple, its not as easy to optimise later on as everything is treated as a function ast element, it also leads to fairly verbose AST.  Another part I don't like is the presence of mutable reference cell representing the current type variable identifier: `let nextVariableId = ref 0`.  this should be reset whenever the type environment needs to be rechecked.  Im itching to factor this out but I've left it here as it matches the referenced paper.  

## Code

All code is in a self contained project:
[HMBasic](HMBasic/)

## References
[Luca Cardelli: Basic Polymorphic Typechecking](http://lucacardelli.name/Papers/BasicTypechecking.pdf)