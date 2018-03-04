# Hindley Milner Mutable inference

This implementation is based on algorithm w from [tomprimozic/type-systems/algorithm_w](https://github.com/tomprimozic/type-systems/tree/master/algorithm_w).

This implementation uses several optimizations over a naive implementation. 
Instead of explicit substitutions when unifying the types it uses updateable references. 
It also tags unbound type variables with levels or ranks to optimize generalizations of let bindings.  This technique was first described by Didier Rémy. A more detailed description of the ranked type variables algorithm and associated optimizations was written by [Oleg Kiselyov](http://okmij.org/ftp/ML/generalization.html).  

The part I don't like in this implementation is the mutable reference that represents the current type variable state: `let currentId = ref 0` I have left it in to keep this implementation close to [tomprimozic/type-systems/algorithm_w](https://github.com/tomprimozic/type-systems/tree/master/algorithm_w).  Although this implementation is 3-4x faster than the pure implementations its also a little more difficult to follow in my opinion, I also think that the ranking optimisation could be applied to the pure implementations too.

## Code

All code is in a self contained project:
[HMMutable](HMMutable/)

## References
[Didier Rémy: Extension of ML Type System with a Sorted Equational Theory on Types](ftp://ftp.inria.fr/INRIA/Projects/cristal/Didier.Remy/eq-theory-on-types.ps.gz)
