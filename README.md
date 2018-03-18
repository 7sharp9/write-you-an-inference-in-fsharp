# Write you an inference _in F#_

This repo is inspired by other great resources in this area but targeted at 
idiomatic and easy to follow F# code.  Saying that, type inference algorithms are not 
the easiest to get your head round but this will be a place to describe different 
types and methods of doing type inference.  

The algorithms are split into pure and mutable Hindley-Milner type inference and row polymorphism extension to it.

## Hindley-Milner inference
  * [Basic implementation based on Luca Cardellis paper](Hindley-Milner-Basic.md)  
  * [Pure implmentation with combined constraints and solving](Hindley-Milner-Pure.md)
  * [Pure implmentation with separate constraint gathering and solving](Hindley-Milner-Split-Solver.md)
  * [Mutable implementation with rank optimisations](Hindley-Milner-Mutable.md)
  
## Hindley-Milner inference with row polymorphism
  * [Mutable implementation with row polymorphism extension](Hindley-Milner-Mutable-Rowpolymorphism.md)
  * [Pure implementation with row polymorphism extension](Hindley-Milner-Pure-Rowpolymorphism.md)

This repo grew out of a small language that I was tinkering with to test out various ideas around type systems and while reading one of the papers on rank n types I came across the following which is quite true:

>Considering how many papers there are on type systems, there is surprising little 
literature on type inference that is aimed unambiguously at implementors.
  
If you have any suggestions or want to make any contributions I'll happily take any contributions :-)

