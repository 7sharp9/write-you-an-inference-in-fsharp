# Write you an inference _in F#_

This repo is inspired by other great resources in this area but targeted at 
idiomatic easy to follow F# code.  Saying that, type inference algorithms are not 
the easiest to get your head round but this will be a place to describe different 
types and methods of doing type inference.  

Initially the focus will be basic Hindley-Milner inference, followed by adding 
extensions on for row polymorphism, variant polymorphism, with both duplicate and 
restricted labels.  Finally I expect to have a of rank n or higher kinded polymorphisms with row 
and variant polymorphism which should allow some interesting effects.  _(Namely a form of first class modules)_

The algorithms have been implemented from various sources and papers which I will 
add in due course, but for now here is the different variations planned.  

Heres what we have so far, I have written all of these but not yet committed all the code:

## Basic Hindley-Milner inference
  * [Basic implementation based on Luca Cardellis paper](Hindley-Milner inference.md)
  * [Pure implmentation with combined constraints and solving](Hindley-Milner-Pure.md)
  * [Pure implmentation with separate constraint gathering and solving](Hindley-Milner-Split-Solver.md)
  * [Mutable implementation with rank optimisations](Hindley-Milner-Mutable.md)
  
## Basic Hindley-Milner inference with row polymorphism
  * [Mutable implementation with row polymorphism extension](Hindley-Milner-Mutable-Rowpolymorphism.md)
  * [Pure implementation with row polymorphism extension](Hindley-Milner-Pure-Rowpolymorphism.md)
  
I have not yet started but really want to investigate adding row and variant polymorphism with 
the possibility to use higher kinded types.  I'll update the above as I work on this.

This repo grew out of a small language that I am writing to test out various ideas around type systems and 
also targeting the arm platform via LLVM.  While reading one of the papers on rank n types I came across the following which is quite true:

>Considering how many papers there are on type systems, there is surprising little 
literature on type inference that is aimed unambiguously at implementors.
  
I'll also add some notes on type systems, research paper references and description of 
terms written in normal basic language, I may cross reference in my blog, Ive not yet decided.
