# Hindley Milner pure implementation with split constraint generation and solving

This implementation is based from a combination of "Generalizing Hindley-Milner Type Inference Algorithms" and Stephen Diehl's "Write you a Haskell".

This is one of my favorite implementations as it splits the constraint gathering from the solving which mean that you can solve the constraints in different manners.  One of the issues with Hindley-Milner is when an error occurs it is not always easy to find the point at which the error occurs, so having the solving stage separate means you can potentially solve the inference constraints in different ways or use a heuristic approach.  The [Generalizing Hindley-Milner Type Inference Algorithms](https://pdfs.semanticscholar.org/8983/233b3dff2c5b94efb31235f62bddc22dc899.pdf) paper goes into this in more detail

## Code

All code is in a self contained project:
[HMSplitSolve](HMSplitSolve/)

## References
[Generalizing Hindley-Milner Type Inference Algorithms, Bastiaan Heeren, Jurriaan Hage ,Doaitse Swierstra](https://pdfs.semanticscholar.org/8983/233b3dff2c5b94efb31235f62bddc22dc899.pdf)

[Write you a Haskell - Hindley Milner type inference, Stephen Diehl](http://dev.stephendiehl.com/fun/006_hindley_milner.html#constraint-solver)
