# Hindley Milner pure implementation

This implementation is based on [Algorithm W step by step](ttps://github.com/wh5a/Algorithm-W-Step-By-Step/blob/master/AlgorithmW.pdf) by Martin Grabmüller.  

The only lumpy bit in this particular implementation is `let private currentId = ref 0`, this is an artifact of removing the reader monads from the Haskell implementation and a simple reference cell was the best way to get it working.  I actually removed this when I did the [split solver implementation](HMSplitSolve).  If if bothers you then I would happily accept a PR :-) , theres actually an outstanding issue for this.

## Code

All code is in a self contained project:
[HMPure](HMPure/)

## References

[Algorithm W step by step, Martin Grabmuller](https://github.com/wh5a/Algorithm-W-Step-By-Step/blob/master/AlgorithmW.pdf)


