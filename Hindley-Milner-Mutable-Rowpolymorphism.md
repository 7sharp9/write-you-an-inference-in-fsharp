# Hindley Milner Mutable inference with row polymorphism

This is an implementation of type inference for safe, polymorphic and extensible records.  This code is based on the implementation [here](https://github.com/tomprimozic/type-systems/tree/master/extensible_rows).  Essentially this implementation is the same as [HMMutable](HMMutable) with row polymorphism added.  You can see the extension by examining the additional union case fields in the `expr` type that describe all the different operations that can be applied: `RecordSelect`, `RecordExtend`, `RecordRestrict` and `RecordEmpty`.  And again in `ty`: `TRecord `, `TRowEmpty` and `TRowExtend` byt looking at the usages of these types you can see which parts of the algorithm change.

## Code

All code is in a self contained project:
[HMMutable-RowPolymorphism](HMMutable-RowPolymorphism)

## References
[Extension of ML Type System with a Sorted Equational Theory on Types, Didier Rémy](ftp://ftp.inria.fr/INRIA/Projects/cristal/Didier.Remy/eq-theory-on-types.ps.gz)
[Extensible records with scoped labels, Daan Leijen](http://research.microsoft.com/apps/pubs/default.aspx?id=65409)
