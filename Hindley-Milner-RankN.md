# Hindley-Milner with arbitrary-rank (rank-n) types

## Background

Standard Hindley-Milner (HM) restricts `forall` quantifiers to appear **only at the
outermost level** of a type.  Under this restriction every polymorphic type has the form

```
forall a b … . τ
```

where τ is a *monotype* (no foralls anywhere inside).  This means you can write:

```
id     : forall a. a -> a
const  : forall a b. a -> b -> a
```

but you *cannot* give a parameter a polymorphic type:

```
-- rank-2, illegal in standard HM:
applyToInt : (forall a. a -> a) -> Int
```

**Rank-n polymorphism** lifts this restriction so that `forall` may appear at any
*negative* (contravariant, i.e. argument) position.  The *rank* of a type is the
maximum nesting depth of `forall` quantifiers on the left-hand side of arrows:

| Type | Rank |
|------|------|
| `forall a. a -> a` | 1 |
| `(forall a. a -> a) -> Int` | 2 |
| `((forall a. a -> a) -> Int) -> Int` | 3 |

GHC's `RankNTypes` (and `Rank2Types`) extension exposes exactly this capability.

---

## Algorithm

The implementation is based on

> Peyton Jones, S. & Shields, M. (2007).
> *Practical Type Inference for Arbitrary-Rank Types.*
> Journal of Functional Programming 17(1), pp. 1–82.

Two changes to standard HM are sufficient:

### 1 — The `TForAll` type constructor

Types are extended with an explicit `forall` node that can appear at any position:

```fsharp
type Ty =
    | TConst  of Name              // Int, Bool
    | TVar    of TyVar ref         // unification variable
    | TArr    of Ty * Ty           // a -> b
    | TForAll of Name list * Ty    // forall a b. T   ← rank-n quantifier
```

Type variables still come in four kinds:

```fsharp
and TyVar =
    | Unbound of Id * Level   // unsolved (level used for generalisation)
    | Link    of Ty           // solved — forwarding pointer
    | Generic of Name         // bound by an enclosing TForAll after generalisation
    | Skolem  of Name * Id    // rigid constant introduced during checking
```

### 2 — Bidirectional type checking + subsumption

Standard HM uses a single `infer` pass with `unify` at every constraint site.
Rank-n types require two passes and a *subsumption* relation instead of
unification.

#### `infer env level expr → Ty`   (synthesis mode)

Returns the most general type of `expr`.  When the expression is a variable, the
raw polymorphic type is returned so that the caller (either `matchFunTy` or
`subsume`) can decide whether to instantiate or skolemise it.

#### `check env level expr expectedTy`   (checking mode)

Verifies that `expr` has the given `expectedTy`.  When `expectedTy` is a `forall`,
the binders are *skolemised* before checking the body — this ensures the expression
works for **any** choice of the universally quantified variables.  When `expr` is a
`Lam`, the parameter is bound at the declared argument type (which may itself be
polymorphic), enabling higher-rank lambda parameters.

#### `subsume level σ1 σ2`   ("σ1 is at least as polymorphic as σ2")

This is the key operation used at every function-application site instead of `unify`.

```
(forall a. a -> a)  subsumes  (Int -> Int)   ✓
(Int -> Int)   does NOT subsume   (forall a. a -> a)
```

The algorithm uses *deep skolemisation*:

1. If σ2 starts with a `forall`, **skolemise** σ2 (replace binders with fresh
   rigid constants) and recurse.  After the recursive call, verify that none of the
   pre-existing free unification variables of σ1 ended up equated to a skolem
   (*escape check*).

2. If σ1 starts with a `forall`, **instantiate** σ1 (replace binders with fresh
   unification variables) and recurse.

3. If both are arrow types, recurse *contravariantly* on the argument and
   *covariantly* on the result.

4. Otherwise fall back to plain monotype **unification**.

The escape check is performed correctly: the free unification variables of σ1 are
collected *before* the recursive subsumption call (as mutable refs), and only those
pre-existing variables are inspected afterwards.  This prevents false positives when
a locally-introduced variable is unified with a skolem as part of the check.

---

## Code

All code lives in the self-contained project:

[HMRankN/](HMRankN/)

| File | Contents |
|------|----------|
| `HMRankN.fs` | Type definitions, unification, subsumption, generalisation, inference |
| `Program.fs`  | Demo: rank-1, rank-2, and rank-3 examples with expected output |

---

## Worked examples

### Rank-1 (standard HM)

```
fun x -> x                 : forall 't0. 't0 -> 't0
let id = fun x -> x in id  : forall 't0. 't0 -> 't0
fun f g arg -> g (f arg)   : forall 't3 't4 't5. ('t5 -> 't3) -> ('t3 -> 't4) -> 't5 -> 't4
```

### Rank-2 (polymorphic argument)

```
-- Accepted: id has type  forall a. a -> a  which subsumes the parameter type
applyToInt id   : Int

-- Rejected: succ has type  Int -> Int  which does NOT subsume  forall a. a -> a
applyToInt succ : ERROR — cannot unify '!a' and 'Int'
```

### Rank-3

```
rank3 : ((forall a. a -> a) -> Int) -> Int
```

---

## Key differences from standard HM

| Feature | Standard HM | Rank-n |
|---------|-------------|--------|
| `forall` position | top-level only | anywhere (negative positions) |
| Constraint at call site | `unify` | `subsume` |
| Inference mode | single pass | bidirectional (`infer` + `check`) |
| Type annotations | optional | required for rank-2+ arguments |
| Generalisation | unchanged | unchanged (still let-generalisation) |

---

## References

* Peyton Jones, S. & Shields, M. (2007). *Practical Type Inference for Arbitrary-Rank
  Types.* Journal of Functional Programming 17(1), pp. 1–82.
  <https://www.microsoft.com/en-us/research/publication/practical-type-inference-for-arbitrary-rank-types/>

* Vytiniotis, D., Peyton Jones, S., & Schrijvers, T. (2010). *Let Should Not Be
  Generalised.* In Proceedings of TLDI '10.
