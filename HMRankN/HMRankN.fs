module HMRankN

// Hindley-Milner type inference extended to support arbitrary-rank
// (rank-n) polymorphism.
//
// In standard HM, forall quantifiers appear only at the outermost level of a
// type scheme.  Rank-n polymorphism lifts this restriction so that foralls may
// appear at any negative (contra-variant) position, e.g.
//
//   rank-1 :         forall a. a -> a
//   rank-2 : (forall a. a -> a) -> Int
//   rank-n : arbitrary nesting
//
// The algorithm follows "Practical Type Inference for Arbitrary-Rank Types"
// (Peyton Jones & Shields, 2007).  The core ideas are:
//   * Bidirectional type checking  (infer / check)
//   * Subsumption instead of plain unification at call sites
//   * Skolemisation  to check that a type really is at least as polymorphic as
//     required

open System

// ─── Names & identifiers ──────────────────────────────────────────────────────

type Name  = string
type Id    = int
type Level = int

// ─── Expression language ─────────────────────────────────────────────────────

type Expr =
    | Var  of Name
    | Lit  of Lit
    | App  of Expr * Expr
    | Lam  of Name * Expr
    | Let  of Name * Expr * Expr
    | Ann  of Expr * Ty           // explicit type annotation:  e : T

and Lit =
    | LInt  of int
    | LBool of bool

// ─── Type language ───────────────────────────────────────────────────────────
//
// TForAll carries a list of bound-variable names and a body type.  These names
// index Generic entries inside the body, exactly the same way HMMutable uses
// Generic nodes after generalisation, but now the quantifier can appear at any
// position in the type, not just the top level.

and Ty =
    | TConst  of Name              // Int, Bool, …
    | TVar    of TyVar ref         // unification variable (mutable)
    | TArr    of Ty * Ty           // a -> b
    | TForAll of Name list * Ty    // forall a b. T   (rank-n quantifier)

and TyVar =
    | Unbound of Id * Level        // unsolved — level used for generalisation
    | Link    of Ty                // solved — forwarding pointer
    | Generic of Name              // bound by an enclosing TForAll
    | Skolem  of Name * Id         // rigid constant; cannot be unified

// ─── Type environment ────────────────────────────────────────────────────────

type Env = Map<Name, Ty>

// ─── Fresh-variable counter ───────────────────────────────────────────────────

let mutable private counter = 0

let private nextId () =
    let i = counter
    counter <- i + 1
    i

let newVar     level = TVar(ref (Unbound(nextId (), level)))
let newSkolem  name  = TVar(ref (Skolem(name, nextId ())))

// ─── Error handling ───────────────────────────────────────────────────────────

exception TypeError of string
let inline typeError fmt = Printf.kprintf (fun msg -> raise (TypeError msg)) fmt

// ─── Link following ───────────────────────────────────────────────────────────

let rec shallowNorm ty =
    match ty with
    | TVar { contents = Link ty } -> shallowNorm ty
    | ty -> ty

// ─── Pretty printer ───────────────────────────────────────────────────────────
// Defined early so error messages in unify can use it.

let rec prettyPrec prec ty =
    match ty with
    | TConst name -> name
    | TVar { contents = Link ty }       -> prettyPrec prec ty
    | TVar { contents = Unbound(id, _)} -> sprintf "_%d" id
    | TVar { contents = Generic name }  -> name
    | TVar { contents = Skolem(n, _) }  -> sprintf "!%s" n
    | TArr(a, b) ->
        let s = sprintf "%s -> %s" (prettyPrec 1 a) (prettyPrec 0 b)
        if prec > 0 then sprintf "(%s)" s else s
    | TForAll(binders, body) ->
        let s = sprintf "forall %s. %s" (String.concat " " binders) (prettyPrec 0 body)
        if prec > 0 then sprintf "(%s)" s else s

let prettyType ty = prettyPrec 0 ty

// ─── Substitution ────────────────────────────────────────────────────────────
// Replace Generic nodes (identified by name) with concrete types.

let rec substTy (subst : Map<Name, Ty>) ty =
    match ty with
    | TConst _ -> ty
    | TVar { contents = Link ty }    -> substTy subst ty
    | TVar { contents = Generic n }  ->
        match Map.tryFind n subst with
        | Some t -> t
        | None   -> ty
    | TVar _   -> ty     // Unbound or Skolem — leave alone
    | TArr(a, b) ->
        TArr(substTy subst a, substTy subst b)
    | TForAll(binders, body) ->
        // Shadow bound names so we do not accidentally substitute them
        let subst' = List.fold (fun s n -> Map.remove n s) subst binders
        TForAll(binders, substTy subst' body)

// ─── Occurs check & level adjustment ─────────────────────────────────────────

let rec private occursAdjust id level ty =
    match ty with
    | TVar { contents = Link ty }    -> occursAdjust id level ty
    | TVar { contents = Generic _ }  -> ()
    | TVar { contents = Skolem _ }   -> ()
    | TVar({ contents = Unbound(otherId, otherLevel) } as tv) ->
        if otherId = id then typeError "recursive type"
        if otherLevel > level then tv := Unbound(otherId, level)
    | TConst _     -> ()
    | TArr(a, b)   -> occursAdjust id level a; occursAdjust id level b
    | TForAll(_, b)-> occursAdjust id level b

// ─── Monotype unification ────────────────────────────────────────────────────
// Unifies monotypes only; TForAll on either side is an error (use subsume instead).

let rec unify ty1 ty2 =
    let rec containsForAll ty =
        match shallowNorm ty with
        | TForAll _ -> true
        | TArr(a, b) -> containsForAll a || containsForAll b
        | TVar { contents = Link t } -> containsForAll t
        | _ -> false

    match shallowNorm ty1, shallowNorm ty2 with
    | TConst n1, TConst n2 when n1 = n2 -> ()
    | TArr(a1, b1), TArr(a2, b2)        -> unify a1 a2; unify b1 b2
    | TForAll _, _
    | _, TForAll _ ->
        typeError "unexpected polymorphic type in monotype unification; use subsume"
    | TVar({ contents = Unbound(id, level) } as tv), ty
    | ty, TVar({ contents = Unbound(id, level) } as tv) ->
        if containsForAll ty then
            typeError "unexpected polymorphic type in monotype unification; use subsume"
        occursAdjust id level ty
        tv := Link ty
    | TVar { contents = Skolem(_, id1) }, TVar { contents = Skolem(_, id2) }
        when id1 = id2 -> ()
    | t1, t2 ->
        typeError "cannot unify '%s' and '%s'" (prettyPrec 0 t1) (prettyPrec 0 t2)

// ─── Skolem-escape check ─────────────────────────────────────────────────────
// After subsumption we verify that skolem variables introduced for checking
// have not leaked into the inferred type on the other side.

let private checkNoEscape (skIds : Set<Id>) ty =
    let rec loop ty =
        match ty with
        | TVar { contents = Link ty }       -> loop ty
        | TVar { contents = Unbound _ }     -> ()
        | TVar { contents = Generic _ }     -> ()
        | TVar { contents = Skolem(n, id) } ->
            if Set.contains id skIds then
                typeError "skolem type variable '%s' escapes its scope" n
        | TConst _      -> ()
        | TArr(a, b)    -> loop a; loop b
        | TForAll(_, b) -> loop b
    loop ty

// ─── Skolemisation ───────────────────────────────────────────────────────────
// Replace the outermost forall binders with fresh skolem constants.
// Returns the skolem id-set (for escape checks) and the specialised body.

let private skolemise ty =
    match ty with
    | TForAll(binders, body) ->
        let sks = binders |> List.map (fun n -> n, newSkolem n)
        let subst = Map.ofList sks
        let skIds =
            sks |> List.map (fun (_, sk) ->
                match sk with
                | TVar r -> (match !r with Skolem(_, id) -> id | _ -> -1)
                | _ -> -1)
            |> Set.ofList
        subst, skIds, substTy subst body
    | ty -> Map.empty, Set.empty, ty

// ─── Instantiation ───────────────────────────────────────────────────────────
// Replace the outermost forall binders with fresh unification variables.

let instantiate level ty =
    match ty with
    | TForAll(binders, body) ->
        let subst = binders |> List.map (fun n -> n, newVar level) |> Map.ofList
        substTy subst body
    | ty -> ty

// ─── Free-variable collection ────────────────────────────────────────────────
// Collect all TyVar refs that are currently Unbound (before any unification).
// We use these refs *after* unification to see whether they picked up a skolem.

let private collectUnboundRefs ty =
    let rec loop (acc : TyVar ref list) ty =
        match ty with
        | TVar { contents = Link ty }        -> loop acc ty
        | TVar({ contents = Unbound _ } as r)-> r :: acc
        | TVar _   -> acc
        | TConst _ -> acc
        | TArr(a, b)    -> loop (loop acc a) b
        | TForAll(_, b) -> loop acc b
    loop [] ty

// ─── Subsumption ─────────────────────────────────────────────────────────────
//
// subsume level σ1 σ2  checks that σ1 is *at least as polymorphic as* σ2,
// meaning every value of type σ2 can also be given type σ1.  This replaces
// plain unification at function-application sites.
//
// Intuition:
//   (forall a. a -> a)  subsumes  (Int -> Int)   ✓
//   (Int -> Int)  does NOT subsume  (forall a. a -> a)
//
// Algorithm (deep skolemisation):
//   1.  If σ2 has a leading forall, skolemise it and recurse.
//       The skolems act as arbitrary ground witnesses so σ1 must work for them.
//       After the check, verify that none of σ1's *pre-existing* free
//       unification variables ended up equated to a skolem (escape check).
//   2.  If σ1 has a leading forall, instantiate it with fresh unification vars
//       and recurse.
//   3.  If both are arrow types, recurse contravariantly on the argument and
//       covariantly on the result.
//   4.  Otherwise fall back to plain monotype unification.

let rec subsume level ty1 ty2 =
    let ty1 = shallowNorm ty1
    let ty2 = shallowNorm ty2
    match ty1, ty2 with

    // Case 1 — σ2 is polymorphic: skolemise and check σ1 works for all instances.
    // Escape check: collect σ1's free unification vars *before* unification,
    // then afterwards verify none of them were unified to a skolem.
    | _, TForAll _ ->
        let freeRefs = collectUnboundRefs ty1
        let _, skIds, body2 = skolemise ty2
        subsume level ty1 body2
        // For each free var that existed in ty1 before unification, if it now
        // resolves (via Links) to a type containing a skolem, that skolem has
        // escaped its scope.
        for r in freeRefs do
            match !r with
            | Link ty -> checkNoEscape skIds ty
            | _       -> ()   // still unbound — no escape

    // Case 2 — σ1 is polymorphic: instantiate and check the instance subsumes σ2
    | TForAll _, _ ->
        let inst = instantiate level ty1
        subsume level inst ty2

    // Case 3 — both are function types: contravariant in arg, covariant in result
    | TArr(a1, r1), TArr(a2, r2) ->
        subsume level a2 a1     // argument is contravariant
        subsume level r1 r2

    // Case 4 — fall back to monotype unification
    | _ -> unify ty1 ty2

// ─── Generalisation ──────────────────────────────────────────────────────────
// Walk the type and promote every Unbound variable whose level exceeds
// `level` to a Generic node.

let rec generalize level ty =
    match ty with
    | TVar { contents = Link ty } -> generalize level ty
    | TVar { contents = Generic _ }
    | TVar { contents = Skolem _ } -> ty
    | TVar({ contents = Unbound(id, otherLevel) } as tv) when otherLevel > level ->
        let name = sprintf "'t%d" id
        tv := Generic name
        TVar tv
    | TVar _ -> ty
    | TConst _ -> ty
    | TArr(a, b)    -> TArr(generalize level a, generalize level b)
    | TForAll(bs, b)-> TForAll(bs, generalize level b)

// Collect all Generic names reachable in the type (minus those already bound).

let rec private collectGenerics bound ty =
    match ty with
    | TVar { contents = Link ty }   -> collectGenerics bound ty
    | TVar { contents = Generic n } -> if Set.contains n bound then Set.empty else Set.singleton n
    | TVar _  -> Set.empty
    | TConst _ -> Set.empty
    | TArr(a, b) ->
        Set.union (collectGenerics bound a) (collectGenerics bound b)
    | TForAll(bs, body) ->
        collectGenerics (Set.union bound (Set.ofList bs)) body

// Wrap a type in a TForAll if it contains free Generic nodes.

let quantify ty =
    let gens = collectGenerics Set.empty ty |> Set.toList |> List.sort
    if List.isEmpty gens then ty
    else TForAll(gens, ty)

// ─── Arrow matching ───────────────────────────────────────────────────────────
// Given a type expected to be a function, return (argTy, retTy).
// If the type is a flexible unification variable, constrain it to be an arrow.

let rec private matchFunTy level ty =
    match shallowNorm ty with
    | TArr(a, b) -> a, b
    | TForAll _  ->
        // Instantiate and retry
        matchFunTy level (instantiate level ty)
    | TVar({ contents = Unbound(_, lvl) } as tv) ->
        let a = newVar lvl
        let b = newVar lvl
        tv := Link(TArr(a, b))
        a, b
    | ty -> typeError "expected a function type but got '%s'" (prettyPrec 0 ty)

// ─── Bidirectional type checking ─────────────────────────────────────────────
//
// infer env level expr       → Ty    (synthesis mode)
// check env level expr ty    → unit  (checking mode)
//
// The two modes cooperate: `check` can push polymorphic type information into
// lambdas, while `infer` uses subsumption at application sites.

let rec infer (env : Env) level expr =
    match expr with
    | Lit(LInt _)  -> TConst "Int"
    | Lit(LBool _) -> TConst "Bool"

    | Var name ->
        match Map.tryFind name env with
        | Some ty -> ty           // return the polymorphic type as-is;
                                  // instantiation happens in matchFunTy (function position)
                                  // or subsume (argument position)
        | None    -> typeError "unbound variable '%s'" name

    // An explicit type annotation switches to checking mode
    | Ann(e, ty) ->
        check env level e ty
        ty

    | Lam(x, body) ->
        let argTy = newVar level
        let retTy = infer (Map.add x argTy env) level body
        TArr(argTy, retTy)

    | App(f, arg) ->
        let fTy = infer env level f
        let argTy, retTy = matchFunTy level fTy
        // Infer the argument at level+1 and generalise before calling subsume.
        // This mirrors the paper's `inferSigma` step: locally-created unification
        // variables are promoted to Generic nodes so the subsumption escape check
        // correctly distinguishes them from environment variables.
        let argMono = infer env (level + 1) arg
        let argPoly = generalize level argMono |> quantify
        subsume level argPoly argTy
        retTy

    | Let(x, e, body) ->
        // Generalise at the let binding (the "value restriction" is relaxed
        // here for simplicity; syntactic values would need extra care)
        let eTy   = infer env (level + 1) e
        let genTy = generalize level eTy |> quantify
        infer (Map.add x genTy env) level body

and check (env : Env) level expr expectedTy =
    let expectedTy = shallowNorm expectedTy
    match expr, expectedTy with

    // A lambda checked against an arrow type: bind the parameter at the
    // given argument type (which may itself be polymorphic — rank-2+)
    | Lam(x, body), TArr(argTy, retTy) ->
        check (Map.add x argTy env) level body retTy

    // Checking against a forall: infer and generalise the expression's type first,
    // then delegate to subsume which contains the correct escape check.
    | expr, TForAll _ ->
        let inferredMono = infer env (level + 1) expr
        let inferredPoly = generalize level inferredMono |> quantify
        subsume level inferredPoly expectedTy

    // Fall through: infer a type and then check subsumption
    | expr, ty ->
        let inferredTy = infer env level expr
        subsume level inferredTy ty

// ─── Top-level entry point ────────────────────────────────────────────────────

let inferTop (env : Env) expr : Ty =
    counter <- 0
    let ty = infer env 0 expr
    // Generalise at level -1 so that variables created at level 0 (the outermost
    // lambda binders) are also quantified, matching standard HM behaviour.
    generalize (-1) ty |> quantify
