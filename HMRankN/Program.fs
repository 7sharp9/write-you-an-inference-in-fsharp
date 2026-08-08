open HMRankN

// ─── Helper to build polymorphic built-in types ───────────────────────────────

let gen name   = TVar(ref (Generic name))
let forAll ns t = TForAll(ns, t)
let (-->) a b  = TArr(a, b)

// ─── Built-in environment ────────────────────────────────────────────────────

let builtins : Env =
    Map.ofList
        [ // id : forall a. a -> a
          "id",    forAll ["a"] (gen "a" --> gen "a")
          // const : forall a b. a -> b -> a
          "const", forAll ["a";"b"] (gen "a" --> (gen "b" --> gen "a"))
          // succ : Int -> Int
          "succ",  TConst "Int" --> TConst "Int"
          // not : Bool -> Bool
          "not",   TConst "Bool" --> TConst "Bool" ]

// ─── Demo runner ─────────────────────────────────────────────────────────────

let run label expr =
    try
        let ty = inferTop builtins expr
        printfn "  %-35s : %s" label (prettyType ty)
    with
    | TypeError msg -> printfn "  %-35s : ERROR — %s" label msg

[<EntryPoint>]
let main _ =
    printfn ""
    printfn "═══ Standard rank-1 (HM) examples ═══════════════════════════════"
    printfn ""

    // λx. x
    run "fun x -> x"
        (Lam("x", Var "x"))

    // λx. λy. x
    run "fun x y -> x"
        (Lam("x", Lam("y", Var "x")))

    // let id = fun x -> x in id
    run "let id = fun x -> x in id"
        (Let("id", Lam("x", Var "x"), Var "id"))

    // let id = fun x -> x in id id
    run "let id = fun x -> x in id id"
        (Let("id", Lam("x", Var "x"), App(Var "id", Var "id")))

    // let id = fun x -> x in id 42
    run "let id = fun x -> x in id 42"
        (Let("id", Lam("x", Var "x"), App(Var "id", Lit(LInt 42))))

    // λm. let y = m in let x = y true in x
    run "fun m -> let y = m in let x = y true in x"
        (Lam("m",
            Let("y", Var "m",
                Let("x", App(Var "y", Lit(LBool true)),
                    Var "x"))))

    // λf. λg. λarg. g (f arg)   — composition
    run "fun f g arg -> g (f arg)"
        (Lam("f", Lam("g", Lam("arg",
            App(Var "g", App(Var "f", Var "arg"))))))

    printfn ""
    printfn "═══ Rank-2 examples ══════════════════════════════════════════════"
    printfn ""

    // Rank-2 annotation: a function that takes a *polymorphic* argument
    //   applyToInt : (forall a. a -> a) -> Int
    //   applyToInt f = f 42
    //
    // Without rank-2 support this would fail because standard HM can only
    // instantiate `f` once, but here `f` needs to remain polymorphic inside
    // the function body.
    let polyId = forAll ["a"] (gen "a" --> gen "a")

    run "applyToInt : (forall a. a->a) -> Int"
        (Ann(
            Lam("f", App(Var "f", Lit(LInt 42))),
            polyId --> TConst "Int"))

    // applyToBool : (forall a. a -> a) -> Bool
    run "applyToBool : (forall a. a->a) -> Bool"
        (Ann(
            Lam("f", App(Var "f", Lit(LBool true))),
            polyId --> TConst "Bool"))

    // A rank-2 function applied to `id` from the environment.
    // id has type forall a. a -> a, so it subsumes the rank-2 argument.
    run "applyToInt id"
        (App(
            Ann(
                Lam("f", App(Var "f", Lit(LInt 42))),
                polyId --> TConst "Int"),
            Var "id"))

    // A lambda can also be passed directly without naming it in a let.
    // This requires the generalisation step in App to work correctly.
    run "applyToInt (fun x -> x)"
        (App(
            Ann(
                Lam("f", App(Var "f", Lit(LInt 42))),
                polyId --> TConst "Int"),
            Lam("x", Var "x")))

    // Demonstrate that a monomorphic function is NOT accepted where
    // a polymorphic one is expected.
    //   applyToInt succ   — should FAIL because succ : Int -> Int
    //                       but the annotation needs  forall a. a -> a
    run "applyToInt succ (expected failure)"
        (App(
            Ann(
                Lam("f", App(Var "f", Lit(LInt 42))),
                polyId --> TConst "Int"),
            Var "succ"))

    printfn ""
    printfn "═══ Rank-3 example ═══════════════════════════════════════════════"
    printfn ""

    // rank3arg : ((forall a. a -> a) -> Int) -> Int
    // rank3arg g = g id
    //
    // The argument g already has a rank-2 type, making this a rank-3 function.
    let rank2Arg = (polyId --> TConst "Int") --> TConst "Int"

    run "rank3 : ((forall a.a->a)->Int)->Int"
        (Ann(
            Lam("g", App(Var "g", Var "id")),
            rank2Arg))

    printfn ""
    0
