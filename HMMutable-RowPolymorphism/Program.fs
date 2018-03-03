open System
open HMMutableRowpolymorphism

[<EntryPoint>]
let main argv =

    let example1 =
        "let f = fun x y -> g(x, y) in f(a, b)",
        Fun([("a")], Var(("a") ))

    let example2 =
        "compose or (>>)",
        Fun(["f"], 
                Fun(["g"], 
                    Fun (["x"], 
                        Call(Var "g",[Call(Var "f", [Var "x"])])
                    )
                )
        )

    let example3 =
        "fun (a,b) -> a",
        Fun(["a"; "b"], Var(("a") ))

    let example4 =
        "let f a b = a",
        Fun( ["a"], Fun(["b"], Var "a"))

    let example5 =
        "fun x -> let y = x in y",
        Fun(["x"], Let("y", Var "x", Var "y"))

    let example6 =
        "{ }",
        RecordEmpty

    let example7 =
        "{a = one}",
        RecordExtend("a", Var "one", RecordEmpty)

    ///expecting: {a : int, b : bool}
    let example8 =
        "{a = one, b = true}",
        RecordExtend("a", Var("one"), RecordExtend("b", Var("true"), RecordEmpty) )

    ///expecting: {b : bool, a : int}
    let example9 =
        "{b = true, a = one}",
        RecordExtend("b", Var("true"), RecordExtend("a", Var("one"), RecordEmpty))

    ///expecting: int
    let example10 =
        "{a = one, b = true}.a",
        RecordSelect(RecordExtend("a", Var("one"), RecordExtend("b", Var("true"), RecordEmpty)), "a")

    ///expecting: bool
    let example11 =
        "{a = one, b = true}.b",
        RecordSelect(RecordExtend("a", Var("one"), RecordExtend("b", Var("true"), RecordEmpty)), "b")

    ///expecting: {f : a -> a}
    let example12 =
        "{f = fun x -> x}",
        RecordExtend("f", Fun(["x"], Var("x")), RecordEmpty)

    let example13 =
        "let r = {a = id, b = succ} in choose(r.a, r.b)",
        Let("r", (RecordExtend("a", Var("id"), RecordExtend("b", Var("succ"), RecordEmpty))),
            Call(Var("choose"), [RecordSelect(Var("r"), "a"); RecordSelect(Var("r"), "b")])
        )

    let example14 =
        "let r = {a = id, b = fun x -> x} in choose(r.a, r.b)",
        Let("r", (RecordExtend("a", Var("id"), RecordExtend("b", Fun(["x"], Var("x")), RecordEmpty))), 
            Call(Var("choose"), [RecordSelect(Var("r"), "a"); RecordSelect(Var("r"), "b")])
        )

    let example15 =
        ///expecting: {x = a4 | r5} -> a4"
        "let f = fun r -> (_.x) r in f", 
        Let("f", Fun(["r"], RecordSelect(Var "r", "x")), Var "f")

    ///This should error, recursive row types are not allowed
    let recordRecurse = 
        "fun r -> choose({x = zero | r}, {y = one | r})",
        Fun(["r"], Call( Var("choose"), [RecordExtend("x", Var("zero"), Var("r")); RecordExtend("y", Var("one"), Var("r")) ]))
    
    let basicEnv =
        let env = ref Env.empty
        let extend name ty =
            env := Env.extend !env name ty
        
        extend "zero" (TConst "int")
        extend "one" (TConst "int")
        extend "true" (TConst "bool")
        extend "false" (TConst "bool")
        extend "choose" (TArrow([TVar {contents = Generic 0}; TVar {contents = Generic 0}], TVar {contents = Generic 0}))
        extend "succ" (TArrow([TConst("int")], TConst("int")))
        extend "id" (TArrow([TVar {contents = Generic 0}], TVar {contents = Generic 0}))
        !env

    let testBank =
        [example1
         example2
         example3
         example4
         example5
         example6
         example7
         example8
         example9
         example10
         example11
         example12
         example13
         example14
         example15]

    let runTestBank bank printResult =
      bank
      |> List.iter (fun (name, exp) -> resetId()
                                       let ty = infer basicEnv 0 exp
                                       let generalizedTy = generalize (-1) ty 
                                       if printResult then
                                            printfn "%s" name
                                            printfn "Expression: %s" (HMMutableRowpolymorphism.exp.toString exp)
                                            printfn "Infered: %s\n" (HMMutableRowpolymorphism.ty.toString generalizedTy) )

    //run through the tests as a warm up
    runTestBank testBank true

    let times =
      [for i in 1..1000 ->
         let sw = Diagnostics.Stopwatch.StartNew()
         runTestBank testBank false
         sw.Stop()
         sw.Elapsed.TotalMilliseconds ]

    printfn "Average bank = %f" (times |> List.average)
    printfn "Average individual = %f" (times |> List.averageBy (fun t -> t / float testBank.Length ))
    0 // return an integer exit code
