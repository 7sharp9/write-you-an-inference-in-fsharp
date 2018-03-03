open System
open HMMutable

[<EntryPoint>]
let main argv =

    let example1 =
        "let f = fun x y -> g(x, y) in f(a, b)",
        Fun([("a")], Var(("a") ))

    let example2 =
        "fun f -> (fun g -> (fun arg (f g arg)))",
        Fun(["f"], 
            Fun(["g"], 
                Fun (["arg"], 
                    Call(Var "g",[Call(Var "f", [Var "arg"])])
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

    let testBank = [example1; example2; example3; example4; example5]

    let runTestBank bank printResult =
      bank
      |> List.iter (fun (name, exp) -> resetId()
                                       let ty = infer Env.empty 0 exp
                                       let generalizedTy = generalize (-1) ty 
                                       if printResult then
                                            printfn "%s" name
                                            printfn "Expression: %s" (HMMutable.exp.toString exp)
                                            printfn "Infered: %s\n" (HMMutable.ty.toString generalizedTy) )

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
