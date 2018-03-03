open System
open HMPure

[<EntryPoint>]
let main argv =

    let b1 =
        "b1", ELet ("id", EAbs("x", EVar "x"), EVar "id")

    let b2 =
        "b2", ELet ("id", EAbs( "x", EVar "x"), EApp(EVar "id", EVar "id"))

    let b3 =
        "b3", ELet( "id", (EAbs("x", ELet( "y", EVar "x", EVar "y"))), EApp(EVar "id", EVar "id"))

    let b4 =
        "b4", ELet( "id", EAbs( "x", ELet("y", EVar "x", EVar "y")),    EApp(EApp(EVar "id", EVar "id") ,EPrim (Int 2)))

    let b5 =
        "b5", ELet("id", EAbs( "x", EApp(EVar "x", EVar "x")), EVar "id")

    let b6 =
        "b6", EAbs("m", (ELet("y", EVar "m", ELet("x", (EApp(EVar "y", EPrim(Bool true))), EVar "x"))))

    let b7 =
          "b6: fun f -> (fun g -> (fun arg (f g arg)))",
          EAbs("f", EAbs("g", EAbs("arg", EApp(EVar("g"), EApp(EVar("f"), EVar("arg"))))))

    let testBank = [b1; b2; b3; b4; b6; b7]

    let runTestBank bank printResult =
      bank
      |> List.iter (fun (name, exp) -> HMPure.resetId()
                                       let result = HMPure.typeInference Map.empty exp
                                       if printResult then
                                            printfn "%s" name
                                            printfn "Expression: %A" exp
                                            printfn "inferred: %s\n" (HMPure.Typ.toString result))

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
