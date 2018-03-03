open System
open HMPureRowpolymorphism

[<EntryPoint>]
let main argv =

    let r1 =
        "r1: {y=2} :: {y = Int}",
        EApp (EApp(EPrim(RecordExtend "y"), (EPrim ( Int 2))), (EPrim RecordEmpty))

    let r2 =
        "r2: {x=1, y=2 } :: {x = Int, y = Int}",
        EApp (EApp (EPrim(RecordExtend "x"), (EPrim (Int 1))), snd r1)

    let r3 =
        "r3: (_.y) {x=1, y=2 } :: Int",
        EApp (EPrim (RecordSelect "y"), snd r2)

    let r4 =
        "r4: let f = fun r -> (_.x) r in f \nexpecting :: {x = a4 | r5} -> a4",
        ELet("f", EAbs("r", EApp( EPrim(RecordSelect "x"), EVar "r")), EVar "f" )

    let r5 =
        "r5: fun r -> (_.x) r\nexpecting :: {x = a3 | r2} -> a3",
        EAbs("r", EApp( EPrim(RecordSelect "x") , EVar "r") )

    let b1 =
        "b1: let id = fun x -> x",
        ELet ("id", EAbs("x", EVar "x"), EVar "id")

    let b2 =
        "b2",
        ELet ("id", EAbs( "x", EVar "x"), EApp(EVar "id", EVar "id"))

    let b3 =
        "b3",
        ELet( "id", (EAbs("x", ELet( "y", EVar "x", EVar "y"))), EApp(EVar "id", EVar "id"))

    let b4 =
        "b4",
        ELet( "id", EAbs( "x", ELet("y", EVar "x", EVar "y")), EApp(EApp(EVar "id", EVar "id") ,EPrim (Int 2)))

    let b5 =
        "b5: fail infinite type rank 2 needed",
        ELet("id", EAbs( "x", EApp(EVar "x", EVar "x")), EVar "id")

    let b6 =
        "b6: let m y = let x = y true in x",
        EAbs("m", (ELet("y", EVar "m", ELet("x", (EApp(EVar "y", EPrim(Bool true))), EVar "x"))))

    let b7 =
          "b6: fun f -> (fun g -> (fun arg (f g arg)))",
          EAbs("f", EAbs("g", EAbs("arg", EApp(EVar("g"), EApp(EVar("f"), EVar("arg"))))))

    let testBank = [r1; r2; r3; r4; r5; b1; b2; b3; b4; b6; b7]

    let runTestBank bank printResult =
      bank
      |> List.iter (fun (name, exp) -> HMPureRowpolymorphism.resetId()
                                       let result = HMPureRowpolymorphism.typeInference Map.empty exp
                                       if printResult then
                                            printfn "%s" name
                                            printfn "Expression: %A" exp
                                            printfn "inferred: %s\n" (HMPureRowpolymorphism.Typ.toString result))

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
