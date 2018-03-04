open System
open HMBasic

[<EntryPoint>]
let main argv =

    let pair = Apply(Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))), Apply(Ident("f"), Ident("true")))
  
    let example1 =
        "example1",
        LetRec("factorial", (* letrec factorial = *)
          Lambda("n",    (* fn n => *)
            Apply(
              Apply(   (* cond (zero n) 1 *)
                Apply(Ident("cond"),     (* cond (zero n) *)
                  Apply(Ident("zero"), Ident("n"))),
                Ident("1")),
              Apply(    (* times n *)
                Apply(Ident("times"), Ident("n")),
                Apply(Ident("factorial"),
                  Apply(Ident("pred"), Ident("n")))
              )
            )
          ),      (* in *)
          Apply(Ident("factorial"), Ident("5"))
        )

    (* Should fail: *)
    (* fn x => (pair(x(3) (x(true))) *)
    let example2 =
        "example2",
        Lambda("x",
            Apply(
              Apply(Ident("pair"),
                  Apply(Ident("x"), Ident("3"))),
              Apply(Ident("x"), Ident("true"))))

    (* pair(f(3), f(true)) *)
    let example3 =
        "example3",
        Apply(
            Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))),
            Apply(Ident("f"), Ident("true")))

    (* letrec f = (fn x => x) in ((pair (f 4)) (f true)) *)
    let example4 =
        "example4",
        Let("f", Lambda("x", Ident("x")), pair);

    (* fn f => f f (fail) *)
    let example5 =
        "example5",
        Lambda("f", Apply(Ident("f"), Ident("f")));

    (* let g = fn f => 5 in g g *)
    let example6 =
        "example6",
        Let("g",
            Lambda("f", Ident("5")),
            Apply(Ident("g"), Ident("g")));

    (* example that demonstrates generic and non-generic variables: *)
    (* fn g => let f = fn x => g in pair (f 3, f true) *)
    let example7 =
       "example7",
        Lambda("g",
           Let("f",
             Lambda("x", Ident("g")),
             Apply(
              Apply(Ident("pair"),
                  Apply(Ident("f"), Ident("3"))
              ),
              Apply(Ident("f"), Ident("true")))));

    (* Function composition *)
    (* fn f (fn g (fn arg (f g arg))) *)
    let example8 =
        "example8",
        Lambda("f", Lambda("g", Lambda("arg", Apply(Ident("g"), Apply(Ident("f"), Ident("arg"))))))

    let basicEnv =
        let var1 = makeVariable ()
        let var2 = makeVariable ()
        let pairTy = TypeOperator({ name = "*"; types = [var1; var2] })
        let var3 = makeVariable ()
        [ ("pair", makeFunctionType var1 (makeFunctionType var2 pairTy))
          ("true", boolType)
          ("cond", makeFunctionType boolType (makeFunctionType var3 (makeFunctionType var3 var3)))
          ("zero", makeFunctionType intType boolType)
          ("pred", makeFunctionType intType intType)
          ("times", makeFunctionType intType (makeFunctionType intType intType))
        ]

    let testBank = [example1; example2; example3; example4; example5; example6; example7; example8]

    let runTestBank bank printResult =
      bank
      |> List.iter (fun (name, exp) -> nextVariableId := 0
                                       let result =
                                         try Result.Ok (analyse exp basicEnv)
                                         with ex -> Result.Error (ex.Message)
                                       if printResult then
                                            printfn "%s" name
                                            printfn "Expression: %s" (HMBasic.exp.toString exp)
                                            match result with
                                            | Ok result ->
                                                printfn "inferred: %s\n" (HMBasic.ty.toString result)
                                            | Result.Error error ->
                                                printfn "inferred: %s\n" error )

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
