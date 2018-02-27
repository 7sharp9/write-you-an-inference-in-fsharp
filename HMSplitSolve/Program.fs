// Learn more about F# at http://fsharp.org

open System
open HMSplitSolve

[<EntryPoint>]
let main argv =
    let b1 =
      Let ("id", Lam("x", Var "x"), Var "id")
    let b2 =
      Let ("id", Lam( "x", Var "x"), App(Var "id", Var "id"))
    let b3 =
      Let( "id", (Lam("x", Let( "y", Var "x", Var "y"))), App(Var "id", Var "id"))
    let b4 =
      Let( "id", Lam( "x", Let("y", Var "x", Var "y")), App(App(Var "id", Var "id"), Lit (LInt 2)))
    let b5 =
      Let("id", Lam( "x", App(Var "x", Var "x")), Var "id")
    let b6 =
      Lam("m", (Let("y", Var "m", Let("x", (App(Var "y", Lit(LBool true))), Var "x"))))
    let b7 =
      Lam("f", Lam("g", Lam("arg", App(Var("g"), App(Var("f"), Var("arg"))))))

    let result = inferTop TypeEnv.empty ["b7", b7] (InferState())
    printfn "Inference: %A" result

    let constraints, subst, typ, scheme = constraintsExpr b7 TypeEnv.empty (InferState())
    printfn "Constraints: %A" constraints
    printfn "Substitutions: %A" subst
    printfn "Type: %A" typ
    printfn "Scheme: %A" scheme
    0 // return an integer exit code
