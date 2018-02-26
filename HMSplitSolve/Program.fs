// Learn more about F# at http://fsharp.org

open System
open HMSplitSolve

[<EntryPoint>]
let main argv =
    let basicInference =
      Let ("id", Lam("x", Var "x"), Var "id")

    let result = inferTop TypeEnv.empty ["basicInference", basicInference] (InferState())
    printfn "Inference: %A" result

    let constraints, subst, typ, scheme = constraintsExpr basicInference TypeEnv.empty (InferState())
    printfn "Constraints: %A" constraints
    printfn "Substitutions: %A" subst
    printfn "Type: %A" typ
    printfn "Scheme: %A" scheme
    0 // return an integer exit code
