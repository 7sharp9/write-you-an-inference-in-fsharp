module HMMutableRowpolymorphism
open System
open ExtCore

type name = string

type expr =
    | Var of name
    | Call of expr * expr list
    | Fun of name list * expr
    | Let of name * expr * expr

      /// selecting value of label: `r.a`
    | RecordSelect of expr * name
      /// extending a record: `{a = 1 | r}`
    | RecordExtend of name * expr * expr
      /// deleting a label: `{r - a}`
    | RecordRestrict of expr * name
      /// empty record: `{}`
    | RecordEmpty

type id = int
type level = int

type ty =
    | TConst of name   
    | TApp of ty * ty list
    | TArrow of ty list * ty
    | TVar of tvar ref

      /// record type: `{<...>}`
    | TRecord of row
      /// empty row: `<>`
    | TRowEmpty
      /// row extension: `<a : _ | ...>`
    | TRowExtend of name * ty * row

/// The kind of rows - empty row, row variable, or row extension
and row = ty

and tvar =
    | Unbound of id * level
    | Link of ty
    | Generic of id

module exp =
    let toString expr : string =
        let rec tostringRec isSimple exp =
            match exp with
            | Var name -> name
            | Call(fnExpr, argList) ->
                tostringRec true fnExpr + "(" + String.concat ", " (List.map (tostringRec false) argList) + ")"
            | Fun(paramList, bodyExpr) ->
                    let funStr =
                        sprintf "fun %s -> %s" (String.concat " " paramList)  (tostringRec false bodyExpr)
                    if isSimple then sprintf "(%s)" funStr else funStr
            | Let(varName, valueExpr, bodyExpr) ->
                    let letStr =
                        sprintf "let %s = %s in %s" varName  (tostringRec false valueExpr) (tostringRec false bodyExpr)
                    if isSimple then sprintf "(%s)" letStr else letStr
            | RecordEmpty -> "{}"
            | RecordSelect(recordExpr, label) ->
                sprintf "%s.%s" (tostringRec true recordExpr) label
            | RecordRestrict(recordExpr, label) ->
                sprintf "{%s - %s }"  (tostringRec false recordExpr) label
            | RecordExtend(label, expr, recordExpr) ->
                    let rec appendElements str = function
                        | RecordEmpty -> str
                        | RecordExtend(label, expr, recordExpr) ->
                            appendElements (str + ", " + label + " = " + tostringRec false expr) recordExpr
                        | other_expr -> str + " | " + tostringRec false other_expr
                    "{" + appendElements (label + " = " + tostringRec false expr) recordExpr + "}"
        tostringRec false expr

module ty =
    let toString ty : string =
        let mutable idNameMap = HashMap.empty
        let count = ref 0
        let nextName () =
            let i = !count
            incr count
            let name =
                match i with
                | i when i >= 26 -> string(char (97 + i % 26)) + string (i / 26)
                | _ -> string(char (97 + i % 26))
            name
        let rec f isSimple = function
            | TConst name -> name
            | TApp(ty, tyArgList) ->
                    f true ty + "[" + String.concat ", " (tyArgList |> List.map (f false) ) + "]"
            | TArrow(paramTyList, returnTy) ->
                    let arrowTyStr =
                        match paramTyList with
                        | [singleTy] ->
                                let paramTyStr = f true singleTy
                                let returnTyStr = f false returnTy
                                sprintf "%s -> %s" paramTyStr returnTyStr
                        | _ ->
                                let paramTyListStr = String.concat ", " (paramTyList |> List.map (f false) )
                                let returnTyStr = f false returnTy
                                sprintf "(%s) -> %s" paramTyListStr returnTyStr
                    
                    if isSimple then sprintf "(%s)" arrowTyStr else arrowTyStr
            | TVar {contents = Generic id} -> 
                        
                            match idNameMap |> HashMap.tryFind id with
                            | Some ty -> ty
                            | None ->
                                let name = nextName()
                                idNameMap <- idNameMap |> HashMap.add id name 
                                name
                    
            | TVar {contents = Unbound(id, _)} -> "_" + string id
            | TVar {contents = Link ty} -> f isSimple ty
            | TRecord row_ty ->
                sprintf "{%s}" (f false row_ty)
            | TRowEmpty -> ""
            | TRowExtend(label, ty, rowTy) ->
                //replace with fold over stringbuilder?
                let rec appendElements str ty =
                    match ty with
                    | TRowEmpty -> str
                    | TRowExtend(label, ty, rowTy) ->
                            appendElements (str + ", " + label + " : " + f false ty) rowTy
                    | TVar {contents = Link ty} -> appendElements str ty
                    | otherTy -> str + " | " + f false otherTy
                appendElements (label + " : " + f false ty) rowTy
        
        let tyStr = f false ty
        if !count > 0 then
            let varNames =
                idNameMap
                |> HashMap.toSeq
                |> Seq.map (fun (k, v)  -> v )
                |> Seq.sort
            sprintf "forall[%s] %s" (String.concat " " varNames) tyStr
        else
            tyStr

let currentId = ref 0

let nextId() =
    let id = !currentId
    currentId := id + 1
    id

let resetId() = currentId := 0

let newVar level = TVar (ref (Unbound(nextId (), level)))
let newGenVar() = TVar (ref (Generic(nextId ())))

module Env =
    type env = HashMap<String, ty>
    let empty = HashMap.empty : env
    let extend env name ty =
        env |> HashMap.add name ty
    let lookup env name =
        env |> HashMap.tryFind name

let occursCheckAdjustLevels tvarId tvarLevel ty =
    let rec f ty =
        match ty with
        | TVar {contents = Link ty} -> f ty
        | TVar {contents = Generic _} as tvar -> failwithf "%A should not be matched here for ty: %A" tvar ty
        | TVar ({contents = Unbound(otherId, otherLevel)} as otherTvar) ->
            if otherId = tvarId then
                failwithf "recursive types are not allowed: %A" ty
            else
                if otherLevel > tvarLevel then
                    otherTvar := Unbound(otherId, tvarLevel)
                else ()
        | TApp(ty, tyArgList) ->
                f ty
                List.iter f tyArgList
        | TArrow(paramTyList, returnTy) ->
                List.iter f paramTyList
                f returnTy
        | TConst _ -> ()
        //Records
        | TRecord row -> f row
        | TRowExtend(_label, fieldTy, row) ->
            f fieldTy
            f row
        | TRowEmpty -> ()
    f ty

let rec unify (ty1) (ty2) =
    if ty1 == ty2 then ()
    else
        match (ty1, ty2) with
            | TConst(name1), TConst(name2) when name1 = name2 -> ()
            | TApp(ty1, tyArgList1), TApp(ty2, tyArgList2) ->
                    unify ty1 ty2
                    List.iter2 unify tyArgList1 tyArgList2
            | TArrow(paramTyList1, returnTy1), TArrow(paramTyList2, returnTy2) ->
                    List.iter2 unify paramTyList1 paramTyList2
                    unify returnTy1 returnTy2
            | TVar {contents = Link ty1}, ty2
            | ty1, TVar {contents = Link ty2} -> unify ty1 ty2
            | TVar {contents = Unbound(id1, _)}, TVar {contents = Unbound(id2, _)} when id1 = id2 ->
                    failwithf "Error: There should only a single instance of a particular type variable"
            | TVar ({contents = Unbound(id, level)} as tvar), ty
            | ty, TVar ({contents = Unbound(id, level)} as tvar) ->
                    occursCheckAdjustLevels id level ty
                    tvar := Link ty
            | TRecord row1, TRecord row2 -> unify row1 row2
            | TRowEmpty, TRowEmpty -> ()
            | TRowExtend(label1, fieldTy1, restRow1), (TRowExtend _ as row2) ->
                let restRow1TvarRefOption =
                    match restRow1 with
                    | TVar ({contents = Unbound _} as tvar_ref) -> Some tvar_ref
                    | _ -> None
                let restRow2 = rewriteRow row2 label1 fieldTy1
                match restRow1TvarRefOption with
                | Some {contents = Link _} -> failwithf "Error: recursive row type of %A" restRow1
                | _ -> ()
                unify restRow1 restRow2
            | _, _ ->
                failwithf "cannot unify types %s and %s"  (ty.toString ty1) (ty.toString ty2)

and rewriteRow row2 label1 fieldTy1 =
    match row2 with
    | TRowEmpty -> failwithf "row does not contain label %s" label1
    | TRowExtend(label2, fieldTy2, restRow2) when label2 = label1 ->
            unify fieldTy1 fieldTy2 ;
            restRow2
    | TRowExtend(label2, fieldTy2, restRow2) ->
            TRowExtend(label2, fieldTy2, rewriteRow restRow2 label1 fieldTy1)
    | TVar {contents = Link row2} -> rewriteRow row2 label1 fieldTy1
    | TVar ({contents = Unbound(id, level)} as tvar) ->
            let restRow2 = newVar level
            let ty2 = TRowExtend(label1, fieldTy1, restRow2)
            tvar := Link ty2
            restRow2
    | _ -> failwithf "row type expected"

let rec generalize level ty =
    match ty with
    | TVar {contents = Unbound(id, otherLevel)} when otherLevel > level ->
        TVar (ref (Generic id))
    | TApp(ty, tyArgList) ->
        TApp(generalize level ty, List.map (generalize level) tyArgList )
    | TArrow(paramTyList, returnTy) ->
        TArrow(paramTyList |> List.map (generalize level), generalize level returnTy)
    | TVar {contents = Link ty } ->
        generalize level ty
    | TRecord row ->
        TRecord (generalize level row)
    | TRowExtend(label, fieldTy, row) ->
        TRowExtend(label, generalize level fieldTy, generalize level row)
    | TVar {contents = Generic _ }
    | TVar {contents = Unbound _ }
    | TConst _
    | TRowEmpty as ty -> ty

let instantiate level ty =
    let mutable idVarMap = HashMap.empty
    let rec f ty =
        match ty with
        | TConst _ -> ty
        | TVar {contents = Link ty} -> f ty
        | TVar {contents = Generic id} ->
                match HashMap.tryFind id idVarMap with
                | Some ty -> ty
                | None ->
                    let var = newVar level
                    idVarMap <- HashMap.add id var idVarMap
                    var
        | TVar {contents = Unbound _} -> ty
        | TApp(ty, tyArgList) ->
                TApp(f ty, List.map f tyArgList)
        | TArrow(paramTyList, returnTy) ->
                TArrow(List.map f paramTyList, f returnTy)
        | TRecord row -> TRecord (f row)
        | TRowEmpty -> ty
        | TRowExtend(label, fieldTy, row) ->
            TRowExtend(label, f fieldTy, f row)
    f ty

let rec matchFunTy numParams ty =
    match ty with
    | TArrow(paramTyList, returnTy) ->
            if List.length paramTyList <> numParams then
                failwithf "unexpected number of arguments, expected %i but was %i" numParams (List.length paramTyList)
            else paramTyList, returnTy
    | TVar {contents = Link ty} -> matchFunTy numParams ty
    | TVar ({contents = Unbound(_id, level)} as tvar) ->
            let paramTyList = 
                let rec loop i =
                    match i with
                    | 0 -> []
                    | n -> newVar level :: loop (n - 1)
                loop numParams
            let returnTy = newVar level
            tvar := Link (TArrow(paramTyList, returnTy))
            paramTyList, returnTy
    | other -> failwithf "expected a function but was a %A" other

let rec infer env level exp =
        match exp with
        | Var name ->
                match Env.lookup env name with
                | Some v -> instantiate level v
                | None -> failwithf "variable %s not found" name
        | Fun(paramList, bodyExpr) ->
                let paramTyList = paramList |> List.map (fun _ -> newVar level) 
                let fnEnv =
                    List.fold2 (fun env paramName paramTy -> Env.extend env paramName paramTy) env paramList paramTyList
                let returnTy = infer fnEnv level bodyExpr
                TArrow(paramTyList, returnTy)
        | Let(varName, valueExpr, bodyExpr) ->
                let varTy = infer env (level + 1) valueExpr
                let generalizedTy = generalize level varTy
                infer (Env.extend env varName generalizedTy) level bodyExpr
        | Call(fnExpr, argList) ->
                let paramTyList, returnTy =
                    matchFunTy (List.length argList) (infer env level fnExpr)
                List.iter2
                    (fun paramTy argExpr -> unify paramTy (infer env level argExpr))
                    paramTyList argList
                returnTy
        | RecordEmpty -> TRecord TRowEmpty
        | RecordSelect(recordExpr, label) ->
                /// inlined code for Call of function with type `forall[a r] {label : a | r} -> a`
                let restRowTy = newVar level
                let fieldTy = newVar level
                let paramTy = TRecord (TRowExtend(label, fieldTy, restRowTy))
                let returnTy = fieldTy
                unify paramTy (infer env level recordExpr)
                returnTy
        | RecordRestrict(recordExpr, label) ->
                /// inlined code for Call of function with type `forall[a r] {label : a | r} -> {r}`
                let restRowTy = newVar level
                let fieldTy = newVar level
                let paramTy = TRecord (TRowExtend(label, fieldTy, restRowTy))
                let returnTy = TRecord restRowTy
                unify paramTy (infer env level recordExpr)
                returnTy
        | RecordExtend(label, expr, recordExpr) ->
                /// inlined code for Call of function with type `forall[a r] (a, {r}) -> {label : a | r}`
                let restRowTy = newVar level
                let fieldTy = newVar level
                let param1Ty = fieldTy
                let param2Ty = TRecord restRowTy
                let returnTy = TRecord (TRowExtend(label, fieldTy, restRowTy))
                unify param1Ty (infer env level expr)
                unify param2Ty (infer env level recordExpr)
                returnTy

