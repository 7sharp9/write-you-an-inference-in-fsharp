module HMPure
open System
open ExtCore

type name = string
type label = string

type exp = 
    | EVar of name
    | EPrim of prim
    | EApp of exp * exp
    | EAbs of name * exp
    | ELet of name * exp * exp

and prim =
    | Int of int
    | Bool of bool
    | Cond

type Typ =
    | TVar of name
    | TInt
    | TBool
    | TFun of Typ * Typ

type Scheme = Scheme of name list * Typ

type TypeEnv = Map<string, Scheme>

type Subst = Map<name,Typ>

module Typ =
    let rec ftv (typ: Typ) =
        match typ with
        | TVar name -> Set.singleton name
        | TInt -> Set.empty
        | TBool -> Set.empty
        | TFun(t1, t2) -> Set.union (ftv t1) (ftv t2)
    
    let rec apply s typ =
        match typ with
        | TVar n ->
            match Map.tryFind n s with
            | Some t -> t
            | None -> TVar n
        | TFun(t1, t2) ->
            TFun (apply s t1, apply s t2)
        | TInt | TBool ->
            typ

    let parens s =
        sprintf "( %s )" s
        
    let braces s =
        sprintf "{ %s }" s
    let rec toString ty =
        let rec parenType ty =
            match ty with
            |  TFun(_type1, _type2) -> parens (toString ty)
            | _ -> toString ty

        match ty with
            | TVar name -> name
            | TInt -> "int"
            | TBool -> "bool"
            | TFun(t, s) ->
                (parenType t) + " -> " + (toString s)

module Scheme =
   let ftv (scheme: Scheme) =
       match scheme with
       | Scheme(variables, typ) ->
           Set.difference (Typ.ftv typ) (Set.ofList variables)

   let apply (s: Subst) (scheme: Scheme) =
       match scheme with
       | Scheme(vars, t) ->
           let newSubst = List.foldBack (fun key currentSubst -> Map.remove key currentSubst ) vars s
           let newTyp = Typ.apply newSubst t
           Scheme(vars, newTyp)

module TypeEnv =
     let remove (env: TypeEnv) (var : string)=
         Map.remove var env
    
     let ftv (typEnv: TypeEnv) =
        Seq.foldBack (fun (KeyValue(_key ,v)) state ->
            Set.union state (Scheme.ftv v)) typEnv Set.empty

     let apply (s : Subst) (env: TypeEnv) =
        Map.map (fun _k v -> Scheme.apply s v) env

module Subst =
    /// Apply `s1` to `s2` then merge the results
    let compose s1 s2 =
        Map.union (Map.map (fun _k (v : Typ) -> Typ.apply s1 v) s2) s1

///generalize abstracts a type over all type variables which are free
/// in the type but not free in the given type environment.
let generalize (env : TypeEnv) (t : Typ) =
    let variables =
       Set.difference (Typ.ftv t) (TypeEnv.ftv env)
       |> Set.toList 
    Scheme(variables, t)

let private currentId = ref 0

let nextId() =
    let id = !currentId
    currentId := id + 1
    id

let resetId() = currentId := 0

let newTyVar prefix =
    TVar ( sprintf "%s%i" prefix (nextId ()))

/// Replaces all bound type variables in a type scheme with fresh type variables.
let instantiate (ts : Scheme) =
    match ts with
    | Scheme(vars, t) ->
        let nvars = vars |> List.map (fun name -> newTyVar (string name.[0]) )
        let s = List.zip vars nvars |> Map.ofList
        Typ.apply s t

let varBind u t =
    match t with
    | TVar name when name = u -> Map.empty
    | _ when Set.contains u (Typ.ftv t) ->
        failwithf "Occur check fails: %s vs %A" u t
    | _ -> Map.singleton u t

let rec unify (t1 : Typ) (t2 : Typ) : Subst =
    match t1, t2 with
    | TFun (l, r), TFun (l', r') ->
        let s1 = unify l l'
        let s2 = unify (Typ.apply s1 r) (Typ.apply s1 r')
        Subst.compose s2 s1
    | TVar u, t
    | t, TVar u -> varBind u t
    | TInt, TInt -> Map.empty
    | TBool, TBool -> Map.empty
    | _ -> failwithf "Types do not unify: %A vs %A" t1 t2

let tiPrim prim =
    match prim with
    | Int _ -> TInt
    | Bool _ -> TBool
    | Cond -> 
        let a = newTyVar "a"
        TFun(TBool, TFun(a, TFun(a, a)))

let rec ti (env : TypeEnv) (exp : exp) : Subst * Typ =
    match exp with
    | EVar name ->
        match Map.tryFind name env with
        | None -> failwithf "Unbound variable: %s" name
        | Some sigma ->
            let t = instantiate sigma
            Map.empty, t
    | EPrim prim -> (Map.empty, tiPrim prim)
    | EAbs(n, e) ->
        let tv = newTyVar "a"
        let env1 = TypeEnv.remove env n
        let env2 = Map.union env1 (Map.singleton n (Scheme([], tv) ))
        let (s1, t1) = ti env2 e
        s1, TFun( Typ.apply s1 tv, t1)
    | EApp(e1, e2) ->
        let s1, t1 = ti env e1
        let s2, t2 = ti (TypeEnv.apply s1 env) e2
        let tv = newTyVar "a"
        let s3 = unify (Typ.apply s2 t1) (TFun(t2, tv))
        Subst.compose (Subst.compose s3 s2) s1, Typ.apply s3 tv
    | ELet(x, e1, e2) ->
        let s1, t1 = ti env e1
        let env1 = TypeEnv.remove env x
        let scheme = generalize (TypeEnv.apply s1 env) t1
        let env2  =  Map.add x scheme env1
        let s2, t2 = ti (TypeEnv.apply s1 env2 ) e2
        Subst.compose s2 s1, t2

let typeInference env e =
  let s, t = ti env e
  Typ.apply s t