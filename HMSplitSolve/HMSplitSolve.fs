module HMSplitSolve
open System


type TVar = TV of String

type Typ =
  | TVar of TVar
  | TCon of string
  | TArr of Typ * Typ

type Scheme = (TVar list * Typ)

let typeInt = TCon "Int"
let typeBool = TCon "Bool"

type Name = string

type Lit =
  | LInt of int
  | LBool of bool

type Binop = Add | Sub | Mul | Eql

type Expr =
  | Var of Name
  | App of Expr * Expr
  | Lam of Name * Expr
  | Let of Name * Expr * Expr
  | Lit of Lit
  | If of Expr * Expr * Expr
  | Fix of Expr
  | Op of Binop * Expr * Expr

type Decl = (String * Expr)

type Program = Program of Decl list * Expr

type TypeEnv = Map<Name, Scheme>

module TypeEnv =
  let empty = Map.empty<Name,Scheme>

  let extend (env : TypeEnv) (x, s) =
    Map.add x s env

  let remove (env : TypeEnv) var =
    (Map.remove var env)

  let extends (env : TypeEnv) xs =
    Map.union (Map.ofList xs) env

  let lookup key (env : TypeEnv) = Map.tryFind key env

  let merge (a : TypeEnv) (b : TypeEnv) =
    Map.union a b

  let mergeEnvs (envs : TypeEnv list)  =
    List.fold merge empty envs

  let singleton x y = Map.singleton x y

  let keys (env : TypeEnv) = Map.keys env

  let fromList xs : TypeEnv = 
    Map.ofList xs

  let toList (env : TypeEnv) = Map.toList env

// Inference state
type InferState() =
  let current = ref 0
  member __.incr() = current := !current + 1
  member __.count = !current


type Constraint = (Typ * Typ)

type Subst = Map<TVar,Typ>

type Unifier = (Subst * Constraint list)

module Typ =
  let rec apply s ty =
    match ty with
    | TCon a -> TCon a
    | TVar a as t ->
      match Map.tryFind a s with
      | Some m -> m
      | None -> t
    | TArr(t1, t2) -> TArr(apply s t1, apply s t2)

  let rec ftv typ =
    match typ with
    | TCon _ -> Set.empty
    | TVar a -> Set.singleton a
    | TArr(t1, t2) -> Set.union (ftv t1) (ftv t2)

module Scheme =
  let apply (s: Subst) ( (vars, t) : Scheme) =
    let newSubst = List.foldBack (fun k v -> Map.remove k v ) vars s
    Typ.apply newSubst t

  let ftv ((vars, t): Scheme) =
    Set.difference (Typ.ftv t) (Set.ofList vars)

module Constraint =
  let rec apply (s: Subst) ((t1, t2): Constraint) =
      (Typ.apply s t1, Typ.apply s t2)

  let rec ftv ((t1, t2): Constraint) =
    Set.union (Typ.ftv t1) (Typ.ftv t2) 

module Env =
  let apply s env =
    Map.map (fun _k v -> Scheme.apply s v) env

  let ftv env =
    Seq.foldBack (fun (KeyValue(_key ,v)) state ->
      Set.union state (Scheme.ftv v)) env Set.empty

type TypeError =
  | UnificationFail of Typ * Type
  | InfiniteType of TVar * Typ
  | UnboundVariable of string
  | Ambigious of Constraint list
  | UnificationMismatch of Typ[] * Typ[]

let letters =
  let rec loop i =
    match i with
      | i when i < 26 -> string (char (i + 97))
      | other -> 
        loop ( (other / 26) - 1) + string(char ((other % 26) + 97)) 
  Seq.initInfinite ( fun i -> loop i  )

let const' a _ = a

///Given the current inference state return a fresh TVar with updated inference state
let fresh (s: InferState) =
  s.incr()
  TVar(TV (letters |> Seq.item s.count) )

let instanatiate ((vars, t): Scheme) (is: InferState) =
  let as' = List.map (fun a -> fresh is ) vars
  let s = Map.ofList <| List.zip vars as'
  Typ.apply s t

let lookupEnv name env state =
  match Map.tryFind name env with
  | Some (s: Scheme) -> instanatiate s state
  | None -> failwithf "unbound varaible: %A" name
 
///Remove and extend:- remove x from m then add (x, sc)
let inEnv (x, sc) (m:TypeEnv) = 
  let scope env =  TypeEnv.extend (TypeEnv.remove env x) (x, sc)
  scope m

let (++) = List.append

let compose (s1:Subst) (s2: Subst) : Subst =
  Map.union (Map.map (fun _k v -> Typ.apply s1 v) s2) s1

let rec infer expr env inferState : Typ * Constraint list =
  match expr with
  | Lit(LInt _) -> (typeInt, [])
  | Lit(LBool _) -> (typeBool, [])
  | Var x ->
    let t = lookupEnv x env inferState
    (t, [])
  | Lam(x, e) ->
    let tv = fresh inferState
    let newEnv = inEnv (x, ([], tv)) env
    let (t, c) = infer e newEnv inferState
    (TArr(tv, t), c)

   | App(e1, e2) ->
    let (t1, c1) = infer e1 env inferState
    let (t2, c2) = infer e2 env inferState
    let tv = fresh inferState
    
    (tv, c1 ++ c2 ++ [t1, TArr(t2, tv)] )

//let inferExpr env expr : Result<Scheme, TypeError> =
  