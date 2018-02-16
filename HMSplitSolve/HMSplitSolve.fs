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
type InferState =
  { count : int }
  static member initial = {count = 0}

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