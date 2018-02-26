module HMSplitSolve
open System
open ExtCore


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

type ConstraintList = Constraint list

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
  let apply (s: Subst) ( (as', t) : Scheme) : Scheme =
    let s' : Subst = List.foldBack (fun k v -> Map.remove k v ) as' s
    as', Typ.apply s' t

  let ftv ((vars, t): Scheme) =
    Set.difference (Typ.ftv t) (Set.ofList vars)

module Constraint =
  let rec apply (s: Subst) ((t1, t2): Constraint) =
      (Typ.apply s t1, Typ.apply s t2)

  let rec ftv ((t1, t2): Constraint) =
    Set.union (Typ.ftv t1) (Typ.ftv t2) 

module List = 
  let private apply apply (s: Subst) xs  =
    List.map (apply s) xs
    
  let private ftv ftv xs  =
    List.foldBack (fun (_key, v) state ->
      Set.union state (ftv v)) xs Set.empty

  module Scheme =
    let apply = apply Scheme.apply
    let ftv = ftv Scheme.ftv

  module Constraint =
    let apply = apply Constraint.apply
    let ftv xs = ftv Constraint.ftv xs

  module Typ =
    let apply = apply Typ.apply
    let ftv xs = ftv Typ.ftv xs

module Env =
  let apply s (env: TypeEnv) : TypeEnv =
    Map.map (fun _k v -> Scheme.apply s v) env

  let ftv (env: TypeEnv)  =
    List.Scheme.ftv (Map.toList env)

type TypeError =
  | UnificationFail of Typ * Type
  | InfiniteType of TVar * Typ
  | UnboundVariable of string
  | Ambigious of Constraint list
  | UnificationMismatch of Typ[] * Typ[]

// inference ---------------------------------------------

//let runInfer env m =

//let inferExpr env ex =

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

let generalize (env: TypeEnv) t : Scheme =
  let as' = Set.toList <| Set.difference (Typ.ftv t) (Env.ftv env)
  (as', t)

///create a localised environment with modifyEnv, then run computation with env
let private local (modifyEnv: TypeEnv -> TypeEnv) computation env =
  let newEnv = modifyEnv env
  computation newEnv

///Remove and extend:- remove x from m then add (x, sc) then run computation `m` in env
let inEnv (x, sc) (e:TypeEnv) m : Typ * Constraint list = 
  let scope e =  TypeEnv.extend (TypeEnv.remove e x) (x, sc)
  local scope m e
  
let lookupEnv name env state =
  match Map.tryFind name env with
  | Some (s: Scheme) -> instanatiate s state
  | None -> failwithf "unbound varaible: %A" name
 
let (++) = List.append

let ops binop =
  match binop with
  | Add | Mul | Sub -> TArr(typeInt, TArr(typeInt, typeInt))
  | Eql -> TArr(typeInt, TArr(typeInt, typeBool))

let rec infer expr inferState env : Typ * Constraint list =
  match expr with
  | Lit(LInt _) -> (typeInt, [])
  | Lit(LBool _) -> (typeBool, [])
  | Var x ->
    let t = lookupEnv x env inferState
    (t, [])

  | Lam(x, e) ->
    let tv = fresh inferState
    let (t, c) =  inEnv (x, ([], tv)) env (infer e inferState)
    (TArr(tv, t), c)

   | App(e1, e2) ->
    let (t1, c1) = infer e1 inferState env
    let (t2, c2) = infer e2 inferState env
    let tv = fresh inferState
    (tv, c1 ++ c2 ++ [t1, TArr(t2, tv)] )

   | Let(x, e1, e2) -> 
     let (t1, c1) = infer e1 inferState env
     let sub = solver (Map.empty, c1)
     let sc = generalize (Env.apply sub env) (Typ.apply sub t1)
     let (t2, c2) = 
       inEnv (x, sc) env (local (Env.apply sub) (infer e2 inferState))
     (t2, c1 ++ c2)

   | Fix e1  ->
     let t1, c1 = infer e1 inferState env
     let tv = fresh inferState
     (tv, c1 ++ [(TArr(tv, tv), t1)])

   | Op(op, e1, e2) ->
     let (t1, c1) = infer e1 inferState env
     let (t2, c2) = infer e2 inferState env
     let tv = fresh inferState
     let u1 = TArr(t1, TArr(t2, tv))
     let u2 = ops op
     (tv, c1 ++ c2 ++ [(u1, u2)])

   | If(cond, tr, fl) ->
     let (t1, c1) = infer cond inferState env
     let (t2, c2) = infer tr inferState env
     let (t3, c3) = infer fl inferState env
     (t2, c1 ++ c2 ++ c3 ++ [(t1, typeBool); (t2, t3)])

let normalize ((_, body) :Scheme) : Scheme =
  let rec fv typ =
    match typ with
    | TVar a -> [a]
    | TArr(a, b) -> fv a ++ fv b
    | TCon _ -> []
  let ord = 
    List.distinct (fv body)
    |> List.mapi (fun i v -> v,  TV <| Seq.item i letters)
  let rec normType typ =
    match typ with
    | TArr(a, b) -> TArr(normType a, normType b)
    | TCon a -> TCon a
    | TVar a -> 
        match Map.ofList ord |> Map.tryFind a with
        | Some x -> TVar x
        | None -> failwith "type variable not in signature"
  List.map snd ord, normType body

// constraint solver -----------------------------

///compose substitutions
let compose (s1:Subst) (s2: Subst) : Subst =
  Map.union (Map.map (fun _k v -> Typ.apply s1 v) s2) s1

let occursCheck a t =
  Set.contains a (Typ.ftv t)

let bind a t =
  match a, t with
  | a, t when (TVar a) == t  -> Map.empty
  | a, t when occursCheck a t -> failwithf "InfiniteType %A %A"  a t
  | _otherwise -> Map.singleton a t

let rec unifyMany ts1 ts2 =
  match ts1, ts2 with
   | [], [] -> Map.empty
   | (t1 :: ts1), (t2 :: ts2) ->
     let su1 = unifies t1 t2
     let su2 = unifyMany (List.Typ.apply su1 ts1) (List.Typ.apply su1 ts2)
     compose su2 su1
   | t1, t2 -> failwithf "UnificationMismatch: %A %A" t1 t2

and unifies t1 t2 =
  match t1, t2 with
  | t1, t2 when t1 == t2 -> Map.empty
  | TVar v, t | t, TVar v -> bind v t
  | TArr(t1, t2), TArr(t3, t4) -> unifyMany [t1; t2] [t3; t4]
  | t1, t2 -> failwithf "UnificationFail: %A %A" t1 t2

///unification solver
let rec solver ((su, cs) : Unifier) =
  match cs with
    | [] ->  su
    | ((t1, t2) :: cs0) -> 
      let su1  = unifies t1 t2
      solver (compose su1 su, List.Constraint.apply su1 cs0)

//run the constraint solver
let runSolve cs =
  let st = (Map.empty, cs)
  solver st




  