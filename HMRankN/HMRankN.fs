module HMRankN
open System
open ExtCore

type Name = String
type Uniq = int

type TyVar =
  | BoundTv of String         //A type variable bound by a ForAll
  | SkolemTv of String * Uniq // A skolem constant; the String is 

type TyCon = IntT | BoolT | Pair2T

type Typ =
  | ForAll of TyVar list * Rho //Forall type
  | Fun of  Typ * Typ        // Function type
  | TyCon of TyCon             // Type constants
  | TyVar of TyVar             // Always bound by a ForAll
  | MetaTv of MetaTv          // A meta type variable

and Rho = Typ //No top-level ForAll
and Tau = Typ //No ForAlls anywhere
and Sigma = Typ

and TyRef =
  Ref<Tau option>
        // `None` means the type variable is not substituted
        // `Some ty` means it has been substituted by 'ty'

and MetaTv = 
  | Meta of Uniq * TyRef // Can unify with any tau-type

module MetaTv =
  let equals m1 m2 =
    match m1, m2 with Meta(u1, _), Meta(u2, _) -> u1 = u2

module TyVar =
  let equals t1 t2 =
    match t1, t2 with
    | BoundTv s1, BoundTv s2 -> s1 = s2
    | SkolemTv(_, u1), SkolemTv(_, u2) -> u1 = u2
    | _ -> false

type Term =
  | Var of Name
  | Lit of int
  | App of Term * Term
  | Lam of Name * Term
  | ALam of Name * Sigma * Term
  | Let of Name * Term * Term
  | Ann of Term * Sigma

let atomicTerm = function
  | Var _ -> true
  | Lit _ -> true
  | _ -> false

let (-->) (arg:Sigma) (res:Sigma) : Sigma =
  Fun(arg, res)

let intType = TyCon IntT
let boolType = TyCon BoolT
let pair2Typ = TyCon Pair2T

let metaTvs types =
  let rec go t xs =
    match t, xs with
    | MetaTv tv, acc -> 
      match tv with
      | tv when List.contains tv acc -> acc
      | _otherwise -> tv :: acc
    | TyVar _, acc -> acc
    | TyCon _, acc -> acc
    | Fun(arg, res), acc -> go arg (go res acc)
    | ForAll(_, ty), acc -> go ty acc //ForAll binds TyVars only
  List.foldBack go types []

let freeTyVars tys =
  let rec go bound ty acc =
    match bound, ty, acc with
    | bound, TyVar tv, acc ->
      match tv with
      | tv when List.contains tv bound -> acc
      | tv when List.contains tv acc -> acc
      | _otherwise -> tv :: acc
    | bound, MetaTv _, acc -> acc
    | bound, TyCon _, acc -> acc
    | bound, Fun(arg, res), acc -> go bound arg (go bound res acc)
    | bound, ForAll(tvs, ty), acc -> go (tvs ++ bound) ty acc
    

  List.foldBack (go []) tys []

