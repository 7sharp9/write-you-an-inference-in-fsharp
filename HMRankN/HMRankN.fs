module HMRankN
open System
open ExtCore
open System
open System.Diagnostics.Tracing
open System.Diagnostics

type Name = String
type Uniq = int

type TyVar =
    | BoundTv of String         //A type variable bound by a ForAll
    | SkolemTv of String * Uniq // A skolem constant; the String is 

type TyCon = IntT | BoolT | Pair2T

type Typ =
    | ForAll of TyVar list * Rho //Forall type
    | Fun of  Typ * Typ          // Function type
    | TyCon of TyCon             // Type constants
    | TyVar of TyVar             // Always bound by a ForAll
    | MetaTv of MetaTv           // A meta type variable

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

///Get the free TyVars from a type; no duplicates in result
let freeTyVars tys =
    //Ignore occurrences of bound type variables
    //Type to look at
    //Accumulates result
    let rec go bound ty acc =
        match bound, ty, acc with
        | bound, TyVar tv, acc ->
            match tv with
            | tv when List.contains tv bound -> acc
            | tv when List.contains tv acc -> acc
            | _otherwise -> tv :: acc
        | _bound, MetaTv _, acc -> acc
        | _bound, TyCon _, acc -> acc
        | bound, Fun(arg, res), acc -> go bound arg (go bound res acc)
        | bound, ForAll(tvs, ty), acc -> go (tvs ++ bound) ty acc
    List.foldBack (go []) tys []

///Get all the binders used in ForAlls in the type, so that
///when quantifying an outer for-all we can avoid these inner ones
let tyVarBndrs ty =
    let rec bndrs ty =
        match ty with
        | ForAll(tvs, body) -> tvs ++ (bndrs body)
        | Fun(arg, res) -> (bndrs arg) ++ (bndrs res)
        | _ -> []
    List.distinct (bndrs ty)

let tyVarName = function
    | BoundTv n -> n
    | SkolemTv(n, _) -> n

type Env = (TyVar * Tau) list

let rec subst_ty (env:Env) tv =
    match tv with
    | Fun(arg, res)   -> Fun( (subst_ty env arg), (subst_ty env res))
    | TyVar n         -> match List.tryFind (fun (k,_v) -> k = n ) env with
                         | Some (_k,v) -> v
                         | None -> TyVar n
    | MetaTv tv       -> MetaTv tv
    | TyCon tc        -> TyCon tc
    | ForAll(ns, rho) ->
        let env' =
            //perf: Set.intersection?
            [for (n, ty') in env do
                if not (List.contains n ns) then
                    yield n, ty' ]
        ForAll(ns, (subst_ty env' rho))

and substTy tvs tys ty =
    subst_ty (List.zip tvs tys) ty

//Pretty printing omitted---------------------

//monad.hs
type TcEnv = { uniqs : Uniq ref;             // Unique supply
               var_env :  Map<Name,Sigma> }  // Type environment for term variables

//Dealing with the type environment-----------

let extendVarEnv var ty (env:TcEnv) =
    let extend (env:TcEnv) =
        { env with var_env = Map.add var ty env.var_env }
    extend env

let newTcRef v =
    ref v

let lookupVar n (env:Map<Name,Sigma>) =
    match Map.tryFind n env with
    | Some ty -> ty
    | None -> failwithf "Not in scope:'%A'" n

//Creating, reading, writing MetaTvs----------

let newUnique (tcenv:TcEnv) =
    let uniq = !tcenv.uniqs
    incr tcenv.uniqs
    uniq

let newMetaTyVar tcenv =
    let uniq = newUnique tcenv
    let tref = newTcRef None 
    Meta(uniq, tref)

let newTyVarTy tcenv =
    let tv = newMetaTyVar tcenv
    MetaTv tv

let newSkolemTyVar tcenv tv =
    let uniq = newUnique tcenv
    SkolemTv((tyVarName tv), uniq)

let writeTv (Meta(_, ref)) (ty: Tau) = 
    writeTcRef ref (Some ty)

//nstantiate the topmost for-alls of the argument type
//with flexible type variables
let instantiate (ty:Sigma) tcenv : Rho =
    match ty with
    | ForAll(tvs, ty) ->
        let tvs' = List.map (fun _ -> newMetaTyVar tcenv) tvs
        substTy tvs (List.map MetaTv tvs') ty
    | _ -> ty

///Performs deep skolemisation, retuning the 
///skolem constants and the deepskol type
//deepskol :: Sigma -> Tc ([TyVar], Rho)
let rec deepskol tcenv (ty: Sigma) =
    match ty with
    | ForAll(tvs, ty) -> // Rule PRPOLY
        let sks1 = List.map (newSkolemTyVar tcenv) tvs
        let (sks2, ty') = deepskol tcenv (substTy tvs (List.map TyVar sks1) ty)
        sks1 ++ sks2, ty'
    | Fun(arg_ty, res_ty) -> // Rule PRFUN
        let sks, res_ty' = deepskol tcenv res_ty
        sks, Fun(arg_ty, res_ty')
    | ty -> // Rule PRMONO
        [], ty

let shallowskol (ty : Sigma) tcenv =
    match ty with
    | ForAll(tvs, ty) ->
        let sks1 = List.map (newSkolemTyVar tcenv) tvs
        sks1, ty
    | _ -> [], 

//reference implementation is allBinders :: [TyVar]
// a,b,..z, a1, b1,... z1, a2, b2,... 
let allBinders =
  let rec loop i =
    match i with
      | i when i < 26 -> TyVar <| string (char (i + 97))
      | other -> TyVar <| string (other / 26) + string(char ((other % 26) + 97)) 
  Seq.initInfinite ( fun i -> loop i  )


