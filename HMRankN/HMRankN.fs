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

/// Get the free TyVars from a type; no duplicates in result
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
        | bound, ForAll(tvs, ty), acc -> go (List.append tvs bound) ty acc
    List.foldBack (go []) tys []

/// Get all the binders used in ForAlls in the type, so that
/// when quantifying an outer for-all we can avoid these inner ones
let tyVarBndrs ty =
    let rec bndrs ty =
        match ty with
        | ForAll(tvs, body) -> List.append tvs (bndrs body)
        | Fun(arg, res) -> List.append (bndrs arg) (bndrs res)
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
    ref := (Some ty)

let readTv (metatv: MetaTv) : Tau option =
    match metatv with
    | Meta(_, ref) -> !ref

/// Instantiate the topmost for-alls of the argument type
/// with flexible type variables
let instantiate (ty:Sigma) tcenv : Rho =
    match ty with
    | ForAll(tvs, ty) ->
        let tvs' = List.map (fun _ -> newMetaTyVar tcenv) tvs
        substTy tvs (List.map MetaTv tvs') ty
    | _ -> ty

/// Performs deep skolemisation, retuning the 
/// skolem constants and the deepskol type
let rec deepskol tcenv (ty: Sigma) =
    match ty with
    | ForAll(tvs, ty) -> // Rule PRPOLY
        let sks1 = List.map (newSkolemTyVar tcenv) tvs
        let (sks2, ty') = deepskol tcenv (substTy tvs (List.map TyVar sks1) ty)
        List.append sks1 sks2, ty'
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
    | _ -> [], ty

/// a,b,..z, a1, b1,... z1, a2, b2,... 
let allBinders =
    let rec loop i =
        match i with
        | i when i < 26 -> BoundTv <| string (char (i + 97))
        | other -> BoundTv <| string (other / 26) + string(char ((other % 26) + 97))
    Seq.initInfinite ( fun i -> loop i  )

/// Eliminate any substitutions in the type
let rec zonkType typ =
    match typ with
    | ForAll(ns, ty) ->
        let ty' = zonkType ty 
        ForAll(ns, ty')
    | Fun(arg, res)  ->
        let arg' = zonkType arg 
        let res' = zonkType res
        Fun(arg', res')
    | TyCon tc -> TyCon tc
    | TyVar n -> TyVar n
    | MetaTv tv -> // A mutable type variable
        let mb_ty = readTv tv
        match mb_ty with
        | None -> MetaTv tv
        | Some ty ->
            let ty' = zonkType ty
            writeTv tv ty' // "Short out" multiple hops
            ty'

/// Quantify over the specified type variables (all flexible)
let quantify (tvs: MetaTv list) (ty: Rho) =
    let used_bndrs = tyVarBndrs ty  // Avoid quantified type variables in use
    let new_bndrs = List.difference (Seq.toList(Seq.take (List.length tvs) allBinders)) used_bndrs
    let bind (tv, name) = writeTv tv (TyVar name)
    List.zip tvs new_bndrs |> List.iter bind // 'bind' is just a cunning way of doing the substitution
    let ty' = zonkType ty
    ForAll(new_bndrs, ty')
    
/// Getting the free tyvars
let getEnvTypes env : Typ list =
    // Get just the types mentioned in the environment
    Map.values env |> Set.toList
    
/// This function takes account of zonking, and returns a set
/// (no duplicates) of unbound meta-type variables
let getMetaTyVars tys : MetaTv list = 
    let tys' = List.map zonkType tys
    metaTvs tys'

/// This function takes account of zonking, and returns a set
/// (no duplicates) of free type variables
let getFreeTyVars tys =
     let tys' = List.map zonkType tys
     freeTyVars tys'

///Tells which types should never be encountered during unification
let (|BadType|) : Tau -> bool = function
    | TyVar(BoundTv _) -> true
    | _ -> false

/// Raise an occurs-check error
let occursCheckErr (tv:MetaTv) (ty:Tau) =
    failwithf "Occurs check for '%A' in %A" tv ty
  //TODO: work out pretty print
  //= failTc (text "Occurs check for" <+> quotes (ppr tv) <+> text "in:" <+> ppr ty)

/// Invariant: the flexible type variable tv1 is not bound
let rec unifyUnboundVar tv1 ty2 =
    match tv1, ty2 with
    | tv1, MetaTv tv2 ->
        // We know that tv1 /= tv2 (else the top case in unify would catch it)
        let mb_ty2 = readTv tv2
        match mb_ty2 with
        | Some ty2' -> unify (MetaTv tv1) ty2'
        | None  -> writeTv tv1 ty2
    | _,  _ ->
        let tvs2 = getMetaTyVars [ty2]
        if  List.contains tv1 tvs2 then occursCheckErr tv1 ty2
        else writeTv tv1 ty2

/// Invariant: tv1 is a flexible type variable
and unifyVar tv1 ty2 =
// Check whether tv1 is bound
    let mb_ty1 = readTv tv1
    match mb_ty1 with
    | Some ty1 -> unify ty1 ty2
    | None  -> unifyUnboundVar tv1 ty2

/// unification
and unify ty1 ty2 =
    match ty1, ty2 with
    | BadType _, _ 
    | _, BadType _ ->  // Compiler error
        failwithf "Panic! Unexpected types in unification: %A, %A" ty1 ty2
        //todo figure out pretty printing error: <+> vcat [ppr ty1, ppr ty2])
    | (TyVar tv1),  (TyVar tv2) when tv1 = tv2 -> ()
    | (MetaTv tv1), (MetaTv tv2) when tv1 = tv2 -> ()
    | (MetaTv tv), ty -> unifyVar tv ty
    | ty, (MetaTv tv) -> unifyVar tv ty

    | Fun(arg1, res1), Fun(arg2, res2) ->
        unify arg1 arg2
        unify res1 res2

    | (TyCon tc1), (TyCon tc2) when tc1 = tc2 -> ()
    //TODO: figure out pretty printing error: <+> vcat [ppr ty1, ppr ty2]
    | ty1, ty2 -> failwithf "Cannot unify types: %A, %A" ty1 ty2