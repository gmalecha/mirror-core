(** Module types for monads **)
(*****************************)
module type MONAD =
sig
  type 'a m

  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val ret : 'a -> 'a m
end

module type STATE =
sig
  type state
  type 'a m

  val get : state m
  val put : state -> unit m
end

module type READER =
sig
  type env
  type 'a m

  val ask : env m
  val local : (env -> env) -> 'a m -> 'a m
end

(** Module types for reification **)
(**********************************)
module type REIFY =
sig
  type result
  type 'a m

  val reify : Term.constr -> result m
end

module type REIFY_APP =
sig
  type result
  type 'a m

  val reify_app : result m Lazy.t ->
                  (Term.constr -> result m) ->
                  (result -> result list -> result m) ->
                  Term.constr -> Term.constr array -> result m
end

(** Reification Instances **)
(***************************)

module ReifyMap (R : REIFY)
		(F : sig type result
			 val map : R.result R.m -> result R.m
  		     end)
		: REIFY with type result = F.result
  		        with type 'a m = 'a R.m =
struct
  type result = F.result
  type 'a m = 'a R.m

  let reify t = F.map (R.reify t)
end

(** Reification based on environments of terms.
 **)
module ReifyEnv
  (M : MONAD)
  (S : STATE with type state = Term.constr option list
             with type 'a m = 'a M.m)
  : REIFY with type 'a m = 'a M.m
          with type result = int =
struct
  type result = int
  type 'a m = 'a M.m

  let env_get k =
    let rec env_get i x =
      match x with
	[] -> None
      | Some x :: xs ->
	if Term.eq_constr x k
	then Some i
	else env_get (i+1) xs
      | None :: xs ->
	env_get (i+1) xs
    in env_get 0

  let env_app a b =
    (List.append a [Some b], List.length a)

  let reify (t : Term.constr) : int m =
    M.bind S.get (fun e ->
      match env_get t e with
	Some i -> M.ret i
      | None ->
	let (new_e, res) = env_app e t in
	M.bind (S.put new_e) (fun _ ->
	  M.ret res))
end


(** return true if the term is an arrow (as opposed to a product) **)
let as_arrow t =
  try
    let (_,lt,rt) = Term.destProd t in
    if Term.noccurn 0 rt then
      Some (lt, rt)
    else
      None
  with
    Invalid_argument _ -> None

module Std (C : sig val contrib_name : string end) =
struct
  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    let re = Coqlib.find_reference C.contrib_name path tm in
    Libnames.constr_of_global re

  let datatypes_pkg = ["Coq";"Init";"Datatypes"]
  let none = lazy (resolve_symbol datatypes_pkg "None")
  let some = lazy (resolve_symbol datatypes_pkg "Some")

  let to_option typ (x : Term.constr option) =
    match x with
      None -> Term.mkApp (Lazy.force none, [| typ |])
    | Some x -> Term.mkApp (Lazy.force some, [| typ ; x |])

  let to_positive =
    let pos_pkg = ["Coq";"Numbers";"BinNums"] in
    let xH = lazy (resolve_symbol pos_pkg "xH") in
    let xO = lazy (resolve_symbol pos_pkg "xO") in
    let xI = lazy (resolve_symbol pos_pkg "xI") in
    let rec to_positive n =
      if n = 1 then
	Lazy.force xH
      else
	if n mod 2 = 0 then
	  Term.mkApp (Lazy.force xO, [| to_positive (n / 2) |])
	else
  	  Term.mkApp (Lazy.force xI, [| to_positive (n / 2) |])
    in
    fun n ->
      if n <= 0
      then raise (Invalid_argument ("to_positive: " ^ string_of_int n))
      else to_positive n

  let to_N =
    let n_pkg = ["Coq";"Numbers";"BinNums"] in
    let o = lazy (resolve_symbol n_pkg "N0") in
    let pos = lazy (resolve_symbol n_pkg "Npos") in
    fun n ->
      if n = 0
      then Lazy.force o
      else
	if n < 0
	then raise (Invalid_argument ("to_N: " ^ string_of_int n))
	else Term.mkApp (Lazy.force pos, [| to_positive n |])

  let to_nat =
    let s = lazy (resolve_symbol datatypes_pkg "S") in
    let o = lazy (resolve_symbol datatypes_pkg "O") in
    let rec to_nat n =
      if n = 0 then
	Lazy.force o
      else
	Term.mkApp (Lazy.force s, [| to_nat (n - 1) |])
    in
    fun n ->
      if n < 0
      then raise (Invalid_argument ("to_nat: " ^ string_of_int n))
      else to_nat n

  let to_list =
    let c_nil = lazy (resolve_symbol datatypes_pkg "nil") in
    let c_cons = lazy (resolve_symbol datatypes_pkg "cons") in
    fun typ ->
      let the_nil = Term.mkApp (Lazy.force c_nil, [| typ |]) in
      let rec to_list (ls : Term.constr list) : Term.constr =
	match ls with
	  [] -> the_nil
	| l :: ls ->
	  Term.mkApp (Lazy.force c_cons, [| typ ; l ; to_list ls |])
      in to_list

  type 'a pmap =
  | PM_Empty
  | PM_Branch of 'a pmap * 'a option * 'a pmap

  let rec pmap_add k v m =
    if k = 1 then
      match m with
	PM_Empty -> PM_Branch (PM_Empty, Some v, PM_Empty)
      | PM_Branch(l,_,r) -> PM_Branch (l, Some v, r)
    else
      if k mod 2 = 0 then
	match m with
	  PM_Empty -> PM_Branch (pmap_add (k / 2) v PM_Empty, None, PM_Empty)
	| PM_Branch (l,d,r) -> PM_Branch (pmap_add (k / 2) v l, d, r)
      else
	match m with
	  PM_Empty -> PM_Branch (PM_Empty, None, pmap_add (k / 2) v PM_Empty)
	| PM_Branch (l,d,r) -> PM_Branch (l, d, pmap_add (k / 2) v r)

  let to_posmap (mkEmpty : 'b)
      (mkBranch : 'b -> 'c option -> 'b -> 'b)
      (get : 'a -> 'c option) =
    let rec to_pm i ls acc =
      match ls with
	[] -> acc
      | l :: ls ->
	to_pm (1 + i) ls
	  (match get l with
	    None ->  acc
	  | Some d -> pmap_add i d acc)
    in
    let rec convert pm =
      match pm with
	PM_Empty -> mkEmpty
      | PM_Branch (l,d,r) ->
	mkBranch (convert l) d (convert r)
    in
    fun ls ->
      let pm = to_pm 1 ls PM_Empty in
      convert pm

end

let rec app_long f acc =
  match Term.kind_of_term f with
    Term.App (f,es) ->
      if Array.length es = 0
      then app_long f acc
      else app_long f (es :: acc)
  | _ ->
    (f, List.rev acc)

module SimpleReifyApp (M : MONAD) (R : sig type result end)
  : REIFY_APP with type 'a m = 'a M.m
              with type result = R.result =
struct
  type result = R.result
  type 'a m = 'a M.m

  let mapM f =
    let rec mapM es =
      match es with
	[] -> M.ret []
      | e :: es -> M.bind (f e) (fun e -> M.bind (mapM es) (fun es -> M.ret (e :: es)))
    in mapM

  let reify_app _ reify_expr reify_app t ts =
    M.bind (reify_expr t) (fun t ->
      M.bind (mapM reify_expr (Array.to_list ts)) (fun ts ->
	reify_app t ts))
end

(** This is the version of reify_app that will handle polymorphism **)
module ReifyAppDep
  (M : MONAD)
  (V : READER with type 'a m = 'a M.m
              with type env = Environ.env)
  (VE : READER with type 'a m = 'a M.m
               with type env = Evd.evar_map)
  (R : REIFY with type 'a m = 'a M.m)
  : REIFY_APP with type 'a m = 'a M.m
              with type result = R.result =
struct
  type result = R.result
  type 'a m = 'a M.m

  let mapM f =
    let rec mapM es =
      match es with
	[] -> M.ret []
      | e :: es -> M.bind (f e) (fun e -> M.bind (mapM es) (fun es -> M.ret (e :: es)))
    in mapM

  let rec noccurn_dprod n cs rc =
    match cs with
      [] -> Term.noccurn n rc
    | c :: cs ->
      if Term.noccurn n c then
	noccurn_dprod (1+n) cs rc
      else
	false

  let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

  let mark_terms (env : Environ.env) =
    let rec mark_terms ty xs =
      match xs with
	[] -> ([], ty)
      | x :: xs ->
	if Term.isProd ty then
	  let (_,t1,t2) = Term.destProd ty in
	  if Term.noccurn 1 t2 then
	    let _ = Format.printf "Non dependent: %a\n" pp_constr t2 in
	    (** non-dependent **)
	    let (rs,rt) = mark_terms t2 xs in
	    ((false, t1, x) :: rs, rt)
	else
	    let _ = Format.printf "Dependent: %a\n" pp_constr t2 in
	    (** dependent **)
	    let (rs,rt) = mark_terms (Term.subst1 x t2) xs in
	    ((true, t1, x) :: rs, rt)
	else
(*	  let (rcs, res) = Reduction.dest_prod env ty in *)
	  assert false
    in mark_terms
(*
	  _ (* TODO: reverse rcs *)
    and continue_terms tys rty xs =
      match tys with
	[] -> mark_terms ty xs
      | ty :: ts_ ->
	match xs with
	  [] -> ([], Term.compose_prod tys rty)
	| x :: xs ->
	  if noccurn_dprod 1 ts_ rty then
	    (false, t1) :: continue_terms ts_ rty xs
	  else
	    (true, t1) :: continue_terms ts_ rty 

      (** look at this type and see if it is dependent **)
*)
  let rindex p =
    let rec rindex i ls =
      match ls with
	[] -> None
      | l :: ls ->
	match rindex (1+i) ls with
	  None -> if p l then Some i else None
	| res -> res
    in rindex 0

  let rec firstn n ls =
    if n > 0 then
      match ls with
	[] -> []
      | l :: ls -> l :: firstn (n - 1) ls
    else
      []
  let rec skipn n ls =
    if n > 0 then
      match ls with
	[] -> []
      | _ :: ls -> skipn (n - 1) ls
    else
      ls

  let partition_until ls =
    match rindex (fun (x,_,_) -> x) ls with
      None -> ([], ls)
    | Some i -> let i = i + 1 in (firstn i ls, skipn i ls)

  let build_lambda f ts =
    match ts with
      [] -> f
    | _ ->
      let mx = List.length ts in
      let app_args = List.mapi (fun n (dep,t,x) ->
	if dep then
	  x
	else
	  Term.mkRel (mx - n - 1)) ts
      in
      let lam_args =
	List.map
	  (fun (_,t,_) -> (Names.Anonymous, t))
	  (List.filter (fun (x,_,_) -> not x) ts)
      in
      (** Here, we do any reduction that we can, just to simplify things **)
      Term.compose_lam (List.rev lam_args)
	               (Reduction.beta_appvect f (Array.of_list app_args))

  let pp_list pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a; " pp x) l

  let reify_app no_progress reify_expr reify_app t ts =
    M.bind V.ask (fun env ->
      M.bind VE.ask (fun evar ->
	let ty = Typing.type_of env evar t in
	let (ts,_) = mark_terms env ty (Array.to_list ts) in
	let (ds,ns) = partition_until ts in
	if ns = [] then
	  Lazy.force no_progress
	else
	  let _ =
	    Printf.fprintf stderr "len ds = %d ; len ns = %d\n"
	      (List.length ds) (List.length ns)
	  in
	  let new_t = build_lambda t ds in
	  let _ = Format.printf "new_t: %a\n" pp_constr new_t in
	  let new_ts = List.map (fun (_,_,x) -> x)
	      (List.filter (fun (x,_,_) -> not x) ds @ ns) in
	  let _ = Format.printf "args: %a\n" (pp_list pp_constr) new_ts in
	  (** TODO: I shouldn't call [reify_expr] on [new_t] because
	   ** I know that there is no way to reify it.
 	   **)
	  M.bind (R.reify new_t) (fun t ->
	    M.bind (mapM reify_expr new_ts) (fun ts ->
	      reify_app t ts))))
end

(*
(fun T x -> x) nat 5
(fun x -> (fun T x -> x) nat x) 5
   ^---- reduce this term before I recurse on it
*)
