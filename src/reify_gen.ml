let resolve_symbol (contrib_name : string) (path : string list) (tm : string) : Term.constr =
  let re = Coqlib.find_reference contrib_name path tm in
  Libnames.constr_of_global re

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

  val reify_app : (Term.constr -> result m) ->
                  (result -> result list -> result m) ->
                  Term.constr -> Term.constr array -> result m
end

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

(** The simplest instantiation is just an environment of
 ** expressions. This can be used for both expressions and types
 **)
module ReifyEnv (M : MONAD)
                (S : STATE with type state = Term.constr list
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
      | x :: xs ->
	if Term.eq_constr x k
	then Some i
	else env_get (i+1) xs
    in env_get 0

  let env_app a b =
    (List.append a [b], List.length a)

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

let to_positive contrib =
  let pos_pkg = ["Coq";"Numbers";"BinNums"] in
  let xH = lazy (resolve_symbol contrib pos_pkg "xH") in
  let xO = lazy (resolve_symbol contrib pos_pkg "xO") in
  let xI = lazy (resolve_symbol contrib pos_pkg "xI") in
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

let to_N contrib =
  let n_pkg = ["Coq";"Numbers";"BinNums"] in
  let o = lazy (resolve_symbol contrib n_pkg "N0") in
  let pos = lazy (resolve_symbol contrib n_pkg "Npos") in
  let to_pos = to_positive contrib in
  fun n ->
    if n = 0
    then Lazy.force o
    else
      if n < 0
      then raise (Invalid_argument ("to_N: " ^ string_of_int n))
      else Term.mkApp (Lazy.force pos, [| to_pos n |])

let to_nat contrib =
  let pos_pkg = ["Coq";"Init";"Datatypes"] in
  let s = lazy (resolve_symbol contrib pos_pkg "S") in
  let o = lazy (resolve_symbol contrib pos_pkg "O") in
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

let to_list contrib =
  let list_pkg = ["Coq";"Init";"Datatypes"] in
  let c_nil = lazy (resolve_symbol contrib list_pkg "nil") in
  let c_cons = lazy (resolve_symbol contrib list_pkg "cons") in
  fun typ ->
    let the_nil = Term.mkApp (Lazy.force c_nil, [| typ |]) in
    let rec to_list (ls : Term.constr list) : Term.constr =
      match ls with
	[] -> the_nil
      | l :: ls ->
	Term.mkApp (Lazy.force c_cons, [| typ ; l ; to_list ls |])
    in to_list

(** TODO: It is probably easier to do a list and then build
 ** and then use gallina to build the actual pmap object
 **)
(*
type 'a pmap =
| PM_Empty
| PM_Branch of 'a pmap * 'a option * 'a pmap

let rec pmap_add k v m =
  if k = 1 then
    match m with
      PM_Empty -> PM_Branch (PM_Empty, Some v, PM_Empty)
    | PM_Branch(l,_,r) -> PM_Branch (l, v, r)
  else
    if k mod 2 = 0 then
      match m with
	PM_Empty -> PM_Branch (pmap_add (k / 2) v PM_Empty, None, PM_Empty)
      | PM_Branch (l,d,r) -> PM_Branch (pmap_add (k / 2) v l, d, r)
    else
      match m with
	PM_Empty -> PM_Branch (PM_Empty, None, pmap_add (k / 2) v PM_Empty)
      | PM_Branch (l,d,r) -> PM_Branch (l, d, pmap_add (k / 2) v r)

let to_posmap contrib =
  let pm_pkg = ["ExtLib";"Data";"Map";"FMapPositive"] in
  let ctor_empty =
*)


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

  let reify_app reify_expr reify_app t ts =
    M.bind (reify_expr t) (fun t ->
      M.bind (mapM reify_expr (Array.to_list ts)) (fun ts ->
	reify_app t ts))
end
