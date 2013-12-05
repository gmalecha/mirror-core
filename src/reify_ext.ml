open Reify_gen

module type EXPR_BUILDER =
sig
  type e_result
  type t_result
  val mkVar : int -> e_result
  val mkUVar : int -> e_result
  val mkAbs : t_result -> e_result -> e_result
  val mkApp : e_result -> e_result -> e_result
end

let contrib_name = "reify_ext"

let resolve_symbol = resolve_symbol contrib_name
let to_nat = to_nat contrib_name
let to_positive = to_positive contrib_name

(** Reify Type **)
module ReifyType (M : MONAD)
                 (R : REIFY with type 'a m = 'a M.m
                            with type result = Term.constr)
		 : REIFY with type 'a m = 'a M.m
   		         with type result = Term.constr =
struct
  type result = Term.constr
  type 'a m = 'a M.m

  let types_pkg = ["MirrorCore";"Ext";"Types"]

  let typ_arr = lazy (resolve_symbol types_pkg "tyArr")

  let typ_ref = lazy (resolve_symbol types_pkg "tyType")

  let typ_prop = lazy (resolve_symbol types_pkg "tyProp")

  let typ_arrow (l : Term.constr) (r : Term.constr) : Term.constr =
    Term.mkApp (Lazy.force typ_arr, [| l ; r |])

  let rec reify (t : Term.constr) : Term.constr m =
    match Term.kind_of_term t with
      Term.Prod (n,lt,rt) ->
	if Term.noccurn 0 rt then
	  M.bind (reify lt) (fun lc ->
	    M.bind (reify rt) (fun rc ->
	      M.ret (typ_arrow lc rc)))
	else
	  (** I can't reify **)
	  R.reify t
    | Term.Sort (Term.Prop _) ->
      M.ret (Lazy.force typ_prop)
    | _ ->
      R.reify t
end

let rec app_long f acc =
  match Term.kind_of_term f with
    Term.App (f,es) ->
      if Array.length es = 0
      then app_long f acc
      else app_long f (es :: acc)
  | _ ->
    (f, List.rev acc)

(** Reify an expression **)
module ReifyExpr
  (M : MONAD)
  (E : READER with type env = Environ.env
              with type 'a m = 'a M.m)
  (EXPR : EXPR_BUILDER)
  (RT : REIFY with type 'a m = 'a M.m
              with type result = EXPR.t_result)
  (RE : REIFY with type 'a m = 'a M.m
              with type result = EXPR.e_result)
  (RA : REIFY_APP with type 'a m = 'a M.m
                  with type result = EXPR.e_result)
  : REIFY with type 'a m = 'a M.m
          with type result = EXPR.e_result =
struct
  type result = EXPR.e_result
  type 'a m = 'a M.m

  let rec expr_App f es =
    match es with
      [] -> M.ret f
    | e :: es ->
      expr_App (EXPR.mkApp f e) es

  let reify : Term.constr -> result m =
    let rec reify_expr tm =
      match Term.kind_of_term tm with
	Term.Lambda (name, t, c) ->
	  if not (Term.isSort t) then
	    M.bind (RT.reify t) (fun rt ->
	      M.bind (E.local (Environ.push_rel (name, None, t)) (reify_expr c)) (fun e ->
		M.ret (EXPR.mkAbs rt e)))
	  else
	    (** There is no way to reify type abstractions in Ext **)
	    reify_expr tm
      | Term.Rel n ->
	M.ret (EXPR.mkVar n)
      | Term.Evar e ->
	assert false
      | Term.App (f,es) ->
	RA.reify_app reify_expr expr_App f es
      | Term.Cast (t, _, ty) ->
	reify_expr t
      | _ ->
	RE.reify tm
    in reify_expr
end

(** The reification monad **)
module REIFY_MONAD =
struct
  type 'a m = Environ.env -> (Term.constr list) ref -> (Term.constr list) ref -> 'a

  let ret (x : 'a) : 'a m =
    fun _ _ _ -> x

  let bind (c : 'a m) (f : 'a -> 'b m) : 'b m =
    fun e x y ->
      let b = c e x y in
      f b e x y

  let ask_env = fun e _ _ -> e
  let local_env f c = fun e -> c (f e)

  let get_types = fun _ ts _ -> !ts
  let put_types ts = fun _ rts _ -> rts := ts

  let get_funcs = fun _ _ fs -> !fs
  let put_funcs fs = fun _ _ rfs -> rfs := fs

  let runM c ts fs e =
    let ts = ref ts in
    let fs = ref fs in
    let res = c e ts fs in
    (res, !ts, !fs)

end
