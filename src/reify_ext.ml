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

module Std = Reify_gen.Std (struct let contrib_name = "reify_ext" end)

let resolve_symbol = Std.resolve_symbol
let to_nat = Std.to_nat
let to_positive = Std.to_positive

(** Reify Type **)
module ReifyType
  (M : MONAD)
  (R : REIFY with type 'a m = 'a M.m
             with type result = Term.constr)
  (Z : sig val under_type : bool -> 'a M.m -> 'a M.m
	   val lookup_type : int -> int M.m
       end)
  : REIFY with type 'a m = 'a M.m
          with type result = Term.constr =
struct
  type result = Term.constr
  type 'a m = 'a M.m

  let types_pkg = ["MirrorCore";"Ext";"Types"]

  let typ_arr = lazy (resolve_symbol types_pkg "tyArr")

  let typ_ref = lazy (resolve_symbol types_pkg "tyType")

  let typ_prop = lazy (resolve_symbol types_pkg "tyProp")

  let typ_var = lazy (resolve_symbol types_pkg "tyVar")

  let typ_arrow (l : Term.constr) (r : Term.constr) : Term.constr =
    Term.mkApp (Lazy.force typ_arr, [| l ; r |])

  let rec reify (t : Term.constr) : Term.constr m =
    match Term.kind_of_term t with
      Term.Prod (n,lt,rt) ->
	if Term.noccurn 0 rt then
	  M.bind (reify lt) (fun lc ->
	    M.bind (Z.under_type false (reify rt)) (fun rc ->
	      M.ret (typ_arrow lc rc)))
	else
	  (** I can't reify **)
	  R.reify t
    | Term.Rel n ->
      M.bind (Z.lookup_type n) (fun l ->
	M.ret (Term.mkApp (Lazy.force typ_var, [| to_nat l |])))
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


  let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

  let reify : Term.constr -> result m =
    let rec reify_expr tm =
      let _ = Format.printf "Reify: %a\n" pp_constr tm in
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
	RA.reify_app (lazy (RE.reify tm)) reify_expr expr_App f es
      | Term.Cast (t, _, ty) ->
	reify_expr t
      | _ ->
	RE.reify tm
    in reify_expr
end

(** The reification monad **)
module REIFY_MONAD =
struct
  type 'a m = Environ.env ->
    Evd.evar_map ->
    (bool list) ->
    (Term.constr option list) ref ->
    (Term.constr option list) ref -> 'a

  let ret (x : 'a) : 'a m =
    fun _ _ _ _ _ -> x

  let bind (c : 'a m) (f : 'a -> 'b m) : 'b m =
    fun e em look x y ->
      let b = c e em look x y in
      f b e em look x y

  let ask_env = fun e _ _ _ _ -> e
  let local_env f c = fun e -> c (f e)

  let under_type bind_no_bind c =
    fun e em look x y ->
      c e em (bind_no_bind :: look) x y
  let lookup_type n =
    let rec go n ls =
      match ls with
	[] -> assert false
      | l :: ls ->
	if n = 1 then
	  let _ = assert (l = true) in 0
	else if n > 1 then
	  let res = go (n - 1) ls in
	  if l then res + 1 else res
	else
	  assert false
    in
    fun _ _ look _ _ -> go n look

  let ask_evar = fun _ e _ _ _ -> e
  let local_evar _ _ = fun _ _ _ _ _ -> assert false

  let get_types = fun _ _ _ ts _ -> !ts
  let put_types ts = fun _ _ _ rts _ -> rts := ts

  let get_funcs = fun _ _ _ _ fs -> !fs
  let put_funcs fs = fun _ _ _ _ rfs -> rfs := fs

  let runM c ts fs e em =
    let ts = ref ts in
    let fs = ref fs in
    let res = c e em [] ts fs in
    (res, !ts, !fs)

end

(** TODO: Move this to a separate file that deals with reifying Ext.Types
 **)
