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

module Std = Plugin_utils.Coqstd.Std (struct let contrib_name = "reify_ext" end)

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
  (REX : REIFY with type 'a m = 'a M.m
               with type result = int)
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
	    RE.reify tm
      | Term.Rel n ->
	M.ret (EXPR.mkVar n)
      | Term.Evar _ ->
	M.bind (REX.reify tm) (fun k ->
	  M.ret (EXPR.mkUVar k))
      | Term.App (f,es) ->
	RA.reify_app (lazy (RE.reify tm)) reify_expr expr_App f es
      | Term.Cast (t, _, ty) ->
	reify_expr t
      | _ ->
	RE.reify tm
    in reify_expr
end

module ExprBuilder
  (EXT : sig val ext_type : Term.constr Lazy.t end)
(*: EXPR_BUILDER with type e_result = Term.constr
                 with type t_result = Term.constr *) =
struct
  type e_result = Term.constr
  type t_result = Term.constr
  let expr_pkg = ["MirrorCore";"Ext";"ExprCore"]

  let expr_var = lazy (resolve_symbol expr_pkg "Var")
  let expr_uvar = lazy (resolve_symbol expr_pkg "UVar")
  let expr_abs = lazy (resolve_symbol expr_pkg "Abs")
  let expr_app = lazy (resolve_symbol expr_pkg "App")
  let expr_inj = lazy (resolve_symbol expr_pkg "Inj")

  let mkVar n =
    Term.mkApp (Lazy.force expr_var, [| Lazy.force EXT.ext_type ; Std.to_nat n |])

  let mkUVar n =
    Term.mkApp (Lazy.force expr_uvar, [| Lazy.force EXT.ext_type ; Std.to_nat n |])

  let mkAbs t e =
    Term.mkApp (Lazy.force expr_abs, [| Lazy.force EXT.ext_type ; t ; e |])

  let mkApp f x =
    Term.mkApp (Lazy.force expr_app, [| Lazy.force EXT.ext_type ; f ; x |])

  let mkInj x =
    Term.mkApp (Lazy.force expr_inj, [| Lazy.force EXT.ext_type ; x |])
end

(** **)
module ReifyExtTypes
  (PARAM : sig type 'a m
	       val ret : 'a -> 'a m
	       val bind : 'a m -> ('a -> 'b m) -> 'b m
	       val put_types : Term.constr option list -> unit m
	       val get_types : Term.constr option list m
	       val under_type : bool -> 'a m -> 'a m
	       val lookup_type : int -> int m
           end)
  : REIFY with type 'a m = 'a PARAM.m
          with type result = Term.constr =
  ReifyType
    (struct
      type 'a m = 'a PARAM.m
      let bind = PARAM.bind
      let ret = PARAM.ret
     end)
    (ReifyMap (ReifyEnvOption
		 (struct
		   type 'a m = 'a PARAM.m
		   let bind = PARAM.bind
		   let ret = PARAM.ret
		  end)
		 (struct
		   type state = Term.constr option list
		   type 'a m = 'a PARAM.m
		   let put = PARAM.put_types
		   let get = PARAM.get_types
		  end))
       (struct
	 type result = Term.constr
	 let typ_ref = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "tyType")
	 let map x = PARAM.bind x (fun x ->
	   PARAM.ret (Term.mkApp (Lazy.force typ_ref, [| to_positive (1 + x) |])))
	end))
    (struct
      type 'a m = 'a PARAM.m
      let under_type = PARAM.under_type
      let lookup_type = PARAM.lookup_type
     end)
