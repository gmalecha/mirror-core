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

module Std = Plugin_utils.Coqstd.Std (struct let contrib_name = "reify_lambda" end)

let resolve_symbol = Std.resolve_symbol
let to_nat = Std.to_nat
let to_positive = Std.to_positive

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
(*      let _ = Format.printf "Reify: %a\n" pp_constr tm in *)
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
	 (** Coq deBruijn indicies start at 1, not 0 **)
	M.ret (EXPR.mkVar (n-1))
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
  (EXT : sig val typ_type : Term.constr Lazy.t
	     val ext_type : Term.constr Lazy.t
         end)
(*: EXPR_BUILDER with type e_result = Term.constr
                 with type t_result = Term.constr *) =
struct
  type e_result = Term.constr
  type t_result = Term.constr
  let expr_pkg = ["MirrorCore";"Lambda";"ExprCore"]

  let expr_var = lazy (resolve_symbol expr_pkg "Var")
  let expr_uvar = lazy (resolve_symbol expr_pkg "UVar")
  let expr_abs = lazy (resolve_symbol expr_pkg "Abs")
  let expr_app = lazy (resolve_symbol expr_pkg "App")
  let expr_inj = lazy (resolve_symbol expr_pkg "Inj")

  let args = lazy [| Lazy.force EXT.typ_type ; Lazy.force EXT.ext_type |]

  let var = lazy (Term.mkApp (Lazy.force expr_var, Lazy.force args))
  let uvar = lazy (Term.mkApp (Lazy.force expr_uvar, Lazy.force args))
  let app = lazy (Term.mkApp (Lazy.force expr_app, Lazy.force args))
  let abs = lazy (Term.mkApp (Lazy.force expr_abs, Lazy.force args))
  let inj = lazy (Term.mkApp (Lazy.force expr_inj, Lazy.force args))

  let mkVar n =
    Term.mkApp (Lazy.force var, [| Std.to_nat n |])

  let mkUVar n =
    Term.mkApp (Lazy.force uvar, [| Std.to_nat n |])

  let mkAbs t e =
    Term.mkApp (Lazy.force abs, [| t ; e |])

  let mkApp f x =
    Term.mkApp (Lazy.force app, [| f ; x |])

  let mkInj x =
    Term.mkApp (Lazy.force inj, [| x |])
end
