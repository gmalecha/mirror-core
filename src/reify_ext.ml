open Reify_gen

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
    (** Perhaps this should use [Term.kind_of_type], but it is
     **	marked "experimental"
     **)
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
module ReifyExpr (M : MONAD) (E : READER with type env = Environ.env
                                         with type 'a m = 'a M.m)
  (RT : REIFY with type 'a m = 'a M.m
              with type result = Term.constr)
  (RE : REIFY with type 'a m = 'a M.m
              with type result = Term.constr)
  (RA : REIFY_APP with type 'a m = 'a M.m
                  with type result = Term.constr)
  : REIFY with type 'a m = 'a M.m
          with type result = RE.result =
struct
  type result = RE.result
  type 'a m = 'a M.m

  let types_pkg = ["MirrorCore";"Ext";"ExprCore"]

  let expr_var = lazy (resolve_symbol types_pkg "Var")

  let expr_uvar = lazy (resolve_symbol types_pkg "UVar")

  let expr_abs = lazy (resolve_symbol types_pkg "Abs")

  let expr_app = lazy (resolve_symbol types_pkg "App")

  let expr_Var n =
    M.ret (Term.mkApp (Lazy.force expr_var, [| to_nat n |]))

  let expr_Abs t e =
    M.ret (Term.mkApp (Lazy.force expr_abs, [| t ; e |]))

  let rec expr_App f es =
    match es with
      [] -> M.ret f
    | e :: es ->
      expr_App (Term.mkApp (Lazy.force expr_app, [| f ; e |])) es

  let reify : Term.constr -> Term.constr m =
    let rec reify_expr t =
      match Term.kind_of_term t with
	Term.Lambda (name, t, c) ->
	  M.bind (RT.reify t) (fun rt ->
	    M.bind (E.local (Environ.push_rel (name, None, t)) (reify_expr c)) (fun e ->
	      expr_Abs rt e))
      | Term.Rel n ->
	expr_Var n
      | Term.Evar e ->
	assert false
      | Term.App (f,es) ->
	RA.reify_app reify_expr expr_App f es
      | Term.Cast (t, _, ty) ->
	reify_expr t
      | _ ->
	RE.reify t
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
end

module MakeReifyExpr =
  ReifyExpr
    (REIFY_MONAD)
    (struct
      type env = Environ.env
      type 'a m = 'a REIFY_MONAD.m
      let local = REIFY_MONAD.local_env
      let ask = REIFY_MONAD.ask_env
     end)
    (ReifyType (REIFY_MONAD)
               (ReifyMap (ReifyEnv (REIFY_MONAD)
			            (struct
				      type state = Term.constr list
				      type 'a m = 'a REIFY_MONAD.m
				      let put = REIFY_MONAD.put_types
				      let get = REIFY_MONAD.get_types
				     end))
		  (struct
		    type result = Term.constr
		    let typ_ref = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "tyType")
		    let map x = REIFY_MONAD.bind x (fun x ->
		      REIFY_MONAD.ret (Term.mkApp (Lazy.force typ_ref, [| to_positive x |])))
		   end)))
    (ReifyMap (ReifyEnv (REIFY_MONAD)
		        (struct
			  type state = Term.constr list
			  type 'a m = 'a REIFY_MONAD.m
			  let put = REIFY_MONAD.put_funcs
			  let get = REIFY_MONAD.get_funcs
			 end))
		  (struct
		    type result = Term.constr
		    let expr_inj = lazy (resolve_symbol ["MirrorCore";"Ext";"ExprCore"] "Inj")
		    let map x = REIFY_MONAD.bind x (fun x ->
		      REIFY_MONAD.ret (Term.mkApp (Lazy.force expr_inj, [| to_positive x |])))
		   end))
    (SimpleReifyApp (REIFY_MONAD) (struct type result = Term.constr end))
