(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Reify_gen
open Reify_lambda
open Plugin_utils.Term_match

let contrib_name = "reify_McExamples.Monad2.MonadReify"

module Std = Plugin_utils.Coqstd.Std (struct let contrib_name = contrib_name end)

let resolve_symbol = Std.resolve_symbol
let to_positive = Std.to_positive

(** Reification of MirrorCore.Ext.SymEnv **)
let sym_env_pkg = ["McExamples";"Monad2";"MonadExpr"]
let types_pkg = ["McExamples";"Monad2";"MonadTypes"]
let tm_typ = lazy (resolve_symbol ["McExamples";"Monad2";"MonadTypes"] "typ")
let tm_RType = lazy (resolve_symbol ["McExamples";"Monad2";"MonadTypes"] "RType_typ")
let tm_typD = lazy (resolve_symbol ["MirrorCore";"TypesI"] "typD")

let func = lazy (resolve_symbol sym_env_pkg "mext")

module ExprBuilder = Reify_lambda.ExprBuilder
  (struct
    let ext_type = func
    let typ_type = tm_typ
   end)

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

let rec apps a b =
  match b with
    [] -> a
  | b :: bs -> apps (App (a, b)) bs

module REIFY_MONAD =
struct
  type 'a m = Environ.env ->
    Evd.evar_map ->
    (bool list) ->
    (Term.constr list) ref ->
    (Term.constr option list) ref ->
    (Term.constr option list) ref -> 'a

  let ret (x : 'a) : 'a m =
    fun _ _ _ _ _ _ -> x

  let bind (c : 'a m) (f : 'a -> 'b m) : 'b m =
    fun e em look z x y ->
      let b = c e em look z x y in
      f b e em look z x y

  let ask_env = fun e _ _ _ _ _ -> e
  let local_env f c = fun e -> c (f e)

  let under_type bind_no_bind c =
    fun e em look ->
      c e em (bind_no_bind :: look)
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
    fun _ _ look _ _ _ -> go n look

  let ask_evar = fun _ e _ _ _ _ -> e
  let local_evar _ _ = fun _ _ _ _ _ _ -> assert false

  let get_types = fun _ _ _ _ ts _ -> !ts
  let put_types ts = fun _ _ _ _ rts _ -> rts := ts

  let get_funcs = fun _ _ _ _ _ fs -> !fs
  let put_funcs fs = fun _ _ _ _ _ rfs -> rfs := fs

  let get_evars = fun _ _ _ revs _ _ -> !revs
  let put_evars evs = fun _ _ _ revs _ _ -> revs := evs

  let runM c ts fs evars e em =
    let ts = ref ts in
    let fs = ref fs in
    let evars = ref evars in
    let res = c e em [] evars ts fs in
    (res, !ts, !fs, !evars)
end

let sum = lazy (resolve_symbol ["Coq";"Init";"Datatypes"] "sum")
let sum_inl = lazy (resolve_symbol ["Coq";"Init";"Datatypes"] "inl")
let sum_inr = lazy (resolve_symbol ["Coq";"Init";"Datatypes"] "inr")

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

  let typ_m = lazy (resolve_symbol types_pkg "tyM")

  let typ_arr = lazy (resolve_symbol types_pkg "tyArr")

  let typ_ref = lazy (resolve_symbol types_pkg "tyType")

  let typ_prop = lazy (resolve_symbol types_pkg "tyProp")

  let typ_var = lazy (resolve_symbol types_pkg "tyVar")

  let typ_arrow (l : Term.constr) (r : Term.constr) : Term.constr =
    Term.mkApp (Lazy.force typ_arr, [| l ; r |])

  let rec reify (t : Term.constr) : Term.constr m =
    let _ = Format.printf "Reify Type: %a\n" pp_constr t in
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
    | Term.App (_ , [| t' |]) ->
      M.bind (R.reify t') (fun t' ->
	M.ret (Term.mkApp (Lazy.force typ_m, [| t' |])))
    | _ ->
      R.reify t
end

(** **)
module ReifyMonadTypesF
  (PARAM : sig type 'a m
	       val ret : 'a -> 'a m
	       val bind : 'a m -> ('a -> 'b m) -> 'b m
	       val put_types : Term.constr option list -> unit m
	       val get_types : Term.constr option list m
	       val under_type : bool -> 'a m -> 'a m
	       val lookup_type : int -> int m
           end)
  (CHK : Checker with type 'a m = 'a PARAM.m)
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
		  end)
		 (CHK))
       (struct
	 type result = Term.constr
	 let typ_ref = lazy (resolve_symbol ["McExamples";"Monad2";"MonadTypes"] "tyType")
	 let map x = PARAM.bind x (fun x ->
	   PARAM.ret (Term.mkApp (Lazy.force typ_ref, [| to_positive (1 + x) |])))
	end))
    (struct
      type 'a m = 'a PARAM.m
      let under_type = PARAM.under_type
      let lookup_type = PARAM.lookup_type
     end)

(** **)
module ReifyMonadTypes =
  ReifyMonadTypesF (REIFY_MONAD) (CheckEq (REIFY_MONAD))

module REIFY_MONAD_READ_ENV =
struct
  type env = Environ.env
  type 'a m = 'a REIFY_MONAD.m
  let local = REIFY_MONAD.local_env
  let ask = REIFY_MONAD.ask_env
end

module REIFY_MONAD_READ_EVAR =
struct
  type env = Evd.evar_map
  type 'a m = 'a REIFY_MONAD.m
  let local = REIFY_MONAD.local_evar
  let ask = REIFY_MONAD.ask_evar
end

module REIFY_ENV_FUNC =
  ReifyMap (ReifyEnvOption (REIFY_MONAD)
	      (struct
		type state = Term.constr option list
		type 'a m = 'a REIFY_MONAD.m
		let put = REIFY_MONAD.put_funcs
		let get = REIFY_MONAD.get_funcs
	       end)
	      (CheckEq (REIFY_MONAD)))
    (struct
      type result = Term.constr
      let expr_fref = lazy (resolve_symbol ["MirrorCore";"Lambda";"ExprCore"] "Inj")

      let monad_sym_pkg = ["McExamples";"Monad2";"MonadSym"]
      let env_sym_pkg = ["MirrorCore";"syms";"SymEnv"]

      let sym_mfunc = lazy (resolve_symbol monad_sym_pkg "mfunc")
      let sym_func = lazy (resolve_symbol env_sym_pkg "func")

      let ary_app = lazy [| Lazy.force sym_func ; Lazy.force sym_mfunc |]
      let expr_inr = lazy (Term.mkApp (Lazy.force sum_inr, Lazy.force ary_app))
      let expr_inl = lazy (Term.mkApp (Lazy.force sum_inl, Lazy.force ary_app))

      let mkRef (p : Term.constr) =
	Term.mkApp (Lazy.force expr_inl, [| p |])

(*
      let nil_types = lazy (Std.to_list (resolve_symbol ["MirrorCore";"Ext";"Types"] "typ") []) *)
      let map x = REIFY_MONAD.bind x (fun x ->
	let sym = mkRef (to_positive (1 + x)) in
	REIFY_MONAD.ret (ExprBuilder.mkInj sym))
     end)

module REIFY_ENV_EVAR =
  ReifyEnv (REIFY_MONAD)
    (struct
      type state = Term.constr list
      type 'a m = 'a REIFY_MONAD.m
      let put = REIFY_MONAD.put_evars
      let get = REIFY_MONAD.get_evars
     end)
    (CheckEq (REIFY_MONAD))

module BaseReifyApp =
  ReifyAppDep (REIFY_MONAD) (REIFY_MONAD_READ_ENV) (REIFY_MONAD_READ_EVAR)
    (REIFY_ENV_FUNC)

module ClassReifyApp
  (S : STATE with type 'a m = 'a REIFY_MONAD.m
             with type state = Term.constr option list)
  (RT : REIFY with type 'a m = 'a REIFY_MONAD.m
              with type result = Term.constr)
  (E : READER with type 'a m = 'a REIFY_MONAD.m
              with type env = Environ.env)
  : REIFY_APP with type 'a m = 'a REIFY_MONAD.m
              with type result = Term.constr =
struct
  module M = REIFY_MONAD

  type result = Term.constr
  type 'a m = 'a M.m

  module CHK = CheckEq (M)
  module RE = ReifyEnvOption (M) (S) (CHK)

  let tm_bind = lazy (resolve_symbol ["ExtLib";"Structures";"Monad"] "bind")
  let tm_ret = lazy (resolve_symbol ["ExtLib";"Structures";"Monad"] "ret")

  let monad_sym_pkg = ["McExamples";"Monad2";"MonadSym"]
  let env_sym_pkg = ["MirrorCore";"syms";"SymEnv"]

  let expr_bind = lazy (resolve_symbol monad_sym_pkg "mBind")
  let expr_ret = lazy (resolve_symbol monad_sym_pkg "mReturn")
  let sym_mfunc = lazy (resolve_symbol monad_sym_pkg "mfunc")
  let sym_func = lazy (resolve_symbol env_sym_pkg "func")

  let ary_app = lazy [| Lazy.force sym_func ; Lazy.force sym_mfunc |]
  let expr_inr = lazy (Term.mkApp (Lazy.force sum_inr, Lazy.force ary_app))
  let expr_inl = lazy (Term.mkApp (Lazy.force sum_inl, Lazy.force ary_app))

  let wrapM (a : Term.constr) =
    Term.mkApp (Lazy.force expr_inr, [| a |])

  let mkBind (a : Term.constr) (b : Term.constr) =
    wrapM (Term.mkApp (Lazy.force expr_bind, [| a ; b |]))

  let mkRet (a : Term.constr) =
    wrapM (Term.mkApp (Lazy.force expr_ret, [| a |]))

  let mkRef (p : Term.constr) =
    Term.mkApp (Lazy.force expr_inl, [| p |])

  let mapM f =
    let rec mapM es =
      match es with
	[] -> M.ret []
      | e :: es -> M.bind (f e) (fun e -> M.bind (mapM es) (fun es -> M.ret (e :: es)))
    in mapM

  let reify_app (lzy : result m Lazy.t)
      (reify_expr : Term.constr -> result m)
      (mk_app : result -> result list -> result m)
      (t : Term.constr) (ts : Term.constr array) =
(*    let _ = Format.printf "reify_app: %a\n" pp_constr t in *)
    M.bind (E.ask) (fun ctx ->
      matches ctx
	[ (Glob tm_bind,
	   fun _ ->
	     match Array.to_list ts with
	       _ :: _ :: alpha :: beta :: rest ->
		 M.bind (RT.reify alpha) (fun alpha ->
		   M.bind (RT.reify beta) (fun beta ->
		     M.bind (mapM reify_expr rest) (fun es ->
		       let b = ExprBuilder.mkInj (mkBind alpha beta) in
		       mk_app b es)))
	     | _ -> assert false)
	; (Glob tm_ret,
	   fun _ ->
	     match Array.to_list ts with
	       _ :: _ :: alpha :: rest ->
(*		 let _ = Format.printf "return (alpha=%a)\n" pp_constr alpha in *)
		 M.bind (RT.reify alpha) (fun alpha ->
		   M.bind (mapM reify_expr rest) (fun es ->
		     let r = ExprBuilder.mkInj (mkRet alpha) in
		     mk_app r es))
	     | _ -> assert false)
	; (Ignore,
	   fun _ -> BaseReifyApp.reify_app lzy reify_expr mk_app t ts)
	] t)
(*
    M.bind (reify_expr t) (fun t ->
      M.bind (mapM reify_expr (Array.to_list ts)) (fun ts ->
	reify_app t ts))
*)
end

module ReifyMonad =
  ReifyExpr
    (REIFY_MONAD)
    (REIFY_MONAD_READ_ENV)
    (ExprBuilder)
    (ReifyMonadTypes)
    (REIFY_ENV_FUNC)
    (REIFY_ENV_EVAR)
    (ClassReifyApp
       (struct
	 type state = Term.constr option list
	 type 'a m = 'a REIFY_MONAD.m
	 let put = REIFY_MONAD.put_funcs
	 let get = REIFY_MONAD.get_funcs
	end)
       (ReifyMonadTypes)
       (REIFY_MONAD_READ_ENV))
;;

(** extract the values from an environment **)
let types_empty = lazy (resolve_symbol ["McExamples";"Monad2";"MonadTypes"] "TEemp")
let types_branch = lazy (resolve_symbol ["McExamples";"Monad2";"MonadTypes"] "TEbranch")

let mapM (f : 'a -> 'b REIFY_MONAD.m) =
  let rec mapM (ls : 'a list) : 'b list REIFY_MONAD.m =
    match ls with
      [] -> REIFY_MONAD.ret []
    | l :: ls -> REIFY_MONAD.bind (f l) (fun l ->
      REIFY_MONAD.bind (mapM ls) (fun ls ->
	REIFY_MONAD.ret (l :: ls)))
  in mapM

let rtype = lazy (Term.mkSort (Term.Type (Termops.new_univ ())))

let extract_types (ls : Term.constr option list) =
  let rtype = Lazy.force rtype in
  Std.to_posmap (Lazy.force types_empty)
    (fun a b c ->
      Term.mkApp (Lazy.force types_branch,
		  [| a ; Std.to_option rtype b ; c |]))
    (fun x -> x) ls
;;

let mkFunction = lazy (resolve_symbol ["MirrorCore";"syms";"SymEnv"] "F")

(** reify ML-style function types **)
let reify_function_scheme reify_type =
  let rec reify_function_scheme n ft =
    match Term.kind_of_term ft with
      Term.Prod (_,t1,t2) ->
	if Term.noccurn 1 t2 then
	  (** It is a lambda **)
	  REIFY_MONAD.bind
	    (REIFY_MONAD.under_type true (reify_type ft)) (fun rft ->
	    REIFY_MONAD.ret (n, rft))
	else
	  reify_function_scheme (1+n) t2
    | _ ->
      REIFY_MONAD.bind (reify_type ft) (fun rft ->
	REIFY_MONAD.ret (n, rft))
  in reify_function_scheme 0

let build_functions evar env : (Term.constr -> Term.constr) option list REIFY_MONAD.m =
  let do_func f =
    match f with
      None -> REIFY_MONAD.ret None
    | Some f ->
      let _ = Format.printf "1) Build function: %a\n" pp_constr f in
      let tf = Typing.type_of env evar f in
      REIFY_MONAD.bind (reify_function_scheme ReifyMonadTypes.reify tf) (fun (n, rft) ->
	REIFY_MONAD.ret (Some (fun ctor ->
	  Term.mkApp (ctor, [| rft
			     ; Term.mkLambda (Names.Anonymous,
					      Std.list_of (Lazy.force rtype), f)
			     |]))))
  (*Lazy.force mkFunction,
    [| Lazy.force tm_typ ; _ ; rft ; f |])))) *)
  in
  REIFY_MONAD.bind REIFY_MONAD.get_funcs (mapM do_func)

let build_uvars evar env : (Term.constr * Term.constr) list REIFY_MONAD.m =
  REIFY_MONAD.bind REIFY_MONAD.get_evars
    (mapM (fun e ->
(*      let _ = Format.printf "2) Reify: %a\n" pp_constr e in *)
      let te = Typing.type_of env evar e in
      REIFY_MONAD.bind (ReifyMonadTypes.reify te) (fun rt ->
	REIFY_MONAD.ret (rt, e))))

let ctor_branch =
  lazy (resolve_symbol ["Coq";"FSets";"FMapPositive";"PositiveMap"] "Node")

let ctor_leaf =
  lazy (resolve_symbol ["Coq";"FSets";"FMapPositive";"PositiveMap"] "Leaf")

let e_function =
  lazy (resolve_symbol ["MirrorCore";"syms";"SymEnv"] "function")

let mapM f =
  let rec mapM es =
    match es with
      [] -> REIFY_MONAD.ret []
    | e :: es ->
      REIFY_MONAD.bind (f e) (fun e ->
	REIFY_MONAD.bind (mapM es) (fun es ->
	  REIFY_MONAD.ret (e :: es)))
  in mapM


(** the simplest version of the tactic will just construct the version of the
 ** environment and return that with the expression.
 ** NOTE: In the future, we'll need to write more plugins to do more specialized
 **       instantiation
 **)
TACTIC EXTEND reify_Monad2_MonadExpr_reify_expr
  | ["reify_expr" constr(m) tactic(k) "[" ne_constr_list(es) "]" ] ->
    [ fun gl ->
        let env = Tacmach.pf_env gl in
	let evar_map = Tacmach.project gl in
	let i_types = [] in
	let i_funcs = [] in
	let i_uvars = [] in
        let (res, r_types, r_funcs, r_uvars) =
	  let cmd = REIFY_MONAD.bind (mapM ReifyMonad.reify es) (fun re ->
	    let _ = Format.printf "done with expressions\n" in
	    REIFY_MONAD.bind (build_functions evar_map env) (fun fs ->
	      let _ = Format.printf "done with functions\n" in
	      REIFY_MONAD.bind (build_uvars evar_map env) (fun us ->
		let _ = Format.printf "done with uvars\n" in
		REIFY_MONAD.ret (re, fs, us))))
	  in
	  let ((res, r_funcs, r_uvars), r_types, _, _) =
	    REIFY_MONAD.runM cmd i_types i_funcs i_uvars env evar_map in
	  (res, r_types, r_funcs, r_uvars)
	in
	let _ = Format.printf "Done Reification\n" in
	let r_types = extract_types r_types in
	let _ = Format.printf "Done types\n" in
	let _ = Format.printf "types = %a\n" pp_constr r_types in
	Plugin_utils.Use_ltac.pose "types" r_types (fun r_types ->
	  let the_rtype = Term.mkApp (Lazy.force tm_RType, [| m ; r_types |]) in
	  let ary_args = [| Lazy.force tm_typ
			  ; the_rtype
			  |] in
	  let typ = Term.mkApp (Lazy.force e_function, ary_args) in
	  let leaf = Term.mkApp (Lazy.force ctor_leaf, [| typ |]) in
	  let func_ctor =
	    Term.mkApp (Lazy.force mkFunction, ary_args)
	  in
	  let r_funcs = Std.to_posmap leaf
	    (fun a b c ->
	      Term.mkApp (Lazy.force ctor_branch,
			  [| typ ; a ; Std.to_option typ b ; c |]))
	    (fun f -> match f with
	      None -> None
	    | Some f -> Some (f func_ctor)) r_funcs in
	  let _ = Format.printf "Done funcs\n" in
	  let _ = Format.printf "funcs = %a\n" pp_constr r_funcs in
	  Plugin_utils.Use_ltac.pose "funcs" r_funcs (fun r_funcs ->
	    let typD = Term.mkApp (Lazy.force tm_typD,
				   [| Lazy.force tm_typ
				    ; the_rtype
				    ; Std.to_list (Lazy.force rtype) [] |]) in
	    let params = [| Lazy.force tm_typ ; typD |] in
	    let env_typ = Term.mkApp (Lazy.force Std.sigT_ctor, params) in
	    let env_elem =
	      Term.mkApp (Lazy.force Std.existT_ctor, params)
	    in
	    let r_uvars =
	      List.map (fun (t,v) -> Term.mkApp (env_elem, [| t ; v |])) [] (* r_uvars *)
	    in
(*	    let _ = Format.printf "-- %a\n" pp_constr env_typ in *)
	    Plugin_utils.Use_ltac.pose "uvars" (Std.to_list env_typ r_uvars)
	      (fun r_uvars ->
(*		let _ = Format.printf "---\n" in
		let _ = Format.printf "2) uvars = %a\n" pp_constr r_uvars in
		let _ = Format.printf "2) res = %a\n" pp_constr res in *)
		let ltac_args =
		  List.map
		    Plugin_utils.Use_ltac.to_ltac_val
		    (r_types :: r_funcs :: r_uvars :: res)
		in
		Plugin_utils.Use_ltac.ltac_apply k ltac_args))) gl
    ]
END;;
