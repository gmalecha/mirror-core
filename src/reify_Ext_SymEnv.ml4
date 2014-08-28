(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Reify_gen
open Reify_ext
open Plugin_utils.Term_match

let contrib_name = "reify_MirrorCore.Ext.SymEnv"

module Std = Plugin_utils.Coqstd.Std (struct let contrib_name = contrib_name end)

let resolve_symbol = Std.resolve_symbol
let to_positive = Std.Positive.to_positive

(** Reification of MirrorCore.Ext.SymEnv **)
let sym_env_pkg = ["MirrorCore";"Ext";"SymEnv"]

let func = lazy (resolve_symbol sym_env_pkg "func")

module ExprBuilder = Reify_ext.ExprBuilder (struct let ext_type = func end)

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

(** This is really fixed **)
module ReifySym
  (M : MONAD)
  (S : STATE with type 'a m = 'a M.m
             with type state = Term.constr option list)
  (RT : REIFY with type 'a m = 'a M.m
              with type result = Term.constr)
  (E : READER with type 'a m = 'a M.m
              with type env = Environ.env)
  : REIFY with type 'a m = 'a M.m
          with type result = Term.constr =
struct
  type 'a m = 'a M.m
  type result = Term.constr

  module CHK = CheckEq (M)
  module RE = ReifyEnvOption (M) (S) (CHK)

  let tm_eq = lazy (resolve_symbol ["Coq";"Init";"Logic"] "eq")
  let tm_not = lazy (resolve_symbol ["Coq";"Init";"Logic"] "not")

  let expr_eq = lazy (resolve_symbol sym_env_pkg "Equal")
  let expr_not = lazy (resolve_symbol sym_env_pkg "Not")
  let expr_fref = lazy (resolve_symbol sym_env_pkg "FRef")

  let reify (tm : Term.constr) : result m =
    M.bind (E.ask) (fun ctx ->
      matches ctx
	[ (App (Glob tm_eq, As (Ignore,"t")),
	   fun _ s ->
	     let t = Hashtbl.find s "t" in
	     M.bind (RT.reify t) (fun t ->
	       M.ret (Term.mkApp (Lazy.force expr_eq, [| t |]))))
        ; (Glob tm_not,
	   fun _ _ ->
	     M.ret (Lazy.force expr_not))
        ; (Ignore,
	   fun _ _ ->
	     M.bind (RE.reify tm) (fun t ->
	       let idx = to_positive (1 + t) in
	       M.ret (Term.mkApp (Lazy.force expr_fref, [| idx |]))))
	]
	tm)
end

(** **)
module ReifyExtTypes =
  Reify_ext.ReifyExtTypes (REIFY_MONAD) (CheckEq (REIFY_MONAD))

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
      let expr_fref = lazy (resolve_symbol ["MirrorCore";"Ext";"SymEnv"] "FRef")
      let nil_types = lazy (Std.List.to_list (resolve_symbol ["MirrorCore";"Ext";"Types"] "typ") [])
      let map x = REIFY_MONAD.bind x (fun x ->
	let sym =
	  Term.mkApp (Lazy.force expr_fref,
		      [| to_positive (1 + x)
		      ; Lazy.force nil_types |]) in
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

module ReifyExtSymEnv =
  ReifyExpr
    (REIFY_MONAD)
    (REIFY_MONAD_READ_ENV)
    (ExprBuilder)
    (ReifyExtTypes)
    (REIFY_ENV_FUNC)
    (REIFY_ENV_EVAR)
(*    (SimpleReifyApp (REIFY_MONAD) (struct type result = Term.constr end)) *)
    (ReifyAppDep (REIFY_MONAD) (REIFY_MONAD_READ_ENV) (REIFY_MONAD_READ_EVAR)
       (REIFY_ENV_FUNC))
;;

(** extract the values from an environment **)
let types_empty = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "TEemp")
let types_branch = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "TEbranch")

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
  Std.PosMap.to_posmap (Lazy.force types_empty)
    (fun a b c ->
      Term.mkApp (Lazy.force types_branch,
		  [| a ; Std.Option.to_option rtype b ; c |]))
    (fun x -> x) ls
;;

let mkFunction = lazy (resolve_symbol ["MirrorCore";"Ext";"SymEnv"] "F")

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
      let tf = Typing.type_of env evar f in
      REIFY_MONAD.bind (reify_function_scheme ReifyExtTypes.reify tf) (fun (n, rft) ->
	REIFY_MONAD.ret (Some (fun ts ->
	  Term.mkApp (Lazy.force mkFunction,
		      [| ts ; Std.Nat.to_nat n ; rft ; f |]))))
  in
  REIFY_MONAD.bind REIFY_MONAD.get_funcs (mapM do_func)

let tm_typ = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "typ")
let tm_typD = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "typD")

let build_uvars evar env : (Term.constr * Term.constr) list REIFY_MONAD.m =
  REIFY_MONAD.bind REIFY_MONAD.get_evars
    (mapM (fun e ->
      let te = Typing.type_of env evar e in
      REIFY_MONAD.bind (ReifyExtTypes.reify te) (fun rt ->
	REIFY_MONAD.ret (rt, e))))

let ctor_branch =
  lazy (resolve_symbol ["Coq";"FSets";"FMapPositive";"PositiveMap"] "Node")

let ctor_leaf =
  lazy (resolve_symbol ["Coq";"FSets";"FMapPositive";"PositiveMap"] "Leaf")

let e_function =
  lazy (resolve_symbol ["MirrorCore";"Ext";"SymEnv"] "function")

(** the simplest version of the tactic will just construct the version of the
 ** environment and return that with the expression.
 ** NOTE: In the future, we'll need to write more plugins to do more specialized
 **       instantiation
 **)
TACTIC EXTEND reify_Ext_SymEnv_reify_expr
  | ["reify_expr" constr(e) tactic(k) ] ->
    [ fun gl ->
        let env = Tacmach.pf_env gl in
	let evar_map = Tacmach.project gl in
	let i_types = [] in
	let i_funcs = [] in
	let i_uvars = [] in
        let (res, r_types, r_funcs, r_uvars) =
	  let cmd = REIFY_MONAD.bind (ReifyExtSymEnv.reify e) (fun re ->
	    REIFY_MONAD.bind (build_functions evar_map env) (fun fs ->
	      REIFY_MONAD.bind (build_uvars evar_map env) (fun us ->
		REIFY_MONAD.ret (re, fs, us))))
	  in
	  let ((res, r_funcs, r_uvars), r_types, _, _) =
	    REIFY_MONAD.runM cmd i_types i_funcs i_uvars env evar_map in
	  (res, r_types, r_funcs, r_uvars)
	in
	let r_types = extract_types r_types in
	Plugin_utils.Use_ltac.pose "types" r_types (fun r_types ->
	  let typ = Term.mkApp (Lazy.force e_function, [| r_types |]) in
	  let leaf = Term.mkApp (Lazy.force ctor_leaf, [| typ |]) in
	  let r_funcs = Std.PosMap.to_posmap leaf
	    (fun a b c ->
	      Term.mkApp (Lazy.force ctor_branch,
			  [| typ ; a ; Std.Option.to_option typ b ; c |]))
	    (fun f -> match f with
	      None -> None
	    | Some f -> Some (f r_types)) r_funcs in
	  Plugin_utils.Use_ltac.pose "funcs" r_funcs (fun r_funcs ->
	    let typD = Term.mkApp (Lazy.force tm_typD,
				   [| r_types
				    ; Std.List.to_list (Lazy.force rtype) [] |]) in
	    let params = [| Lazy.force tm_typ ; typD |] in
	    let env_typ = Term.mkApp (Lazy.force Std.SigT.sigT_type, params) in
	    let env_elem =
	      Term.mkApp (Lazy.force Std.SigT.c_existT, params)
	    in
	    let r_uvars =
	      List.map (fun (t,v) -> Term.mkApp (env_elem, [| t ; v |])) r_uvars
	    in
	    Plugin_utils.Use_ltac.pose "uvars" (Std.List.to_list env_typ r_uvars)
	      (fun r_uvars ->
		let ltac_args =
		  List.map
		    Plugin_utils.Use_ltac.to_ltac_val
		    [r_types; r_funcs; r_uvars; res]
		in
		Plugin_utils.Use_ltac.ltac_apply k ltac_args))) gl
    ]
END;;
