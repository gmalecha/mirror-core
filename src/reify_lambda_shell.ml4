(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Reify_gen
open Reify_ext
open Plugin_utils

let contrib_name = "MirrorCore.Reify.Lambda"

module Std = Plugin_utils.Coqstd.Std
  (struct
    let contrib_name = contrib_name
   end)

module Reification =
struct
  type rule =
    Term_match.pattern *
      ((string, Term.constr) Hashtbl.t -> Term.constr)

  let extensions : (Term.constr, rule) Hashtbl.t = Hashtbl.create 5

  let pattern_mod = ["MirrorCore";"Reify";"Patterns"]

  let ptrn_exact  = Std.resolve_symbol pattern_mod "RExact"
  let ptrn_ignore = Std.resolve_symbol pattern_mod "RIgnore"
  let ptrn_get    = Std.resolve_symbol pattern_mod "RGet"
  let ptrn_app    = Std.resolve_symbol pattern_mod "RApp"
  let ptrn_pi     = Std.resolve_symbol pattern_mod "RPi"
  let ptrn_impl   = Std.resolve_symbol pattern_mod "RImpl"

  let func_function = Std.resolve_symbol pattern_mod "function"
(*  let act_get_store = Std.resolve_symbol pattern_mod "get_store" *)
  let act_call      = Std.resolve_symbol pattern_mod "reify"

  type rpattern =
  | RIgnore
  | RGet   of int
  | RApp   of rpattern * rpattern
  | RPi    of rpattern * rpattern
  | RImpl  of rpattern * rpattern
  | RExact of Term.constr

  let as_ignore s = Term_match.As (Term_match.Ignore, s)

  let into_rpattern gl =
    let rec into_rpattern (ptrn : Term.constr) : rpattern =
      Term_match.matches gl
	[ (Term_match.Glob (lazy ptrn_ignore),
	   fun _ -> RIgnore)
	; (Term_match.App (Term_match.Glob (lazy ptrn_get),
                           Term_match.As (Term_match.Ignore, "0")),
	   fun s ->
	     let s = Hashtbl.find s "0" in
	     RGet (Std.of_nat s))
	; (Term_match.App (Term_match.App (Term_match.Glob (lazy ptrn_exact),
					   Term_match.Ignore),
			   as_ignore "t"),
	   fun s ->
	     let t = Hashtbl.find s "t" in
	     RExact t)
	; (Term_match.App (Term_match.App (Term_match.Glob (lazy ptrn_app),
					   as_ignore "f"),
			   as_ignore "x"),
	   fun s ->
	     let f = Hashtbl.find s "f" in
	     let x = Hashtbl.find s "x" in
	     RApp (into_rpattern f, into_rpattern x))
	]
	ptrn
    in
    into_rpattern

  let rec count rp =
    match rp with
      RIgnore | RExact _ -> 0
    | RGet _ -> 1
    | RApp (a,b)
    | RPi (a,b)
    | RImpl (a,b) -> count a + count b

  let parse_rule gl (rule : Term.constr)
      (ptrn : Term.constr) (template : Term.constr)
  : rule =
    try
      let ptrn = into_rpattern gl ptrn in
      match ptrn with
	RExact g ->
	  (** no bindings **)
	  (Term_match.Glob (lazy g), fun _ -> template)
      | _ -> raise (Failure "not supported yet")
    with
      Term_match.Match_failure -> raise (Failure "match failed")

  let extend trm rul =
    Hashtbl.add extensions trm rul

  let add_rule gl (name : Term.constr)
      (ptrn : Term.constr) (template : Term.constr)
  : unit =
    let rule = parse_rule gl name ptrn template in
    extend name rule

end



VERNAC COMMAND EXTEND Reify_Lambda_Shell_add_hints
  | [ "Add" "Reification" "Hint" constr(pattern) "=>" constr(template) ":" constr(rule) ] ->
    [ try
	let (evm,env) = Lemmas.get_current_context () in
	let pattern   = Constrintern.interp_constr evm env pattern in
	let template  = Constrintern.interp_constr evm env template in
	let rule      = Constrintern.interp_constr evm env rule in
	Reification.add_rule env rule pattern template
      with
	Failure msg -> Pp.msgnl (Pp.str msg)
    ]
END;;

TACTIC EXTEND Reify_Lambda_Shell_reify
  | ["reify_expr" tactic(k) "[" ne_constr_list(es) "]" ] ->
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
