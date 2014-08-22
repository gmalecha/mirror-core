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
    (int Term_match.pattern) *
      ((int, Term.constr) Hashtbl.t -> Term.constr)

  let extensions : (Term.constr, rule) Hashtbl.t = Hashtbl.create 5

  let rec reify_special (name : Term.constr) (special : rule list) gl
      (trm : Term.constr) : Term.constr =
    try
      Term_match.matches gl special trm
    with
      Term_match.Match_failure ->
	begin
	  let _ = Format.eprintf "\n(%a): %a\n" Std.pp_constr name Std.pp_constr trm in
	  raise (Failure "Something bad")
	end
  and reify (name : Term.constr) gl : Term.constr -> Term.constr =
    reify_special name (Hashtbl.find_all extensions name) gl

  let pattern_mod = ["MirrorCore";"Reify";"Patterns"]

  let ptrn_exact    = Std.resolve_symbol pattern_mod "RExact"
  let ptrn_const    = Std.resolve_symbol pattern_mod "RConst"
  let ptrn_ignore   = Std.resolve_symbol pattern_mod "RIgnore"
  let ptrn_get      = Std.resolve_symbol pattern_mod "RGet"
  let ptrn_app      = Std.resolve_symbol pattern_mod "RApp"
  let ptrn_pi       = Std.resolve_symbol pattern_mod "RPi"
  let ptrn_impl     = Std.resolve_symbol pattern_mod "RImpl"
  let ptrn_has_type = Std.resolve_symbol pattern_mod "RHasType"

  let func_function = Std.resolve_symbol pattern_mod "function"
  let func_id       = Std.resolve_symbol pattern_mod "id"
(*  let act_get_store = Std.resolve_symbol pattern_mod "get_store" *)
(*  let act_call      = Std.resolve_symbol pattern_mod "reify" *)

  type rpattern =
  | RIgnore
  | RHasType of Term.constr * rpattern
  | RConst
  | RGet   of int * rpattern
  | RApp   of rpattern * rpattern
  | RPi    of rpattern * rpattern
  | RImpl  of rpattern * rpattern
  | RExact of Term.constr

  let as_ignore s = Term_match.As (Term_match.Ignore, s)

  let into_rpattern gl =
    let rec into_rpattern (ptrn : Term.constr) : rpattern =
      Term_match.matches gl
	[ (Term_match.EGlob ptrn_ignore,
	   fun _ -> RIgnore)
	; (Term_match.App (Term_match.App (Term_match.EGlob ptrn_get,
					   Term_match.As (Term_match.Ignore, 0)),
			   Term_match.As (Term_match.Ignore, 1)),
	   fun s ->
	     let num  = Hashtbl.find s 0 in
	     let next = Hashtbl.find s 1 in
	     RGet (Std.of_nat num, into_rpattern next))
	; (Term_match.App (Term_match.App (Term_match.EGlob ptrn_exact,
					   Term_match.Ignore),
			   as_ignore 0),
	   fun s ->
	     let t = Hashtbl.find s 0 in
	     RExact t)
	; (Term_match.App (Term_match.App (Term_match.EGlob ptrn_app,
					   as_ignore 0),
			   as_ignore 1),
	   fun s ->
	     let f = Hashtbl.find s 0 in
	     let x = Hashtbl.find s 1 in
	     RApp (into_rpattern f, into_rpattern x))
	; (Term_match.EGlob ptrn_const,
	   fun _s -> RConst)
	; (Term_match.App (Term_match.App (Term_match.EGlob ptrn_has_type,
					   as_ignore 0),
			   as_ignore 1),
	   fun s ->
	     let t = Hashtbl.find s 0 in
	     let x = Hashtbl.find s 1 in
	     RHasType (t, into_rpattern x))
	]
	ptrn
    in
    into_rpattern

  let rec app_full trm acc =
    match Term.kind_of_term trm with
      Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)


  let rec compile_pattern (p : rpattern)
  : int Term_match.pattern * int list =
    match p with
      RExact g ->
	(Term_match.EGlob g, [])
    | RIgnore -> (Term_match.Ignore, [])
    | RGet (i, p) ->
      let (p,us) = compile_pattern p in
      (Term_match.As (p, i), i :: us)
    | RApp (p1, p2) ->
      let (p1,l1) = compile_pattern p1 in
      let (p2,l2) = compile_pattern p2 in
      (Term_match.App (p1,p2), l1 @ l2)
    | RConst ->
      let rec filter trm =
	(** TODO: This does not handle polymorphic types right now **)
	let (f, args) = app_full trm [] in
	Term.isConstruct f && List.for_all filter args
      in
      (Term_match.Filter (filter, Term_match.Ignore),[])
    | RHasType (t,p) ->
      raise (Failure "has_type not currently supported")
    | _ -> raise (Failure "unsupported")

  type action =
    Func of Term.constr
  | Id

  let parse_action gl : Term.constr -> action option =
    Term_match.matches gl
      [ (Term_match.App (Term_match.EGlob func_function, as_ignore 0),
	 fun s -> Some (Func (Hashtbl.find s 0)))
      ; (Term_match.App (Term_match.EGlob func_id, Term_match.Ignore),
	 fun s -> Some Id)
      ; (Term_match.Ignore, fun _ -> None)
      ]

  let rec compile_template gl (tmp : Term.constr) (at : int)
  : Term.constr list -> (int, Term.constr) Hashtbl.t -> Term.constr =
    match Term.kind_of_term tmp with
      Term.Lambda (_, typ, body) ->
	begin
	  match parse_action gl typ with
	    None ->
	      fun ls _ ->
		Term.substnl ls 0 body
	  | Some act ->
	    let rest = compile_template gl body (at + 1) in
	    match act with
	    | Func f ->
	      fun vals s ->
		let cur_val = Hashtbl.find s at in
		rest (reify f gl cur_val :: vals) s
	    | Id ->
	      fun vals s ->
		let cur_val = Hashtbl.find s at in
		rest (cur_val :: vals) s
	end
    | _ ->
      fun ls _ ->
	Term.substnl ls 0 tmp

  let parse_rule gl (rule : Term.constr)
      (ptrn : Term.constr) (template : Term.constr)
  : rule =
    try
      let (ptrn, occs) = compile_pattern (into_rpattern gl ptrn) in
      let action = compile_template gl template 0 [] in
      (ptrn, action)
    with
      Term_match.Match_failure -> raise (Failure "match failed, please report")

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
  | ["reify_expr" constr(name) tactic(k) "[" ne_constr_list(es) "]" ] ->
    [ fun gl ->
        let env = Tacmach.pf_env gl in
	let evar_map = Tacmach.project gl in
	let res = List.map (Reification.reify name gl) es in
	let ltac_args =
	  List.map
	    Plugin_utils.Use_ltac.to_ltac_val
	    res
	in
	Plugin_utils.Use_ltac.ltac_apply k ltac_args gl
(*
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
*)
    ]
END;;
