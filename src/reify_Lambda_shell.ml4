(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Plugin_utils
open Reify_Core
open Reify_Monad

let contrib_name = "MirrorCore.Reify"

DECLARE PLUGIN "reify_Lambda_plugin"

module type REIFICATION =
sig

  type all_tables

  val parse_tables : Term.constr -> map_type list

  (** Tables **)
  val declare_table : Names.identifier -> Evd.evar_map -> Term.constr -> bool
  val declare_typed_table : Names.identifier -> Evd.evar_map -> Term.constr -> Term.constr -> bool
  val seed_table    : Term.constr -> int -> Term.constr -> bool
  val seed_typed_table    : Term.constr -> int -> Term.constr -> Term.constr -> bool

  (** Patterns **)
  val declare_pattern : Names.identifier -> Evd.evar_map -> Term.constr -> unit
  val add_pattern     : Term.constr -> Term.constr (* rpattern *) -> Term.constr -> Evd.evar_map -> unit
  val print_patterns  : Term.constr -> Pp.std_ppcmds

  (** Functions **)
  val declare_syntax : Names.identifier -> Environ.env -> Evd.evar_map -> Term.constr (* command *) -> unit

  (** Reification **)
  val reify     : Environ.env -> Evd.evar_map -> map_type list (* tables *) ->
    Term.constr -> Term.constr -> Term.constr * all_tables
  val reify_all : Environ.env -> Evd.evar_map -> map_type list (* tables *) ->
    (Term.constr * Term.constr) list -> Term.constr list * all_tables
  val export_table : Term.constr list -> map_type -> all_tables -> Term.constr

  val pose_each : (string * Term.constr) list -> (Term.constr list -> unit Proofview.tactic) -> unit Proofview.tactic

  val ic : ?env:Environ.env -> ?sigma:Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * Term.constr
  val ics : ?env:Environ.env -> ?sigma:Evd.evar_map -> Constrexpr.constr_expr list -> Evd.evar_map * Term.constr list

  val check_inside_section : string -> unit
  val error_parse : Term.constr -> string -> 'a
end

module Reification : REIFICATION =
struct

  module Std = Reify_Core.Std

  let do_debug = false

  let rec pr_constrs sep ks =
    Pp.prlist_with_sep (fun _ -> sep) Printer.pr_constr ks

  let debug_constr s e =
    if do_debug then
      (Pp.(msg_debug (  (str s) ++ (str ": ") ++ (Printer.pr_constr e))) ;
       Printf.eprintf "debug_constr\n" ;
       flush stderr)
    else
      ()
  let debug_pp p =
    if do_debug then
      (Pp.(msg_debug p) ; flush stderr)
    else ()

  let debug s =
    if do_debug then
      (Pp.(msg_debug (  str s)) ;
       Printf.eprintf "%s\n" s ;
       flush stderr)
    else
      ()

  let resolve_poly_symbol_no_univs path tm =
    lazy (
      let re = Coqlib.find_reference contrib_name path tm in
      fst (Universes.unsafe_constr_of_global re))

  type all_tables =
    { tables : (int * Term.constr) environment Cmap.t
    }

  let get_by_conversion renv (tbl : 'a environment)
      (target : Term.constr) : 'a option =
    let unifies = Reductionops.is_conv renv.env renv.evm target in
    Cmap.fold (fun k v a ->
        match a with
	  None -> if unifies k then Some v else None
        | Some k -> Some k) tbl.mappings None

  let decl_constant ?typ ?opaque:(opaque=false) (na : Names.identifier) evm (c : Term.constr) =
    (** TODO: This looks weird... **)
    let (evm, _) = Typing.type_of (Global.env ()) evm c in
    let vars = Universes.universes_of_constr c in
    let ctx = Universes.restrict_universe_context
        (Univ.ContextSet.of_context (snd (Evd.universe_context evm))) vars in
    Declare.(Term.mkConst(declare_constant na
			    (Entries.(DefinitionEntry
					(definition_entry ~opaque:opaque
                                           ~univs:(Univ.ContextSet.to_context ctx) ~poly:false c)),
			     Decl_kinds.(IsDefinition Definition))))

  let (reify_term, set_reify_term) =
    let global_reifier = ref (fun _ -> assert false) in
    let reify_term (t : Term.constr) = !global_reifier t in
    let set_reify_term rt = global_reifier := rt in
    (reify_term, set_reify_term)

  let pattern_mod = ["MirrorCore";"Reify";"Patterns"]

  module Tables =
  struct

    type key_type = Nat | Pos

    let the_seed_table : (int * Term.constr) environment Cmap.t ref =
      ref Cmap.empty

    (** Freezing and thawing of state (for backtracking) **)
    let _ =
      Summary.(declare_summary "reify-lambda-shell-seed-table"
	         { freeze_function = (fun _ -> !the_seed_table)
	         ; unfreeze_function = (fun pt -> the_seed_table := pt)
	         ; init_function = (fun () -> the_seed_table := Cmap.empty) })

    let check_compatible env evm (e : (int * Term.constr) environment) (i : int)
	(target_ty : Term.constr) (target_t : Term.constr) : bool =
      Cmap.for_all (fun k (id,ty) ->
	  if i = id then
	    Reductionops.is_conv env evm k target_t &&
	    Reductionops.is_conv env evm ty target_ty
	  else true) e.mappings

    let seed_table (tbl_name : Term.constr) (k : int) (t : Term.constr) (v : Term.constr)
      : bool =
      let (evm,env) = Lemmas.get_current_context () in
      try
	let tbl = Cmap.find tbl_name !the_seed_table in
	if check_compatible env evm tbl k t v then
	  let new_tbl = { mappings = Cmap.add v (k,t) tbl.mappings
			; next = max (k+1) tbl.next } in
	  the_seed_table := Cmap.add tbl_name new_tbl !the_seed_table ;
	  true
	else
	  let _ =
	    Pp.(msg_warning (   str "Table '"
		             ++ Printer.pr_constr tbl_name
	                     ++ str "' already contains a mapping for "
                             ++ int k ++ str "." ++ fnl ()
	                     ++ str "This mapping is incompatible with the given mapping."))
	  in false
      with
	Not_found ->
	let _ = Pp.(msg_warning (   str "Table '"
			         ++ Printer.pr_constr tbl_name
	                         ++ str "' does not exist.")) in
	false


    let declare_table (ls : Term.constr) (kt : key_type) =
      if Cmap.mem ls !the_seed_table then
	let _ =
	  Pp.(msg_warning (   str "Table '"
	                   ++ Printer.pr_constr ls
		           ++ str "' already exists."))
	in false
      else
	let _ =
	  the_seed_table := Cmap.add ls { mappings = Cmap.empty
					; next = 1
					} !the_seed_table
	in true

    let declare_typed_table (ls : Term.constr) (kt : key_type) =
      if Cmap.mem ls !the_seed_table then
	let _ =
	  Pp.(msg_warning (   str "Table '"
			   ++ Printer.pr_constr ls
			   ++ str "' already exists."))
	in false
      else
	let _ =
	  the_seed_table := Cmap.add ls { mappings = Cmap.empty
					; next = 1
					} !the_seed_table
	in true

  end

  module Patterns =
  struct

    (** [rule]s implement the pattern feature **)
    type rule =
      { rule_pattern : rpattern
      ; rule_template : template
      ; mutable rule_cache :
          (((int,int,reify_env) Term_match.pattern) *
           (reify_env -> (int, Term.constr) Hashtbl.t -> Term.constr reifier)) CEphemeron.key
      }

    type 'a ptrn_tree =
      { if_app      : 'a IntMap.t
      ; if_has_type : 'a Cmap.t
      ; if_exact    : 'a Cmap.t
      ; otherwise   : 'a
      }

    let empty_ptrn_tree default =
      { if_app = IntMap.empty
      ; if_has_type = Cmap.empty
      ; if_exact = Cmap.empty
      ; otherwise = default
      }

    let rec count_apps = function
      | RApp (a,_) -> count_apps a + 1
      | RExact t ->
        let result =
          match Term.kind_of_term t with
          | Term.App (_,args) -> Array.length args
          | _ -> 0
        in result
      | _ -> 0

    let rec has_open_end = function
      | RApp (a,_) -> has_open_end a
      | RExact _
      | RLam _
      | RPi _
      | RImpl _ -> false
      | _ -> true

    let ptrn_tree_add (type a) (p : rpattern)
        (v : a option -> a) (t : a ptrn_tree) =
      match p with
      | RApp (l,r) ->
        (* NOTE: This is conservative, if the pattern ends in an open pattern
         * (one that could match an application) then it is added
         * to 'otherwise' as well
        *)
        let arity = 1 + count_apps l in
        let cur =
          try Some (IntMap.find arity t.if_app)
          with Not_found -> None
        in { t with
             if_app = IntMap.add arity (v cur) t.if_app
           ; otherwise =
               if has_open_end l then v (Some t.otherwise)
               else t.otherwise }
      | RExact trm -> (** Check universes **)
        let cur =
          try Some (Cmap.find trm t.if_exact)
          with Not_found -> None
        in { t with
             if_exact = Cmap.add trm (v cur) t.if_exact }
      | RHasType (typ,_) ->
        let cur =
          try Some (Cmap.find typ t.if_has_type)
          with Not_found -> None
        in { t with
             if_has_type = Cmap.add typ (v cur) t.if_has_type }
      | _ -> { t with
               otherwise = v (Some t.otherwise) }

    let run_ptrn_tree compile_rule (tr : rule list ptrn_tree) trm gl =
      let get_rule rule =
        try CEphemeron.get rule.rule_cache
        with CEphemeron.InvalidKey ->
          let cache = compile_rule rule.rule_pattern rule.rule_template in
          let _ = rule.rule_cache <- CEphemeron.create cache in
          cache
      in
      match trm with
        Term trm ->
        begin
          try
            Term_match.matches gl
              (List.map get_rule (Cmap.find trm tr.if_exact))
              trm gl
          with Not_found | Term_match.Match_failure ->
          try
            match Term.kind_of_term trm with
            | Term.App (_,args) ->
              Term_match.matches gl
                (List.map get_rule (IntMap.find (Array.length args) tr.if_app))
                trm gl
            | _ -> raise Not_found
          with Not_found | Term_match.Match_failure ->
          try
            if not (Cmap.is_empty tr.if_has_type) then
              (* get the type *)
              let (_,ty) = Typing.type_of gl.env gl.evm trm in
              Term_match.matches gl
                (List.map get_rule (Cmap.find ty tr.if_has_type)) trm gl
            else raise Not_found
          with Not_found | Term_match.Match_failure ->
          try
            Term_match.matches gl (List.map get_rule tr.otherwise) trm gl
          with
            Term_match.Match_failure -> reifier_fail trm gl
        end
      | App (trm, args, from) ->
        begin
          assert false
        end

    (** State **)
    let pattern_table : rule list ptrn_tree Cmap.t ref =
      ref Cmap.empty

    (** Freezing and thawing of state (for backtracking) **)
    let _ =
      Summary.(declare_summary "reify-lambda-shell-pattern-table"
	         { freeze_function = (fun _ -> !pattern_table)
	         ; unfreeze_function = (fun pt -> pattern_table := pt)
	         ; init_function = (fun () -> pattern_table := Cmap.empty) })

    let empty_tree = empty_ptrn_tree []
    let add_empty_pattern name =
      if Cmap.mem name !pattern_table then
	Pp.(
	  msgnl (   (str "Pattern table '")
		    ++ (Printer.pr_constr name)
	            ++ (str "' already exists.")))
      else
	pattern_table := Cmap.add name empty_tree !pattern_table

    let declare_pattern (obj : Term.constr) =
      add_empty_pattern obj

    let extend trm key rul =
      try
	let objs = Cmap.find trm !pattern_table in
        let updated = ptrn_tree_add key (function None -> [rul]
                                                | Some xs -> rul :: xs) objs in
	pattern_table := Cmap.add trm updated !pattern_table
      with
      | Not_found ->
        let updated = ptrn_tree_add key (fun _ -> [rul]) empty_tree in
        pattern_table := Cmap.add trm updated !pattern_table

    let pr_paren = Pp.surround

    let rec print_pattern ptrn =
      Pp.(
	match ptrn with
	  RIgnore -> str "<any>"
        | RHasType (t,p) -> pr_paren (print_pattern p ++ str " : " ++ Printer.pr_constr t)
        | RConst -> str "<constant>"
        | RGet (i, p) -> pr_paren (int i ++ str " <- " ++ print_pattern p)
        | RApp (l, r) -> pr_paren (print_pattern l ++ str " @ " ++ print_pattern r)
        | RPi (l, _, r) -> pr_paren (str "forall _ : " ++ print_pattern l ++ str ", " ++ print_pattern r)
        | RLam (l, r) -> pr_paren (str "fun _ : " ++ print_pattern l ++ str " => " ++ print_pattern r)
        | RImpl (l,r) -> pr_paren (print_pattern l ++ str " -> " ++ print_pattern r)
        | RExact p -> pr_paren (str "! " ++ Printer.pr_constr p))

    let print_rule r = print_pattern r.rule_pattern

    let apps = List.fold_right Pp.(++)

    let print_patterns (name : Term.constr) : Pp.std_ppcmds =
      try
	let vals = Cmap.find name !pattern_table in
        Pp.pr_vertical_list print_rule
          (List.flatten (List.map snd (IntMap.bindings vals.if_app) @
                         List.map snd (Cmap.bindings vals.if_has_type) @
                         List.map snd (Cmap.bindings vals.if_exact) @
                         [vals.otherwise]))
      with Not_found ->
        Pp.(msg_warning (   (str "Unknown pattern table '")
  		            ++ (Printer.pr_constr name)
                            ++ (str "'."))) ;
        Pp.mt ()

    let reify_patterns compile_rule (i : Term.constr) trm
    : Term.constr reifier =
      fun gl ->
        let tbl =
          try Cmap.find i !pattern_table
          with Not_found ->
            Errors.anomaly Pp.(str "Invariant violation, please report!" ++
                               fnl () ++
                               str "pattern table not found:" ++ spc () ++
                               Printer.pr_constr i)
        in
        run_ptrn_tree compile_rule tbl trm gl

    let add_pattern compile_rule env evd
        (name : Term.constr) (ptrn : Term.constr) (template : Term.constr)
    : unit =
      try
        let rule = Reify_Core.parse_pattern env evd ptrn template in
        let rptrn = rule.Reify_Core.rule_pattern in
        let rtemplate = rule.Reify_Core.rule_template in
	extend name rptrn
          { rule_pattern = rptrn
          ; rule_template = rtemplate
          ; rule_cache = CEphemeron.create (compile_rule rptrn rtemplate)
          }
      with
	Term_match.Match_failure ->
        raise (Failure "match failed, please report")

  end

  module Syntax =
  struct

    type syntax_data =
      { reify       : lazy_term -> Term.constr reifier
      ; result_type : Term.constr
      }

    let reify_table : syntax_data CEphemeron.key Cmap.t ref =
      ref Cmap.empty

    let find for_var =
      let rec find ls i acc meta_offset =
	match ls with
          [] -> assert false
        | l :: ls ->
	  if i = 0 then
            begin
              match l with
                RBind -> for_var acc
              | RSkip -> assert false
              | Use -> Term.mkRel meta_offset
            end
          else
            match l with
              RBind -> find ls (i - 1) (acc + 1) meta_offset
            | RSkip -> find ls (i - 1) acc meta_offset
            | Use -> find ls (i - 1) acc (meta_offset + 1)
      in
      fun ls i -> find ls i 0 1

    (** Get the head symbol **)
    let rec app_full trm acc =
      match Term.kind_of_term trm with
        Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
      | _ -> (trm, acc)

    type pattern_effect = (int, Term.constr) Hashtbl.t -> reify_env -> reify_env


    (* This function compiles an [rpattern] into a [Term_match.pattern] and
     * a set of bindings
     *)
    let rec compile_pattern p =
      let fresh = ref (-1) in
      let effects : (int, pattern_effect) Hashtbl.t =
        Hashtbl.create 1
      in
      let rec compile_pattern (p : rpattern)
	  (effect : pattern_effect option)
	: (int,int,reify_env) Term_match.pattern =
	match p with
	  RExact g -> Term_match.EGlob_no_univ g
	| RIgnore -> Term_match.Ignore
	| RGet (i, p) ->
	  let p = compile_pattern p effect in
	  let _ =
	    match effect with
	      None -> ()
	    | Some eft -> Hashtbl.add effects i eft
	  in
          Term_match.As (p, i)
	| RApp (p1, p2) ->
	  let p1 = compile_pattern p1 effect in
	  let p2 = compile_pattern p2 effect in
          Term_match.App (p1,p2)
	| RConst ->
	  let filter _ =
	    let rec filter trm =
	      (** TODO: This does not support polymorphic types **)
	      let (f, args) = app_full trm [] in
	      Term.isConstruct f && List.for_all filter args
	    in
	    filter
	  in
	  Term_match.Filter (filter, Term_match.Ignore)
	| RImpl (p1, p2) ->
	  let p1 = compile_pattern p1 effect in
	  let fresh =
	    let r = !fresh in
	    fresh := r - 1 ;
	    r
	  in
	  let new_effect =
	    match effect with
	      None ->
	      fun s x ->
		let nbindings = RSkip :: x.bindings in
		let nenv =
		  Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		    x.env
		in
		{ x with bindings = nbindings ; env = nenv }
	    | Some eft ->
	      fun s x ->
		let x = eft s x in
		let nbindings = RSkip :: x.bindings in
		let nenv =
		  Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		    x.env
		in
		{ x with bindings = nbindings ; env = nenv }
	  in
	  let p2 = compile_pattern p2 (Some new_effect) in
	  Term_match.Impl (Term_match.As (p1,fresh),p2)
	| RPi (p1, uob, p2) ->
	  let p1 = compile_pattern p1 effect in
	  let fresh =
	    let r = !fresh in
	    fresh := r - 1 ;
	    r
	  in
	  let new_effect =
	    match effect with
	      None ->
	      fun s x ->
		let nbindings = uob :: x.bindings in
		let nenv =
		  Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		    x.env
		in
		{ x with bindings = nbindings ; env = nenv }
	    | Some eft ->
	      fun s x ->
		let x = eft s x in
		let nbindings = uob :: x.bindings in
		let nenv =
		  Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		    x.env
		in
		{ x with bindings = nbindings ; env = nenv }
	  in
	  let p2 = compile_pattern p2 (Some new_effect) in
	  Term_match.Pi (Term_match.As (p1,fresh),p2)
	| RHasType (t,p) ->
	  let p = compile_pattern p effect in
	  Term_match.Filter
	    ((fun env trm ->
	        let (_,ty) = Typing.type_of env.env env.evm trm in
	        Term.eq_constr ty t), p)
        | RLam (a,b) -> assert false
      in
      let ptrn = compile_pattern p None in
      (ptrn, effects)

    and compile_template stk
	(effects : (int, pattern_effect) Hashtbl.t)
        tmp =
      let rec compile_template (tmp : template) (at : int)
        : Term.constr list -> reify_env -> (int, Term.constr) Hashtbl.t ->
	  Term.constr reifier =
        match tmp with
        | Return t -> fun ls _ _ -> reifier_ret (Vars.substnl ls 0 t)
        | Bind (act, rest) ->
	  let rest = compile_template rest (at + 1) in
          let eft =
            try Hashtbl.find effects at
	    with Not_found -> (fun _ x -> x)
          in
	  match act with
          | Func f ->
            let reifier = compile_command stk f in
	    fun vals gl s ->
              let cur_val = Hashtbl.find s at in
	      let rval = reifier_run (reifier_local (eft s) (reifier (Term cur_val))) gl in
	      rest (rval :: vals) gl s
	  | Id ->
            fun vals gl s ->
	      let cur_val = Hashtbl.find s at in
              reifier_bind
	        reifier_get_env
	        (fun env ->
	           if Vars.noccur_between 1 (List.length env.bindings) cur_val then
	             rest (cur_val :: vals) gl s
	           else
	             reifier_fail cur_val)
      in compile_template tmp 0 []

    and compile_rule stk rptrn template =
      let (ptrn, effects) = compile_pattern rptrn in
      let action = compile_template stk effects template in
      (ptrn, action)

    and compile_patterns stk ptrns =
      List.fold_left (fun acc ptrn ->
          let rptrn = ptrn.Reify_Core.rule_pattern in
          let template = ptrn.Reify_Core.rule_template in
          let cptrn =
            { Patterns.rule_pattern = rptrn
            ; Patterns.rule_template = template
            ; Patterns.rule_cache =
                CEphemeron.create (compile_rule stk rptrn template)
            }
          in
          Patterns.ptrn_tree_add ptrn.rule_pattern
            (function None -> [cptrn]
                    | Some xs -> cptrn :: xs) acc)
        (Patterns.empty_ptrn_tree []) ptrns

    and compile_command (stk : (lazy_term -> Term.constr reifier) ref list)
        (ls : command)
    : lazy_term -> Term.constr reifier =
      let rec compile_command stk (l : command)
        : lazy_term -> Term.constr reifier =
	match l with
        | Rec n ->
          let r = List.nth stk n in
          fun trm gl -> !r trm gl
        | Fix k ->
          let z = ref (fun _ -> assert false) in
          let k = compile_command (z :: stk) k in
          z := k ;
          k
        | Call f ->
          fun trm gl -> reify_term f trm gl
	| Patterns i ->
          fun trm gl ->
            Patterns.reify_patterns (fun c -> compile_rule [] c) i trm gl
        | Pattern ptrns ->
          let ptrns = compile_patterns stk ptrns in
          fun trm gl -> Patterns.run_ptrn_tree (compile_rule stk) ptrns trm gl
	| Abs (ty,body,ctor) ->
          let reify_type = compile_command stk ty in
          let reify_term = compile_command stk body in
	  fun trm gl ->
	    begin
	      match Term.kind_of_term (get_term trm) with
		Term.Lambda (name, lhs, rhs) ->
		let ty = reify_type (Term lhs) gl in
		let new_gl =
		  { gl with
		    env = Environ.push_rel (name, None, lhs) gl.env
		  ; bindings = RBind :: gl.bindings
		  }
		in
		let body = reifier_run (reify_term (Term rhs)) new_gl in
		Term.mkApp (ctor, [| ty ; body |])
	      | _ -> reifier_fail_lazy trm gl
	    end
        | PiMeta (ty,cmd) ->
          let reify_body = compile_command stk cmd in
	  fun trm gl ->
	    begin
	      match Term.kind_of_term (get_term trm) with
		Term.Prod (name, lhs, rhs) ->
                reifier_under_binder ~name Use lhs
                  (reifier_fmap
                     (fun b -> Term.mkLambda (Names.Anonymous, ty, b))
                     (reify_body (Term rhs))) gl
	      | _ -> reifier_fail_lazy trm gl
	    end
	| Var ctor ->
          let mkVar idx = Term.mkApp (ctor, [| Std.Nat.to_nat idx |]) in
	  fun trm gl ->
	    begin
       	      match Term.kind_of_term (get_term trm) with
		Term.Rel i ->
		find mkVar gl.bindings (i-1)
	      | _ -> reifier_fail_lazy trm gl
	    end
	| App (f,x,ctor) ->
          let f = compile_command stk f in
          let x = compile_command stk x in
	  fun trm gl ->
	    begin
	      try
		Term_match.(matches gl
			      [ (App (get 0, get 1),
				 fun gl s ->
				   let f = f (Term (Hashtbl.find s 0)) gl in
				   let x = x (Term (Hashtbl.find s 1)) gl in
				   Term.mkApp (ctor, [| f ; x |]))
			      ])
		  (get_term trm)
	      with
		Term_match.Match_failure -> reifier_fail_lazy trm gl
	    end
	| Table tbl_name ->
	  begin
	    let build = Std.Positive.to_positive in
	    fun trm renv ->
	      let tbl =
		let tbls = !(renv.typed_tables) in
		try
		  Cmap.find tbl_name tbls
		with
		  Not_found ->
		  let all_tables = List.map fst (Cmap.bindings tbls) in
		  let _ =
		    Pp.(msg_warning
			  (   str "Implicitly adding table '"
	                   ++ Printer.pr_constr tbl_name
		           ++ str "'. This will not be returned.\n"
			   ++ str "(available tables are: "
			   ++ pr_constrs (str " , ") all_tables
			   ++ str ")"))
		  in
		  { mappings = Cmap.empty
		  ; next = 1 }
	      in
	      let full_term = get_term trm in
	      try
		(** fast path something already in the table **)
		build (fst (Cmap.find full_term tbl.mappings))
	      with
		Not_found ->
		match get_by_conversion renv tbl full_term with
		  None ->
		  let (result, new_tbl) =
		    let result = tbl.next in
		    let value = (result, Lazy.force Std.Unit.tt) in
		    (result,
		     { next = result + 1
		     ; mappings = Cmap.add full_term value tbl.mappings })
		  in
		  renv.typed_tables :=
		    Cmap.add tbl_name new_tbl !(renv.typed_tables) ;
		  build result
		| Some k -> build (fst k)
	  end
	| TypedTable (tbl_name, cmd_type) ->
	  begin
	    let build = Std.Positive.to_positive in
            let reify_type = compile_command stk cmd_type in
	    fun trm renv ->
	      let tbls = !(renv.typed_tables) in
	      let tbl =
		try
		  Cmap.find tbl_name tbls
		with
		  Not_found ->
		  let all_tables = List.map fst (Cmap.bindings tbls) in
		  let _ =
		    Pp.(msg_warning
			  (   str "Implicitly adding table '"
			   ++ Printer.pr_constr tbl_name
			   ++ str "'. This will not be returned.\n"
			   ++ str "(available tables are: "
			   ++ pr_constrs (str " , ") all_tables
			   ++ str ")"))
		  in
		  { mappings = Cmap.empty
		  ; next = 1 }
	      in
	      let full_term = get_term trm in
	      let (_,type_of) = Typing.type_of renv.env renv.evm full_term in
	      let rtyp = reify_type (Term type_of) renv in
	      try
                (** fast path something already in the table **)
		let x = Cmap.find full_term tbl.mappings in
		build (fst x)
	      with
		Not_found ->
		match get_by_conversion renv tbl full_term with
		  None ->
		  let (result, new_tbl) =
		    let result = tbl.next in
		    let value = (result, rtyp) in
		    (result,
		     { next = result + 1
		     ; mappings = Cmap.add full_term value tbl.mappings })
		  in
		  renv.typed_tables := Cmap.add tbl_name new_tbl !(renv.typed_tables) ;
		  build result
		| Some k -> build (fst k)
	  end
	| Map (f,n) ->
	  let cmd = compile_command stk n in
	  begin
	    fun trm ->
	      reifier_bind (cmd trm) (fun t -> reifier_ret (Term.mkApp (f, [| t |])))
	  end
	| Or (a,b) ->
          let l = compile_command stk a in
          let k = compile_command stk b in
          begin
	    fun t gl -> reifier_try (l t) (k t) gl
          end
        | Fail ->
          reifier_fail_lazy
      in
      let result = compile_command stk ls in
      let result =
        fun trm gl ->
          reifier_try
	    (fun gl ->
               let strm = get_term trm in
               match Term.kind_of_term strm with
                 Term.Rel i ->
		 find (fun _ ->
                     raise (ReificationFailure (Lazy.from_val strm)))
                   gl.bindings (i-1)
               | _ -> reifier_fail_lazy trm gl)
            (result trm) gl
      in
      result

    (** Freezing and thawing of state (for backtracking) **)
    let _ =
      Summary.(declare_summary "reify-lambda-shell-syntax-table"
	         { freeze_function   = (fun _ -> !reify_table);
	           unfreeze_function = (fun pt -> reify_table := pt);
	           init_function     = (fun () -> reify_table := Cmap.empty) })

    let cmd_Command  = resolve_poly_symbol_no_univs pattern_mod "Command"
    let get_Command_type env evm cmd =
      let (_,typ) =
        try Typing.type_of env evm cmd
        with _ ->
          Errors.errorlabstrm "Type error"
            Pp.(   str "Reification command is ill-typed"
                ++ fnl ()
                ++ Printer.pr_constr_env env evm cmd)
      in
      try
        Term_match.(matches ()
                      [(apps (Glob_no_univ cmd_Command) [get 0],
                        fun _ s -> Hashtbl.find s 0)]
                      typ)
      with
        Term_match.Match_failure ->
        Errors.errorlabstrm "Type error"
          Pp.(   str "Reification got non-Command"
              ++ fnl ()
              ++ Printer.pr_constr_env env evm cmd
              ++ fnl ()
              ++ str "has type" ++ fnl ()
              ++ Printer.pr_constr_env env evm typ)

    let compile_name (prg : Term.constr) =
      let (evm,env) = Lemmas.get_current_context () in
      let typ = get_Command_type env evm prg in
      let reduced = Reductionops.whd_betadeltaiota env evm prg in
      let program = parse_command env evm reduced in
      try
        { result_type = typ
        ; reify = compile_command [] program }
      with
      | _ ->
        Errors.anomaly
          Pp.(   str "Failed to compile" ++ fnl ()
              ++ Printer.pr_constr prg
              ++ fnl ())

    let get_entry (name : Term.constr) =
      let name = drop_calls name in
      try
        let key = Cmap.find name !reify_table in
        try CEphemeron.get key
        with CEphemeron.InvalidKey ->
          let data = compile_name name in
          reify_table := Cmap.add name (CEphemeron.create data) !reify_table ;
          data
      with
        Not_found ->
        if not (Term.isConst name) then
          debug_pp Pp.(   str "compiling inline reify command (this may impact performance):"
                       ++ spc () ++ Printer.pr_constr name) ;
        let data = compile_name name in
        reify_table := Cmap.add name (CEphemeron.create data) !reify_table ;
        data

    let reify_term (name : Term.constr) =
      let data = get_entry name in
      data.reify

    let _ = set_reify_term reify_term

    let reify_type (name : Term.constr) =
      let data = get_entry name in
      data.result_type

    let declare_syntax (name : Names.identifier) env evm
	(cmd : Term.constr) : unit =
      let typ =
        let (_,typ) = Typing.type_of env evm cmd in
        let open Term_match in
        matches ()
          [ (apps (Glob_no_univ cmd_Command) [get 0],
             fun _ s -> Hashtbl.find s 0)
          ; (get 0,
             fun _ s -> Errors.errorlabstrm "type-error"
                 Pp.(   str "Syntax must have type"
                     ++ Printer.pr_constr (Lazy.force cmd_Command))) ]
          typ
      in
      let program = parse_command env evm cmd in
      let _meta_reifier = compile_command [] program in
      let data = { result_type = typ
                 ; reify = _meta_reifier } in
      let obj = decl_constant name evm cmd in
      reify_table := Cmap.add obj (CEphemeron.create data) !reify_table
  end

  let initial_env (env : Environ.env) (evar_map : Evd.evar_map)
      (tbls : map_type list) =
    let init_table =
      let seed_table = !Tables.the_seed_table in
      let find_default x =
        try Cmap.find x seed_table
        with
          _ -> (* You can not use an undeclared table **)
          raise (Failure "Bad table setup")
      in
      List.fold_left (fun acc tbl ->
          Cmap.add tbl.table_name (find_default tbl.table_name) acc)
        Cmap.empty tbls
    in
    { env = env
    ; evm = evar_map
    ; bindings = []
    ; typed_tables = ref !Tables.the_seed_table }

  let reify (env : Environ.env) (evm : Evd.evar_map) tbls (name : Term.constr)
      trm =
    let env = initial_env env evm tbls in
    let result = Syntax.reify_term name (Term trm) env in
    (result, { tables = !(env.typed_tables) })

(*
  let rec wrap_lambdas t =
    function [] -> t
           | typ :: typs ->
             wrap_lambdas (Term.mkLambda (Names.Anonymous, typ, t)) typs

  let polymorphically k pred =
    function [] -> k (Term pred)
           | all_ts ->
             let pargs = List.length all_ts in
             let rec polymorphically n pred =
               function [] -> reifier_bind (k (Term pred))
                                (fun t -> reifier_ret (wrap_lambdas t all_ts))
                      | t::ts ->
                        Term_match.matches n
                          [ (Term_match.Pi (Term_match.get 0, Term_match.get 1),
                             fun n s ->
                               let t = Hashtbl.find s 0 in
                               assert (Term.isSort t) ;
                               let b = Hashtbl.find s 1 in
                               reifier_under_binder Use t
                                 (polymorphically (n+1) b ts))
                          ; (Term_match.Ignore,
                             fun _ _ -> raise (ReificationFailure (lazy pred)))
                          ]
                          pred
             in
             polymorphically 0 pred all_ts

  let lemma_mod = ["MirrorCore";"Lemma"]

  let reify_lemma
      ~type_fn:typ_rule ~prem_fn:prem_rule ~concl_fn:concl_rule env evm pargs pred =
    let build_lemma = Std.resolve_symbol lemma_mod "Build_lemma" in
    let ty = Syntax.reify_type typ_rule in
    let finish alls prems pred =
      let pr = Syntax.reify_type prem_rule in
      let co = Syntax.reify_type concl_rule in
      let lem = Term.mkApp (Lazy.force build_lemma,
                            [| ty ; pr ; co
                             ; Std.List.to_list ty alls
                             ; Std.List.to_list pr (List.rev prems)
                             ; pred |]) in
      reifier_ret lem
    in
    let get_prems alls =
      let rec get_prems prems pred =
        Term_match.matches ()
          [ (Term_match.Impl(Term_match.get 0, Term_match.get 1),
             fun () s ->
               let t = Hashtbl.find s 0 in
               let b = Hashtbl.find s 1 in
               reifier_bind
                 (Syntax.reify_term prem_rule (Term t))
                 (fun pr ->
                    reifier_under_binder RSkip t
                      (get_prems (pr :: prems) b)))
          ; (Term_match.Ignore,
             fun () s ->
               reifier_bind
                 (Syntax.reify_term concl_rule (Term pred))
                 (fun result -> finish alls prems result))
          ]
          pred
      in get_prems
    in
    let rec get_foralls alls pred =
      Term_match.matches ()
        [ (Term_match.Impl (Term_match.Ignore, Term_match.Ignore),
           fun () _ -> get_prems alls [] pred)
        ; (Term_match.Pi(Term_match.get 0, Term_match.get 1),
           fun () s ->
             let t = Hashtbl.find s 0 in
             let b = Hashtbl.find s 1 in
             reifier_bind
               (Syntax.reify_term typ_rule (Term t))
               (fun ty ->
                  reifier_under_binder RBind t (get_foralls (ty :: alls) b)))
        ; (Term_match.Ignore,
           fun () _ -> get_prems alls [] pred)
        ]
        pred
    in
    let rec dup n =
      if n <= 0 then [] else ty :: dup (n-1)
    in
    try
      reifier_run (polymorphically (fun x -> get_foralls [] (get_term x)) pred (dup pargs))
        (initial_env env evm [])
    with
    | Not_found -> assert false

  let declare_syntax_lemma
      ~name:name ~type_fn:typ_rule ~prem_fn:prem_rule ~concl_fn:concl_rule
      env evm pargs pred =
    let body =
      try
        reify_lemma ~type_fn:typ_rule ~prem_fn:prem_rule ~concl_fn:concl_rule
          env evm pargs pred
      with
        Not_found ->
        assert false
    in
    let _ = decl_constant name evm body in
    ()
*)

  let reify_all (env : Environ.env) (evm : Evd.evar_map) tbls ns_e =
    let start_time = Sys.time () in
    let st = initial_env env evm tbls in
    let result =
      List.map (fun (ns,e) -> Syntax.reify_term ns (Term e) st) ns_e
    in
    let end_time = Sys.time () in
    Pp.(msg_info (str "Total reification time = " ++ real (end_time -. start_time))) ;
    (result, { tables = !(st.typed_tables) })


  let export_table bindings mt tbls =
    let insert_at v =
      let rec insert_at n ls =
	match ls with
	| [] -> if n = 0 then [Some v]
	  else None :: insert_at (n - 1) ls
	| l :: ls -> if n = 0 then Some v :: ls
	  else l :: insert_at (n - 1) ls
      in
      insert_at
    in
    let build tbl = Cmap.fold (fun trm (idx,typ) acc ->
        insert_at (typ,trm) (idx - 1) acc) tbl []
    in
    let maker =
      match mt.table_scheme with
      | SimpleMap ->
	fun (_,tt) ->
	  Vars.substnl bindings 0 (Term.mkApp (mt.table_elem_ctor, [| tt |]))
      | TypedMap ->
	fun (ty,tt) ->
	  Vars.substnl bindings 0 (Term.mkApp (mt.table_elem_ctor, [| ty ; tt |]))
      | TypedMapAbs abs_typ ->
	fun (ty,tt) ->
	  let v =
	    Term.mkApp (Vars.substnl bindings 0 mt.table_elem_ctor,
			[| Vars.substnl bindings 0 ty
			 ; Term.mkLambda (Names.Anonymous,
					  Vars.substnl bindings 0 abs_typ,
					  Vars.substnl bindings 0 tt) |])
	  in
	  v
    in
    let typ = Vars.substnl bindings 0 mt.table_elem_type in
    (*    let ctor = Term.substnl bindings 0 mt.table_elem_ctor in *)
    let ary_typ = [| typ |] in
    let leaf = Term.mkApp (Lazy.force Std.PosMap.c_leaf, ary_typ)  in
    let branch = Term.mkApp (Lazy.force Std.PosMap.c_node, ary_typ) in
    let branch x y z =
      let y =
	match y with
	| None -> None
	| Some ab -> Some (maker ab)
      in
      Term.mkApp (branch, [| x ; Std.Option.to_option typ y ; z |])
    in
    let tbl =
      try
	let env = Cmap.find mt.table_name tbls.tables in
	env.mappings
      with
	Not_found -> Cmap.empty (** This table wasn't seeded **)
    in
    Std.PosMap.to_posmap leaf branch (fun x -> x) (build tbl)

  let table_type = resolve_poly_symbol_no_univs pattern_mod "table"
  let table_value = resolve_poly_symbol_no_univs pattern_mod "a_table"
  let typed_table_type = resolve_poly_symbol_no_univs pattern_mod "typed_table"
  let typed_table_value = resolve_poly_symbol_no_univs pattern_mod "a_typed_table"

  let new_table
  : Term.constr * Tables.key_type -> Libobject.obj =
    let open Libobject in
    declare_object
      { (default_object "REIFY_TABLE") with
	load_function = (fun i (obj_name,value) ->
	    let (name,typ) = value in
            if Tables.declare_table name typ then ()
            else Printf.fprintf stderr "error declaring table")
      ; classify_function = (fun a -> Substitute a)
      ; discharge_function = (fun (_,value) -> Some value)
      ; subst_function = (fun (sub, (c,kt)) ->
          (Mod_subst.subst_mps sub c, kt))
      }

  let new_table_entry
  : Term.constr * int * (Term.constr * Term.constr) -> Libobject.obj =
    let open Libobject in
    declare_object
      { (default_object "REIFY_TABLE_ENTRY") with
        load_function = (fun i (obj_name,value) ->
	    (** TODO: What do I do about [i] and [obj_name]? **)
	    let (tbl_name, key, (ty,value)) = value in
            Printf.eprintf "Loading table entry %d\n" key ;
	    if Tables.seed_table tbl_name key ty value then ()
            else Printf.fprintf stderr "non-existant table")
      ; classify_function = (fun a -> Substitute a)
      ; subst_function = (fun (sub, (nm, i, (ty, trm))) ->
          (Mod_subst.subst_mps sub nm, i,
           (Mod_subst.subst_mps sub ty, Mod_subst.subst_mps sub trm)))
      }

  let declare_table id evm key =
    let key_type =
      if Term.eq_constr key (Lazy.force Std.Nat.nat_type) then Tables.Nat
      else if Term.eq_constr key (Lazy.force Std.Positive.pos_type) then Tables.Pos
      else assert false
    in
    let key_ary = [| key |] in
    let obj = decl_constant ~typ:(Term.mkApp (Lazy.force table_type, key_ary))
        id evm (Term.mkApp (Lazy.force table_value, key_ary))
    in
    if Tables.declare_table obj key_type then
      let _ = Lib.add_anonymous_leaf (new_table (obj, key_type))
      in true
    else false

  let declare_typed_table id evm key typ =
    let key_type =
      if Term.eq_constr key (Lazy.force Std.Nat.nat_type) then Tables.Nat
      else if Term.eq_constr key (Lazy.force Std.Positive.pos_type) then Tables.Pos
      else assert false
    in
    let key_ary = [| key ; typ |] in
    let obj = decl_constant ~typ:(Term.mkApp (Lazy.force typed_table_type, key_ary))
        id evm (Term.mkApp (Lazy.force typed_table_value, key_ary))
    in
    if Tables.declare_table obj key_type then
      let _ = Lib.add_anonymous_leaf (new_table (obj, key_type)) in
      true
    else false

  let seed_table name key value =
    let ty = Lazy.force Std.Unit.tt in
    if Tables.seed_table name key ty value then
      let _ =
	Lib.add_anonymous_leaf (new_table_entry (name, key, (ty, value)))
      in true
    else
      (Pp.(msg_debug (str "failed to seed table: " ++ Printer.pr_constr name)) ;
       false)

  let seed_typed_table name key ty value =
    if Tables.seed_table name key ty value then
      let _ =
	Lib.add_anonymous_leaf (new_table_entry (name, key, (ty, value)))
      in true
    else
      (Pp.(msg_debug (str "failed to seed typed table: " ++ Printer.pr_constr name)) ;
       false)

  let a_pattern = resolve_poly_symbol_no_univs pattern_mod "a_pattern"

  let declare_pattern (name : Names.identifier) evd (value : Term.constr) =
    let obj = decl_constant ~opaque:true name evd (Term.mkApp (Lazy.force a_pattern, [| value |])) in
    (*    let _ = Lib.add_anonymous_leaf (pattern_table_object obj) in *)
    Patterns.declare_pattern obj

  let print_patterns = Patterns.print_patterns

  let new_pattern_object
    : Term.constr * Term.constr * Term.constr -> Libobject.obj =
    Libobject.(declare_object
                 { (default_object "REIFY_ADD_PATTERN") with
                   classify_function = (fun x -> Substitute x)
                 ; subst_function = (fun (subst, (collection, ptrn, rule)) ->
                     (Mod_subst.subst_mps subst collection,
                      Mod_subst.subst_mps subst ptrn,
                      Mod_subst.subst_mps subst rule))
                 ; discharge_function = (fun (obj_name,value) ->
                     Some value)
                 ; load_function = (fun i (obj_name,value) ->
	             let (collection, ptrn, rule) = value in
                     Patterns.add_pattern (Syntax.compile_rule [])
                       Environ.empty_env Evd.empty (** NOTE: neither should be necessary *)
                       collection ptrn rule)
                 ; rebuild_function = (fun value ->
                     let (collection, ptrn, rule) = value in
                     let _ =
                       Patterns.add_pattern (Syntax.compile_rule [])
                         Environ.empty_env Evd.empty collection ptrn rule in
                     value)
                 })

  let add_pattern (name : Term.constr)
      (ptrn : Term.constr) (template : Term.constr) evm : unit =
    let _ = Patterns.add_pattern (Syntax.compile_rule [])
        Environ.empty_env Evd.empty (** TODO: neither should be necessary *)
        name ptrn template in
    let fresh_name = Namegen.next_global_ident_away
        (Names.id_of_string "_pattern_name") []
    in
    let _ = decl_constant fresh_name evm template in
    Lib.add_anonymous_leaf (new_pattern_object (name, ptrn, template))

  let declare_syntax = Syntax.declare_syntax

  let mk_var_map = resolve_poly_symbol_no_univs pattern_mod "mk_var_map"
  let mk_dvar_map = resolve_poly_symbol_no_univs pattern_mod "mk_dvar_map"
  let mk_dvar_map_abs = resolve_poly_symbol_no_univs pattern_mod "mk_dvar_map_abs"

  let parse_table (trm : Term.constr) : map_type =
    let open Term_match in
    matches ()
      [ (apps (Glob_no_univ mk_var_map) [Ignore;Ignore;get 2;get 0;get 1],
	 fun _ s -> { table_name = Hashtbl.find s 0
	            ; table_elem_type = Hashtbl.find s 2
	            ; table_elem_ctor = Hashtbl.find s 1
	            ; table_scheme = SimpleMap })
      ; (apps (Glob_no_univ mk_dvar_map) [Ignore;Ignore;get 2;Ignore;
					  get 0;get 1],
	 fun _ s -> { table_name = Hashtbl.find s 0
	            ; table_elem_type = Hashtbl.find s 2
	            ; table_elem_ctor = Hashtbl.find s 1
	            ; table_scheme = TypedMap })
      ; (apps (Glob_no_univ mk_dvar_map_abs) [Ignore;Ignore;get 2;get 3;
					      Ignore;get 0;get 1],
	 fun _ s -> { table_name = Hashtbl.find s 0
	            ; table_elem_type = Hashtbl.find s 2
	            ; table_elem_ctor = Hashtbl.find s 1
	            ; table_scheme = TypedMapAbs (Hashtbl.find s 3) })
      ] trm

  let rec parse_tables (tbls : Term.constr) : map_type list =
    let open Term_match in
    matches ()
      [ (Lam (0,get 0,get 1),
	 fun _ s ->
             parse_table (Hashtbl.find s 0)
          :: parse_tables (Hashtbl.find s 1))
      ; (Ignore, fun _ s -> [])
      ] tbls


  let rec pose_each (ls : (string * Term.constr) list)
      (k : Term.constr list -> 'a) : 'a =
    match ls with
      [] -> k []
    | (s,trm) :: ls ->
      Plugin_utils.Use_ltac.pose s trm
        (fun var -> pose_each ls (fun vs -> k (var :: vs)))

  let ic ?env ?sigma c =
    let env =
      match env with
      | None -> snd (Lemmas.get_current_context ())
      | Some x -> x
    in
    let sigma =
      match sigma with
      | None -> fst (Lemmas.get_current_context ())
      | Some x -> x
    in
    Constrintern.interp_open_constr env sigma c

  let k ls evm = (evm,ls)

  let ics ?env ?sigma ls =
    let env =
      match env with
      | None -> snd (Lemmas.get_current_context ())
      | Some x -> x
    in
    let sigma =
      match sigma with
      | None -> fst (Lemmas.get_current_context ())
      | Some x -> x
    in
    let rec go evm k = function
        [] -> k [] evm
      | c :: cs ->
        let (cc, uevm) = Constrintern.interp_constr env evm c in
        go (Evd.merge_universe_context evm uevm)
          (fun ls evm -> k (cc::ls) evm) cs
    in go sigma k ls

  let check_inside_section the_msg =
    if Lib.sections_are_opened () then
      (** In trunk this seems to be moved to Errors **)
      Errors.errorlabstrm contrib_name Pp.(   str "You can not" ++ spc ()
                                           ++ str the_msg ++ spc ()
                                           ++ str "in a section.")
    else ()

  let error_parse trm typ =
    Errors.errorlabstrm contrib_name
      Pp.(   str "Failed to parse "
          ++ str typ
          ++ str " from '"
          ++ Printer.pr_constr trm
          ++ str "'.")

end

VERNAC COMMAND EXTEND Reify_Lambda_Shell_add_lang
  | [ "Reify" "Declare" "Syntax" ident(name) ":=" lconstr(cmd) ] ->
    [ Reification.check_inside_section "declare patterns" ;
      let (evm,cmd) = Reification.ic cmd in
      let env = snd (Lemmas.get_current_context ()) in
      try
        Reification.declare_syntax name env evm cmd
      with
        ParseFailure (trm, typ) -> Reification.error_parse trm typ
    ]
END

(** Patterns **)
VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Pattern
  | [ "Reify" "Declare" "Patterns" ident(name) ":" lconstr(value) ] ->
    [ Reification.check_inside_section "declare patterns" ;
      let (evd,value) = Reification.ic value in
      try
        Reification.declare_pattern name evd value
      with
        ParseFailure (trm, typ) -> Reification.error_parse trm typ
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Add_Pattern
  | [ "Reify" "Pattern" constr(rule) "+=" constr(pattern) "=>" lconstr(template) ] ->
    [ Reification.check_inside_section "add patterns" ;
      try
        let (evm, [pattern;template;rule]) =
          Reification.ics [pattern;template;rule] in
	Reification.add_pattern rule pattern template evm
      with
	Failure msg -> Errors.errorlabstrm "Reify" (Pp.str msg)
      | ParseFailure (trm, typ) -> Reification.error_parse trm typ
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Print_Pattern CLASSIFIED AS QUERY
  | [ "Reify" "Print" "Patterns" constr(name) ] ->
    [ let (_,name) = Reification.ic name in
      Pp.(msg_info (   str "Patterns for "
	            ++ Printer.pr_constr name
	            ++ str ":"
	            ++ fnl ()
	            ++ Reification.print_patterns name))
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Table
  | [ "Reify" "Declare" "Table" ident(name) ":" constr(key) ] ->
    [ Reification.check_inside_section "declare tables" ;
      let (evm,key) = Reification.ic key in
      if Reification.declare_table name evm key then
	()
      else
        Errors.errorlabstrm "Reify"
          Pp.(   str "Error creating table '"
              ++ str (Names.string_of_id name)
              ++ str "'.")
    ]
  | [ "Reify" "Declare" "Typed" "Table" ident(name) ":" constr(key) "=>" lconstr(typ) ] ->
    [ Reification.check_inside_section "declare typed tables" ;
      let (evm,env) = Lemmas.get_current_context () in
      let (evm,[key;typ]) = Reification.ics [key;typ] in
      if Reification.declare_typed_table name evm key typ then
	()
      else
	Errors.errorlabstrm "Reify"
          Pp.(str "Failed to declare table.")
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Seed_Table
  | [ "Reify" "Seed" "Table" constr(tbl) "+=" integer(key) "=>" lconstr(value) ] ->
    [ let (evm,[tbl;value])   = Reification.ics [tbl;value] in
      if Reification.seed_table tbl key value then
	()
      else
	Errors.errorlabstrm "Reify"
          Pp.(   str "Failed to seed the table "
              ++ Printer.pr_constr tbl
              ++ str " table.") ]
  | [ "Reify" "Seed" "Typed" "Table" constr(tbl) "+=" integer(key) "=>"
	"[[" constr(typ) "," constr(value) "]]" ] ->
    [ let (evm,[tbl;typ;value]) = Reification.ics [tbl;typ;value] in
      if Reification.seed_typed_table tbl key typ value then
	()
      else
	Errors.errorlabstrm "Reify"
          Pp.(   str "Failed to seed the typed table "
              ++ Printer.pr_constr tbl
              ++ str " table.") ]
END

TACTIC EXTEND Reify_Lambda_Shell_reify
  | ["reify_expr" constr(name) tactic(k) "[[" constr(tbls) "]]" "[[" ne_constr_list(es) "]]" ] ->
    [ let tbls = Reification.parse_tables tbls in
      Proofview.Goal.enter begin fun gl ->
	try
	  let (res,tbl_data) =
	    Reification.reify_all (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)
              tbls (List.map (fun e -> (name,e)) es)
	  in
	  let rec generate tbls acc =
	    match tbls with
	      [] ->
		let ltac_args =
		  List.map
		    Plugin_utils.Use_ltac.to_ltac_val
		    (List.rev_append acc res)
		in
		Plugin_utils.Use_ltac.ltac_apply k ltac_args
	    | tbl :: tbls ->
	      let mp = Reification.export_table acc tbl tbl_data in
	      Plugin_utils.Use_ltac.pose "tbl" mp
		(fun var -> generate tbls (var :: acc))
	  in
	  generate tbls []
        with
          ReificationFailure trm ->
	    let pr = Pp.(   str "Failed to reify term '"
		         ++ Printer.pr_constr (Lazy.force trm)
                         ++ str "'.") in
	    Tacticals.New.tclZEROMSG pr
        | ParseFailure (trm, typ) ->
            let pr = Pp.(   str "Failed to parse term '"
		         ++ Printer.pr_constr trm
                         ++ str "' at type " ++ str typ ++ str ".") in
	    Tacticals.New.tclZEROMSG pr
      end
    ]
END

TACTIC EXTEND Reify_Lambda_Shell_reify_bind
  | ["reify_expr_bind" constr(name) tactic(k) "[[" constr(tbls) "]]" "[[" ne_constr_list(es) "]]" ] ->
    [ let tbls = Reification.parse_tables tbls in
      Proofview.Goal.enter begin fun gl ->
        Printf.eprintf "table length = %d\n" (List.length tbls) ;
	try
	  let (res,tbl_data) =
	    Reification.reify_all (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)
               tbls (List.map (fun e -> (name,e)) es)
	  in
	  let rec generate tbls acc =
	    match tbls with
	      [] ->
	      Reification.pose_each (List.map (fun x -> ("e",x)) res) (fun res ->
		let ltac_args =
		  List.map
		    Plugin_utils.Use_ltac.to_ltac_val
		    (List.rev_append acc res)
		in
		Plugin_utils.Use_ltac.ltac_apply k ltac_args)
	    | tbl :: tbls ->
	      let mp = Reification.export_table acc tbl tbl_data in
	      Plugin_utils.Use_ltac.pose "tbl" mp
		(fun var -> generate tbls (var :: acc))
	  in
	  generate tbls []
	with
	  ReificationFailure trm ->
	    let pr = Pp.(   (str "Failed to reify term '")
		         ++ (Printer.pr_constr (Lazy.force trm))
	                 ++ (str "'.")) in
            Tacticals.New.tclZEROMSG pr
        | ParseFailure (trm, typ) ->
            let pr = Pp.(   str "Failed to parse term '"
		         ++ Printer.pr_constr trm
                         ++ str "' at type " ++ str typ ++ str ".") in
	    Tacticals.New.tclZEROMSG pr
      end
    ]
END


(**
TACTIC EXTEND Reify_Lambda_Shell_poly_reify_constr
  | ["reify_poly_expr" constr(n) constr(typ) constr(name) tactic(k) "[[" constr(tbls) "]]" "[[" ne_constr_list(es) "]]" ] ->
    [ let n = Reification.nat_to_int n in
      let rec dup n =
        if n <= 0 then [] else typ :: dup (n-1)
      in
      let tbls = Reification.parse_tables tbls in
      Proofview.Goal.enter begin fun gl ->
	try
	  let (res,tbl_data) =
	    Reification.reify_all ~poly:(dup n) (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)
              tbls (List.map (fun e -> (name,e)) es)
	  in
	  let rec generate tbls acc =
	    match tbls with
	      [] ->
		let ltac_args =
		  List.map
		    Plugin_utils.Use_ltac.to_ltac_val
		    (List.rev_append acc res)
		in
		Plugin_utils.Use_ltac.ltac_apply k ltac_args
	    | tbl :: tbls ->
	      let mp = Reification.export_table acc tbl tbl_data in
	      Plugin_utils.Use_ltac.pose "tbl" mp
		(fun var -> generate tbls (var :: acc))
	  in
	  generate tbls []
        with
          ReificationFailure trm ->
	    let pr = Pp.(   (str "Failed to reify term '")
		         ++ (Printer.pr_constr (Lazy.force trm))
                         ++ (str "'.")) in
	    Tacticals.New.tclZEROMSG pr
      end
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Reify_Lemma
  | [ "Reify" "BuildLemma" "<" constr(typ) constr(term) constr(concl) ">"
        ident(name) ":" lconstr(lem) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (evm,[lem;typ;term;concl])   =
        Reification.ics ~env:env ~sigma:evm [lem;typ;term;concl] in
      let (evm,lem_type) = Typing.type_of env evm lem in
      try
        Reification.declare_syntax_lemma
          ~name:name ~type_fn:typ ~prem_fn:term ~concl_fn:concl
          env evm 0 lem_type
      with
        (ReificationFailure trm) ->
          Errors.errorlabstrm "Reify"
            Pp.(   str "Failed to reify term '"
		++ Printer.pr_constr (Lazy.force trm)
                ++ str "'.")
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Reify_Poly_Lemma
  | [ "Reify" "BuildPolyLemma" integer(pargs) "<" constr(typ) constr(term) constr(concl) ">"
        ident(name) ":" lconstr(lem) ] ->
    [ if pargs < 0 then
        Errors.errorlabstrm "Reify"
          Pp.(   str "Polymorphic lemmas can not have a negative number"
              ++ str " of polymorphic arguments")
      else
        let (evm,env) = Lemmas.get_current_context () in
        let (evm,[lem;typ;term;concl])   =
          Reification.ics ~env:env ~sigma:evm [lem;typ;term;concl] in
        let (evm,lem_type) = Typing.type_of env evm lem in
        try
          Reification.declare_syntax_lemma
            ~name:name ~type_fn:typ ~prem_fn:term ~concl_fn:concl
            env evm pargs lem_type
        with
          (ReificationFailure trm) ->
          Errors.errorlabstrm "Reify"
            Pp.(   str "Failed to reify term '"
		++ Printer.pr_constr (Lazy.force trm)
                ++ str "'.")
    ]
END
**)
