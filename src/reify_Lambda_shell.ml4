(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Reify_gen
open Plugin_utils

let contrib_name = "MirrorCore.Reify"

DECLARE PLUGIN "reify_Lambda_plugin"

module Std = Plugin_utils.Coqstd.Std
  (struct
    let contrib_name = contrib_name
   end)

let do_debug = false

let rec pr_constrs sep ks =
  match ks with
    [] -> Pp.(str) ""
  | [k] -> Printer.pr_constr k
  | k :: ks -> Pp.(Printer.pr_constr k ++ sep ++ pr_constrs sep ks)

let debug_constr s e =
  if do_debug then
    Pp.(msg_warning (  (str s) ++ (str ": ") ++ (Printer.pr_constr e)))
  else
    ()

let debug s =
  if do_debug then
    Pp.(msg_warning (  (str s)))
  else
    ()


module type REIFICATION =
sig
  type map_sort =
    SimpleMap
  | TypedMap
  | TypedMapAbs of Term.constr
  type map_type =
  { table_name : Term.constr
  ; table_elem_type : Term.constr
  ; table_elem_ctor : Term.constr
  ; table_scheme : map_sort
  }

  exception ReificationFailure of Term.constr Lazy.t

  type all_tables

  val parse_tables : Term.constr -> map_type list

  (** Tables **)
  val declare_table : Names.identifier -> Evd.evar_map -> Term.constr -> bool
  val declare_typed_table : Names.identifier -> Evd.evar_map -> Term.constr -> Term.constr -> bool
  val seed_table    : Term.constr -> int -> Term.constr -> bool
  val seed_typed_table    : Term.constr -> int -> Term.constr -> Term.constr -> bool

  (** Patterns **)
  val declare_pattern : Names.identifier -> Evd.evar_map -> Term.constr -> unit
  val add_pattern     : Term.constr -> Term.constr (* rpattern *) -> Term.constr -> unit
  val print_patterns  : Term.constr -> Pp.std_ppcmds

  (** Functions **)
  val declare_syntax : Names.identifier -> Evd.evar_map -> Term.constr (* command *) -> unit

  (** Reification **)
  val reify     : Environ.env -> Evd.evar_map -> map_type list (* tables *) ->
    Term.constr -> Term.constr -> Term.constr * all_tables
  val reify_all : Environ.env -> Evd.evar_map -> map_type list (* tables *) ->
    (Term.constr * Term.constr) list -> Term.constr list * all_tables
  val export_table : Term.constr list -> map_type -> all_tables -> Term.constr

  val reify_lemma : type_fn:Term.constr -> prem_fn:Term.constr -> concl_fn:Term.constr ->
    Environ.env -> Evd.evar_map -> Term.types -> Term.constr
  val declare_syntax_lemma :
    name:Names.identifier ->
    type_fn:Term.constr -> prem_fn:Term.constr -> concl_fn:Term.constr ->
    Environ.env -> Evd.evar_map -> Term.constr -> unit

  val pose_each : (string * Term.constr) list -> (Term.constr list -> unit Proofview.tactic) -> unit Proofview.tactic

  val ic : env:Environ.env -> sigma:Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * Term.constr
end

module Reification : REIFICATION =
struct
  module Cmap = Map.Make
    (struct
      type t = Term.constr
      let compare = Term.constr_ord
     end)

  module IntMap = Map.Make
    (struct
      type t = int
      let compare = Int.compare
    end)

  type map_sort =
    SimpleMap
  | TypedMap
  | TypedMapAbs of Term.constr
  type map_type =
  { table_name : Term.constr
  ; table_elem_type : Term.constr
  ; table_elem_ctor : Term.constr
  ; table_scheme : map_sort
  }

  type 'a environment =
  { mappings : 'a Cmap.t
  ; next     : int
  }

  type reify_env =
  { env : Environ.env
  ; evm : Evd.evar_map
  ; bindings : bool list
  ; typed_tables : (int * Term.constr) environment Cmap.t ref
  }

  type all_tables =
  { tables : (int * Term.constr) environment Cmap.t
  }

  type lazy_term =
  | Term of Term.constr
  | App of Term.constr * Term.constr array * int

  let get_by_conversion renv (tbl : 'a environment) (target : Term.constr) : 'a option =
    let unifies = Reductionops.is_conv renv.env renv.evm target in
    Cmap.fold (fun k v a ->
      match a with
	None -> if unifies k then Some v else None
      | Some k -> Some k) tbl.mappings None


  exception ReificationFailure of (Term.constr Lazy.t)

  (** [reifier]s are the actual functions that get run **)
  type 'a reifier =
    reify_env -> 'a

  (** [rule]s implement the pattern feature **)
  type 'a rule =
    ((int,int,reify_env) Term_match.pattern) *
      ('a -> (int, Term.constr) Hashtbl.t -> Term.constr reifier)

  let empty_array : Term.constr array = [| |]

  let get_term (trm : lazy_term) =
    match trm with
      Term trm -> trm
    | App (trm,args,from) ->
      if from = -1 then trm
      else if from = Array.length args then
	Term.mkApp (trm, args)
      else Term.mkApp (trm, Array.sub args 0 (from+1))

  let reifier_bind (c : 'a reifier) (k : 'a -> 'b reifier) : 'b reifier =
    fun gl ->
      k (c gl) gl

  let reifier_fail (t : Term.constr) : 'a reifier =
    fun gl -> raise (ReificationFailure (lazy t))

  let reifier_fail_lazy (t : lazy_term) : 'a reifier =
    fun gl -> raise (ReificationFailure (lazy (get_term t)))

  let reifier_try (c : 'a reifier) (x : 'a reifier) : 'a reifier =
    fun gl ->
      try c gl
      with ReificationFailure _ -> x gl

  let reifier_ret (value : 'a) : 'a reifier =
    fun _ -> value
  let reifier_get_env : reify_env reifier =
    fun e -> e

  let reifier_local (f : reify_env -> reify_env) (c : 'a reifier) : 'a reifier =
    fun gl -> c (f gl)

  let reifier_under_binder (b : bool) (t : Term.constr) (c : 'a reifier)
  : 'a reifier =
    fun gl -> c { gl with
                  bindings = b :: gl.bindings
                ; env = Environ.push_rel (Names.Anonymous, None, t) gl.env }

  let reifier_run (c : 'a reifier) (gl : reify_env) = c gl

  type rpattern =
  | RIgnore
  | RHasType of Term.constr * rpattern
  | RConst
  | RGet   of int * rpattern
  | RApp   of rpattern * rpattern
  | RPi    of rpattern * rpattern
  | RLam   of rpattern * rpattern
  | RImpl  of rpattern * rpattern
  | RExact of Term.constr

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

  let ptrn_tree_add (type a) (p : rpattern) (v : a option -> a) (t : a ptrn_tree) =
    match p with
    | RApp (l,r) ->
      (* NOTE: This is conservative, if ends in an open pattern
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

  (** Get the head symbol **)
  let rec app_full trm acc =
    match Term.kind_of_term trm with
      Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)

  let pattern_mod = ["MirrorCore";"Reify";"Patterns"]

  let decl_constant ?typ (na : Names.identifier) evm (c : Term.constr) =
    (** TODO: This looks weird... **)
    let (evm, _) = Typing.type_of (Global.env ()) evm c in
    let vars = Universes.universes_of_constr c in
    let ctx = Universes.restrict_universe_context (Univ.ContextSet.of_context (Evd.universe_context evm)) vars in
    Declare.(Term.mkConst(declare_constant na
			    (Entries.(DefinitionEntry
					(definition_entry ~opaque:false ~univs:(Univ.ContextSet.to_context ctx) c))

					(*

					{ const_entry_body = Future.from_val c;
					  const_entry_secctx = None;
					  const_entry_type = typ;
					  const_entry_opaque = false }) *),
			     Decl_kinds.(IsDefinition Definition))))

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
	    Pp.(msg_warning (   (str "Table '")
			     ++ (Printer.pr_constr tbl_name)
			     ++ (str (Printf.sprintf "' already contains a mapping for %d.\n" k))
	                     ++ (str "This mapping is incompatible with the given mapping.")))
	  in false
      with
	Not_found ->
	  let _ = Pp.(msg_warning (   (str "Table '")
				   ++ (Printer.pr_constr tbl_name)
				   ++ (str "' does not exist."))) in
	  false


    let declare_table (ls : Term.constr) (kt : key_type) =
      if Cmap.mem ls !the_seed_table then
	let _ =
	  Pp.(msg_warning (   (str "Table '")
			   ++ (Printer.pr_constr ls)
			   ++ (str "' already exists.")))
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
	  Pp.(msg_warning (   (str "Table '")
			   ++ (Printer.pr_constr ls)
			   ++ (str "' already exists.")))
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
    (** State **)
    let pattern_table : ((reify_env rule) list) ptrn_tree Cmap.t ref =
      ref Cmap.empty

    (** Freezing and thawing of state (for backtracking) **)
    let _ =
      Summary.(declare_summary "reify-lambda-shell-pattern-table"
	{ freeze_function = (fun _ -> !pattern_table)
	; unfreeze_function = (fun pt -> pattern_table := pt)
	; init_function = (fun () -> pattern_table := Cmap.empty) })

    let ptrn_exact    = Std.resolve_symbol pattern_mod "RExact"
    let ptrn_const    = Std.resolve_symbol pattern_mod "RConst"
    let ptrn_ignore   = Std.resolve_symbol pattern_mod "RIgnore"
    let ptrn_get      = Std.resolve_symbol pattern_mod "RGet"
    let ptrn_app      = Std.resolve_symbol pattern_mod "RApp"
    let ptrn_pi       = Std.resolve_symbol pattern_mod "RPi"
    let ptrn_lam      = Std.resolve_symbol pattern_mod "RLam"
    let ptrn_impl     = Std.resolve_symbol pattern_mod "RImpl"
    let ptrn_has_type = Std.resolve_symbol pattern_mod "RHasType"

    let action_function  = Std.resolve_symbol pattern_mod "function"
    let action_id        = Std.resolve_symbol pattern_mod "id"
    let action_associate = Std.resolve_symbol pattern_mod "associate"
    let action_store     = Std.resolve_symbol pattern_mod "store"

    let into_rpattern =
      let rec into_rpattern (ptrn : Term.constr) : rpattern =
	Term_match.(matches ()
	  [ (Glob_no_univ ptrn_ignore,
	     fun _ _ -> RIgnore)
	  ; (apps (Glob_no_univ ptrn_get) [get 0; get 1],
	     fun _ s ->
	       let num  = Hashtbl.find s 0 in
	       let next = Hashtbl.find s 1 in
	       RGet (Std.Nat.of_nat num, into_rpattern next))
	  ; (apps (Glob_no_univ ptrn_exact) [Ignore; get 0],
	     fun _ s ->
	       let t = Hashtbl.find s 0 in
	       RExact t)
	  ; (apps (Glob_no_univ ptrn_app) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RApp (into_rpattern f, into_rpattern x))
	  ; (apps (Glob_no_univ ptrn_impl) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RImpl (into_rpattern f, into_rpattern x))
	  ; (apps (Glob_no_univ ptrn_pi) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RPi (into_rpattern f, into_rpattern x))
	  ; (apps (Glob_no_univ ptrn_lam) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RLam (into_rpattern f, into_rpattern x))
	  ; (Glob_no_univ ptrn_const,
	     fun _ _ -> RConst)
	  ; (apps (Glob_no_univ ptrn_has_type) [get 0; get 1],
	     fun _ s ->
	       let t = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RHasType (t, into_rpattern x))
	  ]
	  ptrn)
      in
      into_rpattern

    let compile_pattern (effects : (int, (int, Term.constr) Hashtbl.t -> reify_env -> reify_env) Hashtbl.t) =
      let fresh = ref (-1) in
      let rec compile_pattern (p : rpattern)
	  (effect : ((int, Term.constr) Hashtbl.t -> reify_env -> reify_env) option)
	  : (int,int,reify_env) Term_match.pattern * int list =
	match p with
	  RExact g ->
	    (Term_match.EGlob_no_univ g, [])
	| RIgnore -> (Term_match.Ignore, [])
	| RGet (i, p) ->
	  let (p,us) = compile_pattern p effect in
	  let _ =
	    match effect with
	      None -> ()
	    | Some eft -> Hashtbl.add effects i eft
	  in
	  (Term_match.As (p, i), i :: us)
	| RApp (p1, p2) ->
	  let (p1,l1) = compile_pattern p1 effect in
	  let (p2,l2) = compile_pattern p2 effect in
	  (Term_match.App (p1,p2), l1 @ l2)
	| RConst ->
	  let filter _ =
	    let rec filter trm =
	    (** TODO: This does not handle polymorphic types right now **)
	      let (f, args) = app_full trm [] in
	      Term.isConstruct f && List.for_all filter args
	    in
	    filter
	  in
	  (Term_match.Filter (filter, Term_match.Ignore),[])
	| RImpl (p1, p2) ->
	  let (p1,l1) = compile_pattern p1 effect in
	  let fresh =
	    let r = !fresh in
	    fresh := r - 1 ;
	    r
	  in
	  let new_effect =
	    match effect with
	      None ->
		fun s x ->
		  let nbindings = false :: x.bindings in
		  let nenv =
		    Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		      x.env
		  in
		  { x with bindings = nbindings ; env = nenv }
	    | Some eft ->
	      fun s x ->
		let x = eft s x in
		let nbindings = false :: x.bindings in
		let nenv =
		  Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		    x.env
		in
		{ x with bindings = nbindings ; env = nenv }
	  in
	  let (p2,l2) = compile_pattern p2 (Some new_effect) in
	  (Term_match.Impl (Term_match.As (p1,fresh),p2), l1 @ l2)
	| RPi (p1, p2) ->
	  let (p1,l1) = compile_pattern p1 effect in
	  let fresh =
	    let r = !fresh in
	    fresh := r - 1 ;
	    r
	  in
	  let new_effect =
	    match effect with
	      None ->
		fun s x ->
		  let nbindings = true :: x.bindings in
		  let nenv =
		    Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		      x.env
		  in
		  { x with bindings = nbindings ; env = nenv }
	    | Some eft ->
	      fun s x ->
		let x = eft s x in
		let nbindings = true :: x.bindings in
		let nenv =
		  Environ.push_rel (Names.Anonymous, None, Hashtbl.find s fresh)
		    x.env
		in
		{ x with bindings = nbindings ; env = nenv }
	  in
	  let (p2,l2) = compile_pattern p2 (Some new_effect) in
	  (Term_match.Pi (Term_match.As (p1,fresh),p2), l1 @ l2)
	| RHasType (t,p) ->
	  let (p,l) = compile_pattern p effect in
	  (Term_match.Filter
	     ((fun env trm ->
(*               let start_time = Sys.time () in *)
	       let (_,ty) = Typing.type_of env.env env.evm trm in
(*
               let end_time = Sys.time () in
               Pp.(msg_info (str "type checking time: " ++ real (end_time -. start_time) ++ fnl ())) ; *)
	       Term.eq_constr ty t), p), l)
        | RLam (a,b) -> assert false
      in
      compile_pattern

    type action =
      Func of Term.constr
    | Id
    | Associate of Term.constr (* table name *) * Term.constr (* key *)
    | Store of Term.constr (* table name *)

    let parse_action : Term.constr -> action option =
      Term_match.(matches ()
	[ (App (Glob_no_univ action_function, get 0),
	   fun _ s -> Some (Func (Hashtbl.find s 0)))
	; (App (Glob_no_univ action_id, Ignore),
	   fun _ s -> Some Id)
	; (Ignore, fun _ _ -> None)
	])

    let compile_template
	(effects : (int, (int, Term.constr) Hashtbl.t -> reify_env -> reify_env) Hashtbl.t)
	(reify_term : Term.constr -> lazy_term -> Term.constr reifier) =
      let rec compile_template (tmp : Term.constr) (at : int)
      : Term.constr list -> reify_env -> (int, Term.constr) Hashtbl.t ->
	Term.constr reifier =
	match Term.kind_of_term tmp with
	  Term.Lambda (_, typ, body) ->
	    begin
	      match parse_action typ with
		None ->
		let _ =
		  Pp.(msgerrnl (    (str "Failed to parse action from lambda. Got term: \n")
				 ++ (Printer.pr_constr typ)))
		in
		fun ls _ _ -> reifier_ret (Vars.substnl ls 0 tmp)
	      | Some act ->
		let rest = compile_template body (at + 1) in
		let eft =
		  try
		    Hashtbl.find effects at
		  with
		    Not_found -> (fun _ x -> x)
		in
		match act with
		| Func f ->
		  fun vals gl s ->
		    let cur_val = Hashtbl.find s at in
		    let rval = reifier_run (reifier_local (eft s) (reify_term f (Term cur_val))) gl in
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
		| Associate (tbl_name, key) ->
		  assert false (*
		  fun vals gl s ->
		    let cur_val = Hashtbl.find s at in
		    let get_key =
		      match Term.kind_of_term key with
			Term.Rel i ->
			  begin
			    try
			      List.nth vals (i-1)
			    with
			      Failure _ -> raise (Failure (Printf.sprintf "Associate %d" (i-1)))
			    | Invalid_argument _ -> assert false
			  end
		      | _ -> key
		    in
		    let tbl =
		      try
			Cmap.find tbl_name gl.tables
		      with
			Not_found -> raise (Failure "Accessing unknown map")
		    in
		    (** TODO **)
		    rest (Lazy.force Std.Unit.tt :: vals) gl s
			       *)
		| Store tbl ->
		  assert false
	    end
	| _ ->
	  fun ls _ _ -> reifier_ret (Vars.substnl ls 0 tmp)
      in compile_template

    let extend trm key rul =
      try
	let objs = Cmap.find trm !pattern_table in
        let updated = ptrn_tree_add key (function None -> [rul]
                                                | Some xs -> rul :: xs) objs in
	pattern_table := Cmap.add trm updated !pattern_table
      with
      | Not_found -> assert false

    let add_pattern (dispatch : Term.constr -> lazy_term -> 'a reifier)
	(name : Term.constr) (ptrn : Term.constr) (template : Term.constr)
	: unit =
      try
	let effects = Hashtbl.create 1 in
        let rptrn = into_rpattern ptrn in
	let (ptrn, occs) = compile_pattern effects rptrn None in
	let action = compile_template effects dispatch template 0 [] in
	extend name rptrn (ptrn, action)
      with
	Term_match.Match_failure -> raise (Failure "match failed, please report")

    let pr_paren a =
      Pp.(str "(" ++ a ++ str ")")

    let rec print_rule ptrn =
      Term_match.(Pp.(
	match ptrn with
	  Ignore -> str "<any>"
	| As (a,i) -> pr_paren (pr_paren (print_rule a) ++ str " as " ++ int i)
	| App (l,r) -> pr_paren (print_rule l ++ str " @ " ++ print_rule r)
	| Impl (l,r) -> pr_paren (print_rule l ++ str " -> " ++ print_rule r)
	| Glob g | Glob_no_univ g -> Printer.pr_constr (Lazy.force g)
	| EGlob g | EGlob_no_univ g -> Printer.pr_constr g
	| Lam (a,b,c) -> pr_paren (str "fun " ++ pr_paren (int a ++ str " : " ++ print_rule b) ++ str " => " ++ print_rule c)
	| Ref i -> str "<" ++ int i ++ str ">"
	| Choice ls -> pr_sequence print_rule ls
	| Pi (a,b) -> pr_paren (str "Pi " ++ print_rule a ++ str " . " ++ print_rule b)
	| Filter (_,a) -> pr_paren (str "Filter - " ++ print_rule a)))

    let apps = List.fold_right Pp.(++)

    let print_patterns (name : Term.constr) : Pp.std_ppcmds =
      try
	let vals = Cmap.find name !pattern_table in
        Pp.pr_vertical_list (fun (x,_) -> print_rule x)
          (List.flatten (List.map snd (IntMap.bindings vals.if_app) @
                         List.map snd (Cmap.bindings vals.if_has_type) @
                         List.map snd (Cmap.bindings vals.if_exact) @
                         [vals.otherwise]))
      with Not_found ->
        Pp.(msg_warning (   (str "Unknown pattern table '")
  		         ++ (Printer.pr_constr name)
                         ++ (str "'."))) ;
        Pp.mt ()

    let run_ptrn_tree tr trm gl =
      match trm with
        Term trm ->
        begin
          try
            Term_match.matches gl
              (Cmap.find trm tr.if_exact)
              trm gl
          with Not_found | Term_match.Match_failure ->
            try
              match Term.kind_of_term trm with
              | Term.App (_,args) ->
                Term_match.matches gl
                  (IntMap.find (Array.length args) tr.if_app)
                  trm gl
              | _ -> raise Not_found
            with Not_found | Term_match.Match_failure ->
              try
                if not (Cmap.is_empty tr.if_has_type) then
                  (* get the type *)
                  let (_,ty) = Typing.type_of gl.env gl.evm trm in
                  Term_match.matches gl
                    (Cmap.find ty tr.if_has_type) trm gl
                else raise Not_found
              with Not_found | Term_match.Match_failure ->
                Term_match.matches gl tr.otherwise trm gl
        end
      | App (trm, args, from) ->
        begin
          assert false
        end


    let reify_patterns (i : Term.constr) trm
    : Term.constr reifier =
      fun gl ->
(*        let start_time = Sys.time () in *)
	try
          let result = run_ptrn_tree (Cmap.find i !pattern_table) trm gl in
(*          let end_time = Sys.time () in
          Pp.(msg_info (str "reify_pattern time: " ++ real (end_time -. start_time) ++ fnl ())) ; *)
          result
	with
        | Term_match.Match_failure ->
          begin
(*            let end_time = Sys.time () in
            Pp.(msg_info (str "backtracking...time:" ++ real (end_time -. start_time) ++ fnl ())) ; *)
	    reifier_fail_lazy trm gl
          end

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

  end

  module Syntax =
  struct
    type syntax_data =
      { reify : lazy_term -> Term.constr reifier
      ; result_type : Term.constr
      }
    let reify_table : syntax_data Cmap.t ref =
      ref Cmap.empty

    (** Freezing and thawing of state (for backtracking) **)
    let _ =
      Summary.(declare_summary "reify-lambda-shell-syntax-table"
	{ freeze_function   = (fun _ -> !reify_table);
	  unfreeze_function = (fun pt -> reify_table := pt);
	  init_function     = (fun () -> reify_table := Cmap.empty) })

    type command =
    | Patterns of Term.constr
    | Call of Term.constr
    | App of Term.constr
    | Abs of Term.constr * Term.constr
    | Var of Term.constr
    | Map of Term.constr * command
    | First of command list
    | Table of Term.constr * Term.constr
    | TypedTable of Term.constr * Term.constr * Term.constr

    let reify_term (name : Term.constr) =
      let reifier = Cmap.find name !reify_table in
      reifier.reify

    let reify_type (name : Term.constr) =
      let reifier = Cmap.find name !reify_table in
      reifier.result_type

    let cmd_patterns = Std.resolve_symbol pattern_mod "CPatterns"
    let cmd_call     = Std.resolve_symbol pattern_mod "CCall"
    let cmd_app      = Std.resolve_symbol pattern_mod "CApp"
    let cmd_abs      = Std.resolve_symbol pattern_mod "CAbs"
    let cmd_var      = Std.resolve_symbol pattern_mod "CVar"
    let cmd_table    = Std.resolve_symbol pattern_mod "CTable"
    let cmd_typed_table = Std.resolve_symbol pattern_mod "CTypedTable"
    let cmd_map      = Std.resolve_symbol pattern_mod "CMap"
    let cmd_first    = Std.resolve_symbol pattern_mod "CFirst"


    let rec parse_commands cmd =
      Term_match.(matches ()
	[ (apps (Glob_no_univ Std.List.c_nil) [Ignore],
	   fun _ s -> [])
	; (apps (Glob_no_univ Std.List.c_cons) [Ignore(*T*);get 0(*cmd*);get 1(*cmds*)],
	   fun _ s ->
	     let (_,a) = parse_command (Hashtbl.find s 0) in
	     let b = parse_commands (Hashtbl.find s 1) in
	     (a :: b))
	]
	cmd)
    and parse_command cmd : Term.constr * command =
      Term_match.(matches ()
	[ (apps (Glob_no_univ cmd_patterns) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Patterns (Hashtbl.find s 0)))
	; (apps (Glob_no_univ cmd_call) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Call (Hashtbl.find s 0)))
	; (apps (Glob_no_univ cmd_app) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,App (Hashtbl.find s 0)))
	; (apps (Glob_no_univ cmd_var) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Var (Hashtbl.find s 0)))
	; (apps (Glob_no_univ cmd_abs) [get ~-1(*T*);get 1;get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Abs (Hashtbl.find s 1,Hashtbl.find s 0)))
	; (apps (Glob_no_univ cmd_table) [get ~-1(*T*);Ignore;get 0;get 1],
	   fun _ s -> (Hashtbl.find s ~-1,Table (Hashtbl.find s 0, Hashtbl.find s 1)))
	; (apps (Glob_no_univ cmd_typed_table)
	     [get ~-1(*T*);Ignore(*K*);get 0(*Ty*);
	      get 1(*tbl*);get 2(*ctor*)],
	   fun _ s ->
	     (Hashtbl.find s ~-1,TypedTable (Hashtbl.find s 1, Hashtbl.find s 0, Hashtbl.find s 2)))
	; (apps (Glob_no_univ cmd_map)
	     [get ~-1(*T*);Ignore;get 1(*F*);get 0(*cmd*)],
	   fun _ s ->
	     let (_,c) = parse_command (Hashtbl.find s 0) in
	     (Hashtbl.find s ~-1,Map (Hashtbl.find s 1, c)))
	; (apps (Glob_no_univ cmd_first)
	     [get ~-1(*T*);get 0(*cmds*)],
	   fun _ s ->
	     (Hashtbl.find s ~-1,First (parse_commands (Hashtbl.find s 0))))
	]
	cmd)

    let find =
      let rec find ls i acc =
	match ls with
          [] -> assert false
        | l :: ls ->
	  if i = 0 then
            (assert l ; acc)
          else
	    find ls (i - 1) (if l then acc + 1 else acc)
      in
      fun ls i -> find ls i 0

    let compile_command (ls : command)
    : lazy_term -> Term.constr reifier =
      let top = ref (fun _ _ -> assert false) in
      let rec compile_commands (ls : command list)
      : lazy_term -> Term.constr reifier =
	  match ls with
	    [] ->
	      fun trm gl ->
		let trm = get_term trm in
		(* HERE *)
		Pp.(msg_warning (   (str "backtracking on '")
				 ++ (Printer.pr_constr trm)
				 ++ (str "'\n"))) ;
		raise (ReificationFailure (lazy trm))
	  | l :: ls ->
	    let k = compile_commands ls in
	    let l = compile_command l in
	    fun t gl -> reifier_try (l t) (k t) gl
      and compile_command (l : command)
      : lazy_term -> Term.constr reifier =
	match l with
	| Patterns i ->
	  fun trm gl ->
	  begin
(*
	    let _ = debug_constr "trying patterns" (get_term trm) in
	    try
 *)
	      Patterns.reify_patterns i trm gl
(*
	    with
	      e -> (debug "failed!" ; raise e)
 *)
	  end
	| Call t ->
	  fun trm gl ->
	    reify_term t trm gl
	| Abs (ty_name,ctor) ->
	  fun trm gl ->
	    begin
	      match Term.kind_of_term (get_term trm) with
		Term.Lambda (name, lhs, rhs) ->
		  let ty = reify_term ty_name (Term lhs) gl in
		  let new_gl =
		    { gl with
		      env = Environ.push_rel (name, None, lhs) gl.env
		    ; bindings = true :: gl.bindings
		    }
		  in
		  let body = reifier_run (!top (Term rhs)) new_gl in
		  Term.mkApp (ctor, [| ty ; body |])
	      | _ -> reifier_fail_lazy trm gl
	    end
	| Var ctor ->
	  fun trm gl ->
	    begin
	      match Term.kind_of_term (get_term trm) with
		Term.Rel i ->
		  let idx = find gl.bindings (i-1) in
		  Term.mkApp (ctor, [| Std.Nat.to_nat idx |])
	      | _ -> reifier_fail_lazy trm gl
	    end
	| App ctor ->
	  fun trm gl ->
	    begin
	      try
		Term_match.(matches gl
			      [ (App (get 0, get 1),
				 fun gl s ->
				   let r = !top in
				   let f = r (Term (Hashtbl.find s 0)) gl in
				   let x = r (Term (Hashtbl.find s 1)) gl in
				   Term.mkApp (ctor, [| f ; x |]))
			      ])
		  (get_term trm)
	      with
		Term_match.Match_failure -> reifier_fail_lazy trm gl
	    end
	| Table (tbl_name,ctor) ->
	  begin
	    let build x =
	      Term.mkApp (ctor, [| Std.Positive.to_positive x |])
	    in
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
			    (   (str "Implicitly adding table '")
			     ++ (Printer.pr_constr tbl_name)
			     ++ (str "'. This will not be returned.\n")
			     ++ (str "(available tables are: ")
			     ++ (pr_constrs (str " , ") all_tables)
			     ++ (str ")")))
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
	| TypedTable (tbl_name, type_name, ctor) ->
	  begin
	    let build x =
	      Term.mkApp (ctor, [| Std.Positive.to_positive x |])
	    in
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
			    (   (str "Implicitly adding table '")
			     ++ (Printer.pr_constr tbl_name)
			     ++ (str "'. This will not be returned.\n")
			     ++ (str "(available tables are: ")
			     ++ (pr_constrs (str " , ") all_tables)
			     ++ (str ")")))
		    in
		    { mappings = Cmap.empty
		    ; next = 1 }
	      in
	      let full_term = get_term trm in
	      let (_,type_of) = Typing.type_of renv.env renv.evm full_term in
	      let rtyp = reify_term type_name (Term type_of) renv in
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
	  let cmd = compile_commands [n] in
	  begin
	    fun trm ->
	      reifier_bind (cmd trm) (fun t -> reifier_ret (Term.mkApp (f, [| t |])))
	  end
	| First cs ->
	  compile_commands cs
      in
      let result = compile_command ls in
      top := result ;
      result

    let add_syntax (name : Term.constr) (typ : Term.constr) (cmds : Term.constr) : unit =
      let (_,program) = parse_command cmds in
      let meta_reifier =
        { reify = compile_command program
        ; result_type = typ }
      in
      let _ =
	if Cmap.mem name !reify_table then
	  Pp.(msg_warning (   (str "Redeclaring syntax '")
			   ++ (Printer.pr_constr name)
			   ++ (str "'")))
	else ()
      in
      reify_table := Cmap.add name meta_reifier !reify_table

    let syntax_object : Term.constr * Term.constr * Term.constr -> Libobject.obj =
      Libobject.(declare_object
	{ (default_object "REIFY_SYNTAX") with
	  cache_function = (fun (_,_) -> ())
	; load_function = (fun i ((b,n),value) ->
	  let (name, typ, cmds) = value in
	  add_syntax name typ cmds)
	})

    let declare_syntax (name : Names.identifier) evm
	(cmd : Term.constr) : unit =
      let (typ,_program) = parse_command cmd in
      let _meta_reifier = compile_command _program in
      let obj = decl_constant name evm typ in
      let _ = Lib.add_anonymous_leaf (syntax_object (obj,typ,cmd)) in
      add_syntax obj typ cmd
  end

  let initial_env (env : Environ.env) (evar_map : Evd.evar_map) (tbls : map_type list) =
    { env = env
    ; evm = evar_map
    ; bindings = []
    ; typed_tables = ref !Tables.the_seed_table }

  let reify (env : Environ.env) (evm : Evd.evar_map) tbls (name : Term.constr) trm =
    let env = initial_env env evm tbls in
    let result = Syntax.reify_term name (Term trm) env in
    (result, { tables = !(env.typed_tables) })

  let reify_all (env : Environ.env) (evm : Evd.evar_map) tbls ns_e =
    let start_time = Sys.time () in
    let st = initial_env env evm tbls in
    let result =
      List.map (fun (ns,e) -> Syntax.reify_term ns (Term e) st) ns_e
    in
    let end_time = Sys.time () in
    Pp.(msg_info (str "Total time = " ++ real (end_time -. start_time) ++ fnl ())) ;
    (result, { tables = !(st.typed_tables) })

  let lemma_mod = ["MirrorCore";"Lemma"]

  let reify_lemma
      ~type_fn:typ_rule ~prem_fn:prem_rule ~concl_fn:concl_rule env evm pred =
    let build_lemma = Std.resolve_symbol lemma_mod "Build_lemma" in
    let finish alls prems pred =
      let ty = Syntax.reify_type typ_rule in
      let pr = Syntax.reify_type prem_rule in
      let co = Syntax.reify_type concl_rule in
      reifier_ret
        (Term.mkApp (Lazy.force build_lemma,
                     [| ty ; pr ; co
                      ; Std.List.to_list ty alls
                      ; Std.List.to_list pr (List.rev prems)
                      ; pred |]))
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
                    reifier_under_binder false t
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
                  reifier_under_binder true t (get_foralls (ty :: alls) b)))
        ; (Term_match.Ignore,
           fun _ _ -> get_prems alls [] pred)
        ]
        pred
    in
    reifier_run (get_foralls [] pred)
      (initial_env env evm [])

  let declare_syntax_lemma
    ~name:name ~type_fn:typ_rule ~prem_fn:prem_rule ~concl_fn:concl_rule
    env evm pred =
    let body =
      try
        reify_lemma ~type_fn:typ_rule ~prem_fn:prem_rule ~concl_fn:concl_rule
          env evm pred
      with
        Not_found ->
        assert false
    in
    let _ = decl_constant name evm body in
    ()

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

  let table_type = Std.resolve_symbol pattern_mod "table"
  let table_value = Std.resolve_symbol pattern_mod "a_table"
  let typed_table_type = Std.resolve_symbol pattern_mod "typed_table"
  let typed_table_value = Std.resolve_symbol pattern_mod "a_typed_table"

  let new_table
      : Term.constr * Tables.key_type -> Libobject.obj =
    Libobject.(declare_object
		 { (default_object "REIFY_NEW_TABLE") with
		   cache_function = (fun (_,_) ->
		     (** TODO: I don't know what to do here. **)
		     ())
		 ; load_function = fun i (obj_name,value) ->
		     (** TODO: What do I do about [i] and [obj_name]? **)
		     let (name,typ) = value in
		     if Tables.declare_table name typ then
		       ()
		     else
		       Printf.fprintf stderr "error declaring table"
		 })


  let new_table_entry
      : Term.constr * int * (Term.constr * Term.constr) -> Libobject.obj =
    Libobject.(declare_object
		 { (default_object "REIFY_NEW_TABLE_ENTRY") with
		   cache_function = (fun (_,_) ->
		     (** TODO: I don't know what to do here. **)
		     ())
		 ; load_function = fun i (obj_name,value) ->
		     (** TODO: What do I do about [i] and [obj_name]? **)
		     let (tbl_name, key, (ty,value)) = value in
		     if Tables.seed_table tbl_name key ty value then
		       ()
		     else
		       Printf.fprintf stderr "non-existant table"
		 })


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
      false

  let seed_typed_table name key ty value =
    if Tables.seed_table name key ty value then
      let _ =
	Lib.add_anonymous_leaf (new_table_entry (name, key, (ty, value)))
      in true
    else
      false


  let pattern_table_object : Term.constr -> Libobject.obj =
    Libobject.(declare_object
		 { (default_object "REIFY_NEW_PATTERNS") with
		   cache_function = (fun (_,_) ->
		     (** TODO: I don't know what to do here. **)
		     ())
		 ; load_function = fun i (obj_name,value) ->
		       (** TODO: What do I do about [i] and [obj_name]? **)
		     Patterns.declare_pattern value
		 })

  let a_pattern = Std.resolve_symbol pattern_mod "a_pattern"

  let declare_pattern (name : Names.identifier) evd (value : Term.constr) =
    let obj = decl_constant name evd (Term.mkApp (Lazy.force a_pattern, [| value |])) in
    let _ = Lib.add_anonymous_leaf (pattern_table_object obj) in
    Patterns.declare_pattern obj

  let print_patterns = Patterns.print_patterns

  let new_pattern_object
      : Term.constr * Term.constr * Term.constr -> Libobject.obj =
    Libobject.(declare_object
		 { (default_object "REIFY_ADD_PATTERN") with
		   cache_function = (fun (_,_) ->
		     (** TODO: I don't know what to do here. **)
		     ())
		 ; load_function = fun i (obj_name,value) ->
		     (** TODO: What do I do about [i] and [obj_name]? **)
		     let (name, ptrn, template) = value in
		     Patterns.add_pattern Syntax.reify_term name ptrn template
		 })

  let add_pattern (name : Term.constr)
      (ptrn : Term.constr) (template : Term.constr) : unit =
    let _ = Patterns.add_pattern Syntax.reify_term name ptrn template in
    Lib.add_anonymous_leaf (new_pattern_object (name, ptrn, template))

  let declare_syntax = Syntax.declare_syntax

  let mk_var_map = Std.resolve_symbol pattern_mod "mk_var_map"
  let mk_dvar_map = Std.resolve_symbol pattern_mod "mk_dvar_map"
  let mk_dvar_map_abs = Std.resolve_symbol pattern_mod "mk_dvar_map_abs"

  let parse_table (trm : Term.constr) : map_type =
    Term_match.(matches ()
		  [(apps (Glob_no_univ mk_var_map) [Ignore;Ignore;get 2;get 0;get 1],
		    fun _ s -> { table_name = Hashtbl.find s 0
			       ; table_elem_type = Hashtbl.find s 2
			       ; table_elem_ctor = Hashtbl.find s 1
			       ; table_scheme = SimpleMap })
		  ;(apps (Glob_no_univ mk_dvar_map) [Ignore;Ignore;get 2;Ignore;
					      get 0;get 1],
		    fun _ s -> { table_name = Hashtbl.find s 0
			       ; table_elem_type = Hashtbl.find s 2
			       ; table_elem_ctor = Hashtbl.find s 1
			       ; table_scheme = TypedMap })
		  ;(apps (Glob_no_univ mk_dvar_map_abs) [Ignore;Ignore;get 2;get 3;
						  Ignore;get 0;get 1],
		    fun _ s ->
		      { table_name = Hashtbl.find s 0
		      ; table_elem_type = Hashtbl.find s 2
		      ; table_elem_ctor = Hashtbl.find s 1
		      ; table_scheme = TypedMapAbs (Hashtbl.find s 3) })
		  ]) trm

  let rec parse_tables (tbls : Term.constr) : map_type list =
    Term_match.(matches ()
		  [(Lam (0,get 0,get 1),
		    fun _ s ->
		         parse_table (Hashtbl.find s 0)
		      :: parse_tables (Hashtbl.find s 1))
		  ;(Ignore, fun _ s -> [])
		  ]) tbls


  let rec pose_each (ls : (string * Term.constr) list) (k : Term.constr list -> 'a) : 'a =
    match ls with
      [] -> k []
    | (s,trm) :: ls ->
       Plugin_utils.Use_ltac.pose s trm (fun var -> pose_each ls (fun vs -> k (var :: vs)))

  let ic ~env ~sigma c =
(*    let env =
      match env with
      | None -> Global.env()
      | Some x -> x
    in
    let sigma =
      match sigma with
      | None -> Evd.empty
      | Some x -> x
    in
*)
    Constrintern.interp_open_constr env sigma c

end

VERNAC COMMAND EXTEND Reify_Lambda_Shell_add_lang
  | [ "Reify" "Declare" "Syntax" ident(name) ":=" lconstr(cmd) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (evm,cmd) = Reification.ic ~env:env ~sigma:evm cmd in
      Reification.declare_syntax name evm cmd ]
END

(** Patterns **)
VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Pattern
  | [ "Reify" "Declare" "Patterns" ident(name) ":=" lconstr(value) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (evd,value) = Reification.ic ~env:env ~sigma:evm value in
      Reification.declare_pattern name evd value
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Add_Pattern
  | [ "Reify" "Pattern" constr(rule) "+=" constr(pattern) "=>" lconstr(template) ] ->
    [ try
	let (evm,env) = Lemmas.get_current_context () in
	(** TODO: I probably need this as well! **)
	let (pattern,_)  = Constrintern.interp_constr env evm pattern in
	let (template,_) = Constrintern.interp_constr env evm template in
	let (rule,_)     = Constrintern.interp_constr env evm rule in
	Reification.add_pattern rule pattern template
      with
	Failure msg -> Pp.msgnl (Pp.str msg)
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Print_Pattern CLASSIFIED AS QUERY
  | [ "Reify" "Print" "Patterns" constr(name) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (name,_) = Constrintern.interp_constr env evm name in
      Pp.(msg_info (   str "Patterns for "
	            ++ Printer.pr_constr name
	            ++ str ":"
	            ++ fnl ()
	            ++ Reification.print_patterns name))
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Table
  | [ "Reify" "Declare" "Table" ident(name) ":" constr(key) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (evm,key) = Reification.ic ~env:env ~sigma:evm key in
      if Reification.declare_table name evm key then
	()
      else
        Pp.(msg_debug (   str "Error creating table '"
                       ++ str (Names.string_of_id name)
                       ++ str "'."))
    ]
  | [ "Reify" "Declare" "Typed" "Table" ident(name) ":" constr(key) "=>" constr(typ) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (evm,key) = Reification.ic ~env:env ~sigma:evm key in
      let (evm,typ) = Reification.ic ~env:env ~sigma:evm typ in
      if Reification.declare_typed_table name evm key typ then
	()
      else
	() (** TODO(gmalecha): message? **)
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Seed_Table
  | [ "Reify" "Seed" "Table" constr(tbl) "+=" integer(key) "=>" constr(value) ] ->
    [ (** TODO: Universes... **)
      let (evm,env) = Lemmas.get_current_context () in
      let (tbl,_)   = Constrintern.interp_constr env evm tbl in
      let (value,_) = Constrintern.interp_constr env evm value in
      if Reification.seed_table tbl key value then
	()
      else
	assert false ]
  | [ "Reify" "Seed" "Typed" "Table" constr(tbl) "+=" integer(key) "=>"
	"[[" constr(typ) "," constr(value) "]]" ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      (** TODO: Universes... **)
      let (tbl,_)   = Constrintern.interp_constr env evm tbl in
      let (typ,_)   = Constrintern.interp_constr env evm typ in
      let (value,_) = Constrintern.interp_constr env evm value in
      if Reification.seed_typed_table tbl key typ value then
	()
      else
	assert false ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Reify_Lemma
  | [ "Reify" "BuildLemma" "<" constr(typ) constr(term) constr(concl) ">"
        ident(name) ":" lconstr(lem) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let (lem,_)   = Constrintern.interp_constr env evm lem in
      let (typ,_)   = Constrintern.interp_constr env evm typ in
      let (term,_)  = Constrintern.interp_constr env evm term in
      let (concl,_) = Constrintern.interp_constr env evm concl in
      let (evm,lem_type) = Typing.type_of env evm lem in
      try
        Reification.declare_syntax_lemma
          ~name:name ~type_fn:typ ~prem_fn:term ~concl_fn:concl
          env evm lem_type
      with
        (Reification.ReificationFailure trm) as ex ->
          Pp.(msg_error (   str "Failed to reify term '"
		         ++ Printer.pr_constr (Lazy.force trm)
                         ++ str "'.")) ;
          raise (Failure "Reification failed")
    ]
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
          Reification.ReificationFailure trm ->
	    let pr = Pp.(   (str "Failed to reify term '")
		         ++ (Printer.pr_constr (Lazy.force trm))
                         ++ (str "'.")) in
	    Tacticals.New.tclZEROMSG pr
      end
    ]
END


TACTIC EXTEND Reify_Lambda_Shell_reify_bind
  | ["reify_expr_bind" constr(name) tactic(k) "[[" constr(tbls) "]]" "[[" ne_constr_list(es) "]]" ] ->
    [ let tbls = Reification.parse_tables tbls in
      Proofview.Goal.enter begin fun gl ->
        Printf.fprintf stderr "binding version!\n" ;
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
	  Reification.ReificationFailure trm ->
	    let pr = Pp.(   (str "Failed to reify term '")
		         ++ (Printer.pr_constr (Lazy.force trm))
	                 ++ (str "'.")) in
            Tacticals.New.tclZEROMSG pr
      end
    ]
END
