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
  val print_patterns  : (Format.formatter -> unit -> unit) ->
    Format.formatter -> Term.constr -> unit

  (** Functions **)
  val declare_syntax : Names.identifier -> Evd.evar_map -> Term.constr (* command *) -> unit

  (** Reification **)
  val reify     : 'a Proofview.Goal.t -> map_type list (* tables *) ->
    Term.constr -> Term.constr -> Term.constr * all_tables
  val reify_all : 'a Proofview.Goal.t -> map_type list (* tables *) ->
    (Term.constr * Term.constr) list -> Term.constr list * all_tables
  val export_table : Term.constr list -> map_type -> all_tables -> Term.constr


  val pose_each : (string * Term.constr) list -> (Term.constr list -> unit Proofview.tactic) -> unit Proofview.tactic
end

module Reification : REIFICATION =
struct
  module Cmap = Map.Make
    (struct
      type t = Term.constr
      let compare = Term.constr_ord
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
    let pattern_table : ((reify_env rule) list) Cmap.t ref =
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
	  [ (EGlob_no_univ ptrn_ignore,
	     fun _ _ -> RIgnore)
	  ; (apps (EGlob_no_univ ptrn_get) [get 0; get 1],
	     fun _ s ->
	       let num  = Hashtbl.find s 0 in
	       let next = Hashtbl.find s 1 in
	       RGet (Std.Nat.of_nat num, into_rpattern next))
	  ; (apps (EGlob_no_univ ptrn_exact) [Ignore; get 0],
	     fun _ s ->
	       let t = Hashtbl.find s 0 in
	       RExact t)
	  ; (apps (EGlob_no_univ ptrn_app) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RApp (into_rpattern f, into_rpattern x))
	  ; (apps (EGlob_no_univ ptrn_impl) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RImpl (into_rpattern f, into_rpattern x))
	  ; (apps (EGlob_no_univ ptrn_pi) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RPi (into_rpattern f, into_rpattern x))
	  ; (apps (EGlob_no_univ ptrn_lam) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RLam (into_rpattern f, into_rpattern x))
	  ; (EGlob_no_univ ptrn_const,
	     fun _ _ -> RConst)
	  ; (apps (EGlob_no_univ ptrn_has_type) [get 0; get 1],
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
	       let (_,ty) = Typing.type_of env.env env.evm trm in
	       Term.eq_constr ty t), p), l)
      in
      compile_pattern

    type action =
      Func of Term.constr
    | Id
    | Associate of Term.constr (* table name *) * Term.constr (* key *)
    | Store of Term.constr (* table name *)

    let parse_action : Term.constr -> action option =
      Term_match.(matches ()
	[ (App (EGlob_no_univ action_function, get 0),
	   fun _ s -> Some (Func (Hashtbl.find s 0)))
	; (App (EGlob_no_univ action_id, Ignore),
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
		  Pp.(msgerrnl (    (str "Failed to parse action from lambda.Got term: \n")
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

    let extend trm rul =
      try
	let objs = Cmap.find trm !pattern_table in
	pattern_table := Cmap.add trm (rul :: objs) !pattern_table
      with
      | Not_found -> assert false

    let add_pattern (dispatch : Term.constr -> lazy_term -> 'a reifier)
	(name : Term.constr) (ptrn : Term.constr) (template : Term.constr)
	: unit =
      try
	let effects = Hashtbl.create 1 in
	let (ptrn, occs) = compile_pattern effects (into_rpattern ptrn) None in
	let action = compile_template effects dispatch template 0 [] in
	extend name (ptrn, action)
      with
	Term_match.Match_failure -> raise (Failure "match failed, please report")

    let rec print_rule out ptrn =
      Term_match.(
	match ptrn with
	  Ignore -> Format.fprintf out "<any>"
	| As (a,i) -> Format.fprintf out "((%a) as %d)" print_rule a i
	| App (l,r) -> Format.fprintf out "(%a %@ %a)" print_rule l print_rule r
	| Impl (l,r) -> Format.fprintf out "(%a -> %a)" print_rule l print_rule r
	| Glob g -> Format.fprintf out "%a" Std.pp_constr (Lazy.force g)
	| EGlob g -> Format.fprintf out "%a" Std.pp_constr g
	| Glob_no_univ g -> Format.fprintf out "%a" Std.pp_constr (Lazy.force g)
	| EGlob_no_univ g -> Format.fprintf out "%a" Std.pp_constr g
	| Lam (a,b,c) -> Format.fprintf out "(fun (%d : %a) => %a)" a print_rule b print_rule c
	| Ref i -> Format.fprintf out "<%d>" i
	| Choice ls -> Format.fprintf out "[...]"
	| Pi (a,b) -> Format.fprintf out "(Pi %a . %a)" print_rule a print_rule b
	| Filter (_,a) -> Format.fprintf out "(Filter - %a)" print_rule a)

    let apps = List.fold_right Pp.(++)

    let print_patterns sep out (name : Term.constr) : unit =
      try
	let vals = Cmap.find name !pattern_table in
	List.iter (fun x -> Format.fprintf out "%a%a" sep () print_rule (fst x)) vals
      with
	Not_found -> Pp.(msg_warning (   (str "Unknown pattern table '")
				      ++ (Printer.pr_constr name)
				      ++ (str "'.")))

    let reify_patterns (i : Term.constr) trm
    : Term.constr reifier =
      fun gl ->
	try
	  match trm with
	    Term trm ->
	      Term_match.matches gl
		(Cmap.find i !pattern_table)
		trm gl
	  | App (trm,args,from) ->
	    Term_match.matches_app gl
	      (Cmap.find i !pattern_table)
	      trm args from gl
	with
	  Term_match.Match_failure ->
	    reifier_fail_lazy trm gl

    let add_empty_pattern name =
      if Cmap.mem name !pattern_table then
	Pp.(
	  msgnl (   (str "Pattern table '")
		 ++ (Printer.pr_constr name)
	         ++ (str "' already exists.")))
      else
	pattern_table := Cmap.add name [] !pattern_table

    let declare_pattern (obj : Term.constr) =
      add_empty_pattern obj

  end

  module Syntax =
  struct
    let reify_table : (lazy_term -> Term.constr reifier) Cmap.t ref =
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
      reifier

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
	[ (apps (EGlob_no_univ cmd_patterns) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Patterns (Hashtbl.find s 0)))
	; (apps (EGlob_no_univ cmd_call) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Call (Hashtbl.find s 0)))
	; (apps (EGlob_no_univ cmd_app) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,App (Hashtbl.find s 0)))
	; (apps (EGlob_no_univ cmd_var) [get ~-1(*T*);get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Var (Hashtbl.find s 0)))
	; (apps (EGlob_no_univ cmd_abs) [get ~-1(*T*);get 1;get 0],
	   fun _ s -> (Hashtbl.find s ~-1,Abs (Hashtbl.find s 1,Hashtbl.find s 0)))
	; (apps (EGlob_no_univ cmd_table) [get ~-1(*T*);Ignore;get 0;get 1],
	   fun _ s -> (Hashtbl.find s ~-1,Table (Hashtbl.find s 0, Hashtbl.find s 1)))
	; (apps (EGlob_no_univ cmd_typed_table)
	     [get ~-1(*T*);Ignore(*K*);get 0(*Ty*);
	      get 1(*tbl*);get 2(*ctor*)],
	   fun _ s ->
	     (Hashtbl.find s ~-1,TypedTable (Hashtbl.find s 1, Hashtbl.find s 0, Hashtbl.find s 2)))
	; (apps (EGlob_no_univ cmd_map)
	     [get ~-1(*T*);Ignore;get 1(*F*);get 0(*cmd*)],
	   fun _ s ->
	     let (_,c) = parse_command (Hashtbl.find s 0) in
	     (Hashtbl.find s ~-1,Map (Hashtbl.find s 1, c)))
	; (apps (EGlob_no_univ cmd_first)
	     [get ~-1(*T*);get 0(*cmds*)],
	   fun _ s ->
	     (Hashtbl.find s ~-1,First (parse_commands (Hashtbl.find s 0))))
	]
	cmd)

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
		  let rec find ls i acc =
		    match ls with
		      [] -> assert false
		    | l :: ls ->
		      if i = 0 then
			(assert l ; acc)
		      else
			find ls (i - 1) (if l then acc + 1 else acc)
		  in
		  let idx = find gl.bindings (i-1) 0 in
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

    let add_syntax (name : Term.constr) (cmds : Term.constr) : unit =
      let (_,program) = parse_command cmds in
      let meta_reifier = compile_command program in
      let _ =
	if Cmap.mem name !reify_table then
	  Pp.(msg_warning (   (str "Redeclaring syntax '")
			   ++ (Printer.pr_constr name)
			   ++ (str "'")))
	else ()
      in
      reify_table := Cmap.add name meta_reifier !reify_table

    let syntax_object : Term.constr * Term.constr -> Libobject.obj =
      Libobject.(declare_object
	{ (default_object "REIFY_SYNTAX") with
	  cache_function = (fun (_,_) -> ())
	; load_function = fun i ((b,n),value) ->
	  let (name, cmds) = value in
	  add_syntax name cmds
	})

    let declare_syntax (name : Names.identifier) evm
	(cmd : Term.constr) : unit =
      let (typ,_program) = parse_command cmd in
      let _meta_reifier = compile_command _program in
      let obj = decl_constant name evm typ in
      let _ = Lib.add_anonymous_leaf (syntax_object (obj,cmd)) in
      add_syntax obj cmd
  end

  let initial_env (gl : 'a Proofview.Goal.t) (tbls : map_type list) =
    let env = Proofview.Goal.env gl in
    let evar_map = Proofview.Goal.sigma gl in
    { env = env
    ; evm = evar_map
    ; bindings = []
    ; typed_tables = ref !Tables.the_seed_table }

  let reify (gl : 'a Proofview.Goal.t) tbls (name : Term.constr) trm =
    let env = initial_env gl tbls in
    let result = Syntax.reify_term name (Term trm) env in
    (result, { tables = !(env.typed_tables) })

  let reify_all gl tbls ns_e =
    let st = initial_env gl tbls in
    let result = List.map (fun (ns,e) -> Syntax.reify_term ns (Term e) st) ns_e in
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
    let obj = decl_constant ~typ:(Term.mkApp (table_type, key_ary))
      id evm (Term.mkApp (table_value, key_ary))
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
    let obj = decl_constant ~typ:(Term.mkApp (typed_table_type, key_ary))
      id evm (Term.mkApp (typed_table_value, key_ary))
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
    let obj = decl_constant name evd (Term.mkApp (a_pattern, [| value |])) in
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
		  [(apps (EGlob_no_univ mk_var_map) [Ignore;Ignore;get 2;get 0;get 1],
		    fun _ s -> { table_name = Hashtbl.find s 0
			       ; table_elem_type = Hashtbl.find s 2
			       ; table_elem_ctor = Hashtbl.find s 1
			       ; table_scheme = SimpleMap })
		  ;(apps (EGlob_no_univ mk_dvar_map) [Ignore;Ignore;get 2;Ignore;
					      get 0;get 1],
		    fun _ s -> { table_name = Hashtbl.find s 0
			       ; table_elem_type = Hashtbl.find s 2
			       ; table_elem_ctor = Hashtbl.find s 1
			       ; table_scheme = TypedMap })
		  ;(apps (EGlob_no_univ mk_dvar_map_abs) [Ignore;Ignore;get 2;get 3;
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
end

let print_newline out () =
  Format.fprintf out "\n"

let ic ?env ?sigma c =
  let env =
    match env with
    | None -> Global.env()
    | Some x -> x
  in
  let sigma =
    match sigma with
    | None -> Evd.empty
    | Some x -> x
  in
  Constrintern.interp_open_constr env sigma c


VERNAC COMMAND EXTEND Reify_Lambda_Shell_add_lang
  | [ "Reify" "Declare" "Syntax" ident(name) ":=" "{" constr(cmd) "}" ] ->
    [ let (evm,cmd) = ic cmd in
      Reification.declare_syntax name evm cmd ]
END

(** Patterns **)
VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Pattern
  | [ "Reify" "Declare" "Patterns" ident(name) ":=" constr(value) ] ->
    [ let (evd,value) = ic value in
      Reification.declare_pattern name evd value
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Add_Pattern
  | [ "Reify" "Pattern" constr(rule) "+=" constr(pattern) "=>" constr(template) ] ->
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
      (** TODO: I need this **)
      let (name,name_univ) = Constrintern.interp_constr env evm name in
      let as_string = (** TODO: I don't really understand Ocaml's formatting **)
	let _ = Format.flush_str_formatter () in
	let _ =
	  Format.fprintf Format.err_formatter "%a"
	    (Reification.print_patterns print_newline) name in
	Format.flush_str_formatter ()
      in
      Pp.(
      msgnl (   (str "Patterns for ")
	     ++ (Printer.pr_constr name)
	     ++ (str ":")
	     ++ (fnl ())
	     ++ (str as_string)))
    ]
END

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Table
  | [ "Reify" "Declare" "Table" ident(name) ":" constr(key) ] ->
    [ let (evm,key) = ic key in
      if Reification.declare_table name evm key then
	()
      else
	() (** TODO(gmalecha): message? **)
    ]
  | [ "Reify" "Declare" "Typed" "Table" ident(name) ":" constr(key) "=>" constr(typ) ] ->
    [ let (evm,key) = ic key in
      let (evm,typ) = ic ~sigma:evm typ in
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
      let (tbl,tbl_univ)     = Constrintern.interp_constr env evm tbl in
      let (value,value_univ) = Constrintern.interp_constr env evm value in
      if Reification.seed_table tbl key value then
	()
      else
	assert false ]
  | [ "Reify" "Seed" "Typed" "Table" constr(tbl) "+=" integer(key) "=>"
	"[" constr(typ) "," constr(value) "]" ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      (** TODO: Universes... **)
      let (tbl,tbl_univ)     = Constrintern.interp_constr env evm tbl in
      let (typ,typ_univ)     = Constrintern.interp_constr env evm typ in
      let (value,value_univ) = Constrintern.interp_constr env evm value in
      if Reification.seed_typed_table tbl key typ value then
	()
      else
	assert false ]
END

TACTIC EXTEND Reify_Lambda_Shell_reify
  | ["reify_expr" constr(name) tactic(k) "[" constr(tbls) "]" "[" ne_constr_list(es) "]" ] ->
    [ let tbls = Reification.parse_tables tbls in
      Proofview.Goal.enter begin fun gl ->
	try
	  let (res,tbl_data) =
	    Reification.reify_all gl tbls (List.map (fun e -> (name,e)) es)
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
	  (Reification.ReificationFailure trm) as ex->
(*	    let pr = lazy (Pp.(   (str "Failed to reify term '")
			       ++ (Printer.pr_constr (Lazy.force trm))
			       ++ (str "'."))) in *)
	    Proofview.tclZERO ex
			    end
    ]
END


TACTIC EXTEND Reify_Lambda_Shell_reify_bind
  | ["reify_expr_bind" constr(name) tactic(k) "[" constr(tbls) "]" "[" ne_constr_list(es) "]" ] ->
    [ let tbls = Reification.parse_tables tbls in
      Proofview.Goal.enter begin fun gl ->
        Printf.fprintf stderr "binding version!\n" ;
	try
	  let (res,tbl_data) =
	    Reification.reify_all gl tbls (List.map (fun e -> (name,e)) es)
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
	  (Reification.ReificationFailure trm) as ex ->
(*	    let pr = lazy (Pp.(   (str "Failed to reify term '")
			       ++ (Printer.pr_constr (Lazy.force trm))
			       ++ (str "'."))) in *)
	    Proofview.tclZERO ex
			   end
    ]
END
