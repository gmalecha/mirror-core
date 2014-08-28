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

module type REIFICATION =
sig
  type map_type =
    SimpleMap of Term.constr * Term.constr
  | TypedMap of Term.constr * Term.constr

  val parse_tables : Term.constr -> map_type list

  (** Tables **)
  val declare_table : Names.identifier -> Term.constr -> unit
  val declare_typed_table : Names.identifier -> Term.constr -> Term.constr -> unit
  val seed_table    : Term.constr -> Term.constr -> Term.constr -> unit

  (** Patterns **)
  val declare_pattern : Names.identifier -> Term.constr -> unit
  val add_pattern     : Term.constr -> Term.constr (* rpattern *) -> Term.constr -> unit
  val print_patterns  : (Format.formatter -> unit -> unit) ->
    Format.formatter -> Term.constr -> unit

  (** Functions **)
  val declare_syntax : Names.identifier -> Term.constr (* command *) -> unit

  val reify     : Proof_type.goal Evd.sigma -> map_type list (* tables *) ->
    Term.constr -> Term.constr -> Term.constr
  val reify_all : Proof_type.goal Evd.sigma -> map_type list (* tables *) ->
    (Term.constr * Term.constr) list -> Term.constr list
end

module Reification : REIFICATION =
struct
  module Cmap = Map.Make
    (struct
      type t = Term.constr
      let compare = Term.constr_ord
     end)

  type map_type =
    SimpleMap of Term.constr * Term.constr
  | TypedMap of Term.constr * Term.constr

  type 'a environment =
  { mappings : 'a Cmap.t
  ; next     : int
  }

  type reify_env =
  { env : Environ.env
  ; evm : Evd.evar_map
  ; bindings : bool list
  ; mutable tables : (int environment) Cmap.t
  ; mutable typed_tables : (int * Term.constr) environment Cmap.t
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


  exception ReificationFailure of Term.constr

  (** [rule]s implement the pattern feature **)
  type 'a rule =
    ((int,int,reify_env) Term_match.pattern) *
      ('a -> (int, Term.constr) Hashtbl.t -> Term.constr)

  (** [reifier]s are the actual functions that get run **)
  type 'a reifier =
    reify_env -> 'a

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

  let reifier_ret (value : 'a) : 'a reifier =
    fun _ -> value

  let reifier_local (f : reify_env -> reify_env) (c : 'a reifier) : 'a reifier =
    fun gl -> c (f gl)

  let reifier_run (c : 'a reifier) (gl : reify_env) = c gl


  let call_reify_term (r : 'a reifier) gl trm =
    r gl trm empty_array (-1)

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

  let decl_constant ?typ (na : Names.identifier) (c : Term.constr) =
    Declare.(Term.mkConst(declare_constant na
			    (Entries.(DefinitionEntry
					{ const_entry_body = c;
					  const_entry_secctx = None;
					  const_entry_type = typ;
					  const_entry_opaque = false }),
			     Decl_kinds.(IsDefinition Definition))))

  module Tables =
  struct

    type key_type = Nat | Pos

    let the_seed_table : int environment Cmap.t ref =
      ref Cmap.empty

    let seed_table (c : Term.constr) (k : Term.constr) (v : Term.constr)
    : bool =
      assert false

    let declare_table (ls : Term.constr) (kt : key_type) =
      if Cmap.mem ls !the_seed_table then
	Pp.(msg_warning (   (str "Table '")
			 ++ (Printer.pr_constr ls)
			 ++ (str "' already exists.")))
      else
	let get =
	  match kt with
	    Nat -> Std.Nat.to_nat
	  | Pos -> Std.Positive.to_positive
	in
	the_seed_table := Cmap.add ls { mappings = Cmap.empty
				      ; next = 1
				      } !the_seed_table

    let declare_typed_table (ls : Term.constr) (kt : key_type) =
      if Cmap.mem ls !the_seed_table then
	Pp.(msg_warning (   (str "Table '")
			 ++ (Printer.pr_constr ls)
			 ++ (str "' already exists.")))
      else
	let get =
	  match kt with
	    Nat -> Std.Nat.to_nat
	  | Pos -> Std.Positive.to_positive
	in
	the_seed_table := Cmap.add ls { mappings = Cmap.empty
				      ; next = 1
				      } !the_seed_table


    let export_table (tbl : int environment) (typ : key_type) =
      (** TODO **)
      assert false

    let reify (tbl_name : Term.constr) (trm : lazy_term) : Term.constr reifier =
      assert false (*
	let tbl =
	  try
	    Cmap.find tbl_name renv.tables
	  with
	    Not_found -> raise (Failure "Accessing unbound table")
	in
	let trm =
	  if from = -1 then trm
	  else if from = Array.length ary then
	    Term.mkApp (trm, ary)
	  else Term.mkApp (trm, Array.sub ary 0 (from+1))
	in
	try
	  (** fast path something already in the table **)
	  Std.Positive.to_positive (Cmap.find trm tbl.mappings)
	with
	  Not_found ->
	    match get_by_conversion renv tbl trm with
	      None ->
		(** add to the table **)
		let result = tbl.next in
		renv.tables <- Cmap.add tbl_name 
		tbl.mappings <- Cmap.add trm (tbl.seed, result) tbl.mappings ;
		tbl.seed <- tbl.seed + 1 ;
		result
	    | Some k -> k
		     *)
  end

  module Patterns =
  struct
    (** State **)
    let pattern_table : ((reify_env rule) list) Cmap.t ref =
      ref Cmap.empty

    (** Freezing and thawing of state (for backtracking) **)
    let _ =
      Summary.(declare_summary "reify-lambda-shell-pattern-table"
	{ freeze_function = (fun () -> !pattern_table)
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
	  [ (EGlob ptrn_ignore,
	     fun _ _ -> RIgnore)
	  ; (apps (EGlob ptrn_get) [get 0; get 1],
	     fun _ s ->
	       let num  = Hashtbl.find s 0 in
	       let next = Hashtbl.find s 1 in
	       RGet (Std.Nat.of_nat num, into_rpattern next))
	  ; (apps (EGlob ptrn_exact) [Ignore; get 0],
	     fun _ s ->
	       let t = Hashtbl.find s 0 in
	       RExact t)
	  ; (apps (EGlob ptrn_app) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RApp (into_rpattern f, into_rpattern x))
	  ; (apps (EGlob ptrn_impl) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RImpl (into_rpattern f, into_rpattern x))
	  ; (apps (EGlob ptrn_pi) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RPi (into_rpattern f, into_rpattern x))
	  ; (apps (EGlob ptrn_lam) [get 0; get 1],
	     fun _ s ->
	       let f = Hashtbl.find s 0 in
	       let x = Hashtbl.find s 1 in
	       RLam (into_rpattern f, into_rpattern x))
	  ; (EGlob ptrn_const,
	     fun _ _ -> RConst)
	  ; (apps (EGlob ptrn_has_type) [get 0; get 1],
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
	    (Term_match.EGlob g, [])
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
	       let ty = Typing.type_of env.env env.evm trm in
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
	[ (App (EGlob action_function, get 0),
	   fun _ s -> Some (Func (Hashtbl.find s 0)))
	; (App (EGlob action_id, Ignore),
	   fun _ s -> Some Id)
	; (Ignore, fun _ _ -> None)
	])

    let compile_template
	(effects : (int, (int, Term.constr) Hashtbl.t -> reify_env -> reify_env) Hashtbl.t)
	(reify_term : Term.constr -> lazy_term -> Term.constr reifier) =
      let rec compile_template (tmp : Term.constr) (at : int)
	  : Term.constr list -> reify_env -> (int, Term.constr) Hashtbl.t -> Term.constr =
	match Term.kind_of_term tmp with
	  Term.Lambda (_, typ, body) ->
	    begin
	      match parse_action typ with
		None ->
		  let _ = Format.eprintf "Got Lambda, but didn't have action: %a" Std.pp_constr typ in
		  fun ls _ _ ->
		    Term.substnl ls 0 tmp
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
		    rest (cur_val :: vals) gl s
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
	  fun ls _ _ ->
	    Term.substnl ls 0 tmp
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

    let reify_patterns (i : Term.constr) trm =
      fun gl ->
	try
	  match trm with
	    Term trm ->
	      Term_match.matches gl
		(Cmap.find i !pattern_table)
		trm
	  | App (trm,args,from) ->
	    Term_match.matches_app gl
	      (Cmap.find i !pattern_table)
	      trm args from
	with
	  Term_match.Match_failure ->
	    raise (ReificationFailure (get_term trm))

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
	{ freeze_function   = (fun () -> !reify_table);
	  unfreeze_function = (fun pt -> reify_table := pt);
	  init_function     = (fun () -> reify_table := Cmap.empty) })

    type command =
    | Fail
    | Patterns of Term.constr
    | Call of Term.constr
    | App of Term.constr
    | Abs of Term.constr * Term.constr
    | Var of Term.constr
    | Table of Term.constr * Term.constr
    | TypedTable of Term.constr * Term.constr * Term.constr

    let reify_term (name : Term.constr) =
      let reifier = Cmap.find name !reify_table in
      reifier

    let cmd_fail     = Std.resolve_symbol pattern_mod "Fail"
    let cmd_patterns = Std.resolve_symbol pattern_mod "Patterns"
    let cmd_call     = Std.resolve_symbol pattern_mod "Call"
    let cmd_app      = Std.resolve_symbol pattern_mod "App"
    let cmd_abs      = Std.resolve_symbol pattern_mod "Abs"
    let cmd_var      = Std.resolve_symbol pattern_mod "Var"
    let cmd_table    = Std.resolve_symbol pattern_mod "Table"
    let cmd_typed_table = Std.resolve_symbol pattern_mod "TypedTable"

    let parse_command_act cmd =
      Term_match.(matches ()
	[ (App (EGlob cmd_fail, Ignore), fun _ _ -> Fail)
	; (apps (EGlob cmd_patterns) [Ignore;get 0],
	   fun _ s -> Patterns (Hashtbl.find s 0))
	; (apps (EGlob cmd_call) [Ignore;get 0],
	   fun _ s -> Call (Hashtbl.find s 0))
	; (apps (EGlob cmd_app) [Ignore;get 0],
	   fun _ s -> App (Hashtbl.find s 0))
	; (apps (EGlob cmd_var) [Ignore;get 0],
	   fun _ s -> Var (Hashtbl.find s 0))
	; (apps (EGlob cmd_abs) [Ignore;get 1;get 0],
	   fun _ s -> Abs (Hashtbl.find s 1,Hashtbl.find s 0))
	; (apps (EGlob cmd_table) [Ignore;Ignore;get 0;get 1],
	   fun _ s -> Table (Hashtbl.find s 0, Hashtbl.find s 1))
	; (apps (EGlob cmd_typed_table)
	     [Ignore(*T*);Ignore(*K*);get 0(*Ty*);
	      get 1(*tbl*);get 2(*ctor*)],
	   fun _ s ->
	     TypedTable (Hashtbl.find s 1, Hashtbl.find s 0, Hashtbl.find s 2))
	]
	cmd)


    let rec parse_commands cmd =
      Term_match.(matches ()
	[ (App (EGlob cmd_fail, get 0), fun _ s -> (Hashtbl.find s 0,[]))
	; (App (get 0, get 1),
	   fun _ s ->
	     let (typ,rest) = parse_commands (Hashtbl.find s 1) in
	     (typ,parse_command_act (Hashtbl.find s 0) :: rest))
	]
	cmd)

    let compile_commands (ls : command list)
    : lazy_term -> Term.constr reifier =
      let top = ref (fun _ _ -> assert false) in
      let rec compile_commands (ls : command list)
      : lazy_term -> Term.constr reifier =
	  match ls with
	    [] ->
	      fun trm ->
		let trm = get_term trm in
		let _ = Format.eprintf "Failed for: %a\n" Std.pp_constr trm in
		raise (ReificationFailure trm)
	  | l :: ls ->
	    let k = compile_commands ls in
	    match l with
	    | Patterns i ->
	      begin
		fun trm -> fun gl ->
		  try
		    Patterns.reify_patterns i trm gl
		  with
		    ReificationFailure _ -> k trm gl
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
		  | _ -> k trm gl
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
		  | _ -> k trm gl
		end
	    | App ctor ->
	      fun trm gl ->
		begin
		  try
		    Term_match.(matches gl
		      [ (App (get 0, get 1),
			 fun gl s ->
			   let f = !top (Term (Hashtbl.find s 0)) gl in
			   let x = !top (Term (Hashtbl.find s 1)) gl in
			   Term.mkApp (ctor, [| f ; x |]))
		      ])
		      (get_term trm)
		  with
		    Term_match.Match_failure -> k trm gl
		end
	    | Table (tbl_name,ctor) ->
	      begin
		let build x =
		  Term.mkApp (ctor, [| Std.Positive.to_positive x |])
		in
		fun trm renv ->
		  let tbl =
		    try
		      Cmap.find tbl_name renv.tables
		    with
		      Not_found -> { mappings = Cmap.empty
				   ; next = 1 }
		  in
		  let full_term = get_term trm in
		  try
	          (** fast path something already in the table **)
		    build (Cmap.find full_term tbl.mappings)
		  with
		    Not_found ->
		      match get_by_conversion renv tbl full_term with
			None ->
			  let (result, new_tbl) =
			    let result = tbl.next in
			    (result,
			     { tbl with
		               next = result + 1
			     ; mappings = Cmap.add full_term result tbl.mappings })
			  in
			  renv.tables <- Cmap.add tbl_name new_tbl renv.tables ;
			  build result
		      | Some k -> build k
	      end
	    | TypedTable (tbl_name, type_name, ctor) ->
	      begin
		let build x =
		  Term.mkApp (ctor, [| Std.Positive.to_positive x |])
		in
		fun trm renv ->
		  let tbl =
		    try
		      Cmap.find tbl_name renv.tables
		    with
		      Not_found -> { mappings = Cmap.empty
				   ; next = 1 }
		  in
		  Printf.eprintf "0\n" ;
		  let full_term = get_term trm in
		  let type_of = Typing.type_of renv.env renv.evm full_term in
		  Format.eprintf "1 %a\n" Std.pp_constr type_name ;
		  let rtyp = reify_term type_name (Term type_of) renv in
		  Printf.eprintf "2\n" ;
		  try
	          (** fast path something already in the table **)
		    let x = Cmap.find full_term tbl.mappings in
		    Printf.eprintf "found\n" ;
		    build x
		  with
		    Not_found ->
		      Printf.eprintf "3\n" ;
		      match get_by_conversion renv tbl full_term with
			None ->
			  Printf.eprintf "didn't find by conversion\n" ;
			  let (result, new_tbl) =
			    let result = tbl.next in
			    (result,
			     { tbl with
		               next = result + 1
			     ; mappings = Cmap.add full_term result tbl.mappings })
			  in
			  renv.tables <- Cmap.add tbl_name new_tbl renv.tables ;
			  Printf.eprintf "Done\n" ;
			  build result
		      | Some k -> build k
	      end
      in
      let result = compile_commands ls in
      top := result ;
      result

    let add_syntax (name : Term.constr) (cmds : Term.constr) : unit =
      let (_,program) = parse_commands cmds in
      let meta_reifier = compile_commands program in
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

    let declare_syntax (name : Names.identifier)
	(cmd : Term.constr) : unit =
      let (typ,_program) = parse_commands cmd in
      let _meta_reifier = compile_commands _program in
      let obj = decl_constant name typ in
      let _ = Lib.add_anonymous_leaf (syntax_object (obj,cmd)) in
      add_syntax obj cmd
  end

  let initial_env (gl : Proof_type.goal Evd.sigma) =
    let env = Tacmach.pf_env gl in
    let evar_map = Tacmach.project gl in
    { env = env
    ; evm = evar_map
    ; bindings = []
    ; tables = Cmap.empty (** TODO: This needs to add tables **)
    ; typed_tables = Cmap.empty }

  let reify (gl : Proof_type.goal Evd.sigma) tbls (name : Term.constr) trm =
    Syntax.reify_term name (Term trm) (initial_env gl)

  let reify_all gl tbls ns_e =
    let st = initial_env gl in
    List.map (fun (ns,e) -> Syntax.reify_term ns (Term e) st) ns_e

  let table_type = Std.resolve_symbol pattern_mod "table"
  let table_value = Std.resolve_symbol pattern_mod "a_table"
  let typed_table_type = Std.resolve_symbol pattern_mod "typed_table"
  let typed_table_value = Std.resolve_symbol pattern_mod "a_typed_table"

  let declare_table id key =
    let key_type =
      if Term.eq_constr key (Lazy.force Std.Nat.nat_type) then Tables.Nat
      else if Term.eq_constr key (Lazy.force Std.Positive.pos_type) then Tables.Pos
      else assert false
    in
    let key_ary = [| key |] in
    let obj = decl_constant ~typ:(Term.mkApp (table_type, key_ary))
      id (Term.mkApp (table_value, key_ary))
    in
    Tables.declare_table obj key_type

  let declare_typed_table id key typ =
    let key_type =
      if Term.eq_constr key (Lazy.force Std.Nat.nat_type) then Tables.Nat
      else if Term.eq_constr key (Lazy.force Std.Positive.pos_type) then Tables.Pos
      else assert false
    in
    let key_ary = [| key ; typ |] in
    let obj = decl_constant ~typ:(Term.mkApp (typed_table_type, key_ary))
      id (Term.mkApp (typed_table_value, key_ary))
    in
    Tables.declare_table obj key_type


  let seed_table name key value =
    assert false


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

  let declare_pattern (name : Names.identifier) (value : Term.constr) =
    let obj = decl_constant name (Term.mkApp (a_pattern, [| value |])) in
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

  let parse_table : Term.constr -> map_type =
    Term_match.(matches ()
		  [(apps (EGlob mk_var_map) [Ignore;Ignore;Ignore;get 0;get 1],
		    fun _ s -> SimpleMap (Hashtbl.find s 0, Hashtbl.find s 1))
		  ;(apps (EGlob mk_dvar_map) [Ignore;Ignore;Ignore;Ignore;
					      get 0;get 1],
		    fun _ s -> TypedMap (Hashtbl.find s 0, Hashtbl.find s 1))
		  ])

  let rec parse_tables (tbls : Term.constr) : map_type list =
    Term_match.(matches ()
		  [(Lam (0,get 0,get 1),
		    fun _ s ->
		      parse_table (Hashtbl.find s 0)
		      :: parse_tables (Hashtbl.find s 1))
		  ;(Ignore, fun _ s -> [])
		  ]) tbls


end

let print_newline out () =
  Format.fprintf out "\n"

VERNAC COMMAND EXTEND Reify_Lambda_Shell_add_lang
  | [ "Reify" "Declare" "Syntax" ident(name) ":=" "{" constr(cmd) "}" ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
(*      let typ = Constrintern.interp_constr evm env typ in *)
      let cmd = Constrintern.interp_constr evm env cmd in
      Reification.declare_syntax name cmd ]
END;;

(** Patterns **)
VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Pattern
  | [ "Reify" "Declare" "Patterns" ident(name) ":=" constr(value) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let value     = Constrintern.interp_constr evm env value in
      Reification.declare_pattern name value
    ]
END;;

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Add_Pattern
  | [ "Reify" "Pattern" constr(rule) "+=" constr(pattern) "=>" constr(template) ] ->
    [ try
	let (evm,env) = Lemmas.get_current_context () in
	let pattern   = Constrintern.interp_constr evm env pattern in
	let template  = Constrintern.interp_constr evm env template in
	let rule      = Constrintern.interp_constr evm env rule in
	Reification.add_pattern rule pattern template
      with
	Failure msg -> Pp.msgnl (Pp.str msg)
    ]
END;;

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Print_Pattern
  | [ "Reify" "Print" "Patterns" constr(name) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let name      = Constrintern.interp_constr evm env name in
      let as_string = (** TODO: I don't really understand Ocaml's formatting **)
	let _ =
	  Format.fprintf Format.str_formatter "%a"
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
END;;

VERNAC COMMAND EXTEND Reify_Lambda_Shell_Declare_Table
  | [ "Reify" "Declare" "Table" ident(name) ":" constr(key) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let key       = Constrintern.interp_constr evm env key in
      Reification.declare_table name key
    ]
  | [ "Reify" "Declare" "Typed" "Table" ident(name) ":" constr(key) "=>" constr(typ) ] ->
    [ let (evm,env) = Lemmas.get_current_context () in
      let key       = Constrintern.interp_constr evm env key in
      let typ       = Constrintern.interp_constr evm env typ in
      Reification.declare_typed_table name key typ
    ]
END;;

TACTIC EXTEND Reify_Lambda_Shell_reify
  | ["reify_expr" constr(name) tactic(k) "[" constr(tbls) "]" "[" ne_constr_list(es) "]" ] ->
    [ fun gl ->
      let tbls = Reification.parse_tables tbls in
      let res = Reification.reify_all gl tbls (List.map (fun e -> (name,e)) es) in
      let ltac_args =
	List.map
	  Plugin_utils.Use_ltac.to_ltac_val
	  res
      in
      Plugin_utils.Use_ltac.ltac_apply k ltac_args gl
    ]
END;;
