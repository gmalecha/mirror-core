open Plugin_utils

module Std = Coqstd.Std
    (struct
      let contrib_name = "MirrorCore.Reify"
     end)

exception ParseFailure of Term.constr * string

(* Types *)
type map_sort =
    SimpleMap
  | TypedMap
  | TypedMapAbs of Term.constr
type map_type =
  { table_name      : Term.constr
  ; table_elem_type : Term.constr
  ; table_elem_ctor : Term.constr
  ; table_scheme    : map_sort
  }

type use_or_bind =
    Use
  | RBind
  | RSkip

(* let pattern_mod = ["MirrorCore";"Reify";"Patterns"] *)

type table_name = Term.constr

type command =
    Rec of int
  | Fix of command
  | Or of command * command
  | Fail
  | Call of Term.constr
  | Map of Term.constr * command
  | App of command * command * Term.constr
  | Abs of command * command * Term.constr
  | Var of Term.constr
  | PiMeta of Term.constr * command
  | Patterns of Term.constr
  | Pattern of rule list
  | Table of table_name
  | TypedTable of table_name * command

and rpattern =
    RIgnore
  | RHasType of Term.constr * rpattern
  | RConst
  | RGet   of int * rpattern
  | RApp   of rpattern * rpattern
  | RPi    of rpattern * use_or_bind * rpattern
  | RLam   of rpattern * rpattern
  | RImpl  of rpattern * rpattern
  | RExact of Term.constr

and action =
    Func of command
  | Id

and template =
    Bind of action * template
  | Return of Term.constr

(** [rule]s implement the pattern feature **)
and rule =
  { rule_pattern  : rpattern
  ; rule_template : template
  }

(** Parsing functions *)
let pattern_mod = ["MirrorCore";"Reify";"Patterns"]

let resolve_poly_symbol_no_univs path tm =
  lazy (
    let re = Coqlib.find_reference "MirrorCore.Reify" path tm in
    fst (Universes.unsafe_constr_of_global re))

(* Patterns *)
let ptrn_exact    = resolve_poly_symbol_no_univs pattern_mod "RExact"
let ptrn_const    = resolve_poly_symbol_no_univs pattern_mod "RConst"
let ptrn_ignore   = resolve_poly_symbol_no_univs pattern_mod "RIgnore"
let ptrn_get      = resolve_poly_symbol_no_univs pattern_mod "RGet"
let ptrn_app      = resolve_poly_symbol_no_univs pattern_mod "RApp"
let ptrn_pi       = resolve_poly_symbol_no_univs pattern_mod "RPi"
let ptrn_lam      = resolve_poly_symbol_no_univs pattern_mod "RLam"
let ptrn_impl     = resolve_poly_symbol_no_univs pattern_mod "RImpl"
let ptrn_has_type = resolve_poly_symbol_no_univs pattern_mod "RHasType"

(* Actions *)
let action_function  = resolve_poly_symbol_no_univs pattern_mod "function"
let action_id        = resolve_poly_symbol_no_univs pattern_mod "id"

(* Commands *)
let cmd_patterns = resolve_poly_symbol_no_univs pattern_mod "CPatterns"
let cmd_pattern  = resolve_poly_symbol_no_univs pattern_mod "CPatternTr"
let cmd_app      = resolve_poly_symbol_no_univs pattern_mod "CApp"
let cmd_abs      = resolve_poly_symbol_no_univs pattern_mod "CAbs"
let cmd_var      = resolve_poly_symbol_no_univs pattern_mod "CVar"
let cmd_pi_meta  = resolve_poly_symbol_no_univs pattern_mod "CPiMeta"
let cmd_table    = resolve_poly_symbol_no_univs pattern_mod "CTable"
let cmd_typed_table = resolve_poly_symbol_no_univs pattern_mod "CTypedTable"
let cmd_map      = resolve_poly_symbol_no_univs pattern_mod "CMap"
let cmd_or       = resolve_poly_symbol_no_univs pattern_mod "COr"
let cmd_fail     = resolve_poly_symbol_no_univs pattern_mod "CFail"
let cmd_rec      = resolve_poly_symbol_no_univs pattern_mod "CRec"
let cmd_fix      = resolve_poly_symbol_no_univs pattern_mod "CFix"
let cmd_call     = resolve_poly_symbol_no_univs pattern_mod "CCall"

let c_mkRBranch = resolve_poly_symbol_no_univs pattern_mod "mkRBranch"

let trm_match branches env trm =
  Term_match.matches env branches trm


(* This function parses a [constr] and produces an [rpattern] and
 * 1+maximum bound variable.
*)
let rec parse_pattern_ ptrn : rpattern * int =
  let open Term_match in
  trm_match
    [ (Glob_no_univ ptrn_ignore,
       fun _ _ -> (RIgnore, 0))
    ; (apps (Glob_no_univ ptrn_get) [get 0; get 1],
       fun _ s ->
	 let num  = Std.Nat.of_nat (Hashtbl.find s 0) in
	 let next = Hashtbl.find s 1 in
         let (rst, mx) = parse_pattern_ next in
	 (RGet (num, rst), max mx (1+num)))
    ; (apps (Glob_no_univ ptrn_exact) [Ignore; get 0],
       fun _ s ->
	 let t = Hashtbl.find s 0 in
	 (RExact t, 0))
    ; (apps (Glob_no_univ ptrn_app) [get 0; get 1],
       fun _ s ->
	 let (f,mx1) = parse_pattern_ (Hashtbl.find s 0) in
	 let (x,mx2) = parse_pattern_ (Hashtbl.find s 1) in
      	 (RApp (f, x), max mx1 mx2))
    ; (apps (Glob_no_univ ptrn_impl) [get 0; get 1],
       fun _ s ->
	 let (f,mx1) = parse_pattern_ (Hashtbl.find s 0) in
	 let (x,mx2) = parse_pattern_ (Hashtbl.find s 1) in
      	 (RImpl (f, x), max mx1 mx2))
    ; (apps (Glob_no_univ ptrn_pi) [get 0; get 1],
       fun _ s ->
	 let (f,mx1) = parse_pattern_ (Hashtbl.find s 0) in
	 let (x,mx2) = parse_pattern_ (Hashtbl.find s 1) in
	 (RPi (f, RBind, x), max mx1 mx2))
    ; (apps (Glob_no_univ ptrn_lam) [get 0; get 1],
       fun _ s ->
         let (f,mx1) = parse_pattern_ (Hashtbl.find s 0) in
	 let (x,mx2) = parse_pattern_ (Hashtbl.find s 1) in
	 (RLam (f, x), max mx1 mx2))
    ; (Glob_no_univ ptrn_const,
       fun _ _ -> (RConst, 0))
    ; (apps (Glob_no_univ ptrn_has_type) [get 0; get 1],
       fun _ s ->
	 let t = Hashtbl.find s 0 in
	 let (x,mx) = parse_pattern_ (Hashtbl.find s 1) in
	 (RHasType (t, x), mx))
    ; (get 0,
       fun _ s ->
         raise (ParseFailure (Hashtbl.find s 0, "pattern")))
    ] () ptrn

let rec parse_action_ env_evm trm : action =
  let open Term_match in
  trm_match
    [ (apps (Glob_no_univ action_function) [Ignore;get 0],
       fun env_evd s ->
         let f = Hashtbl.find s 0 in
         Func (parse_command_ env_evd f))
    ; (App (Glob_no_univ action_id, Ignore),
       fun _ s -> Id)
    ; (get 0,
       fun _ s ->
         let trm = Hashtbl.find s 0 in
         raise (ParseFailure (trm, "action")))
    ] env_evm trm

and parse_template env_evd (n : int) (tmp : Term.constr) : template =
  if n > 0 then
    try
      let (_, typ, body) = Term.destLambda tmp in
      let act = parse_action_ env_evd typ in
      let rst = parse_template env_evd (n-1) body in
      Bind (act, rst)
    with
    | Term.DestKO ->
      raise (ParseFailure (tmp, "template"))
  else
    Return tmp

and parse_branch env_evm trm =
  let open Term_match in
  trm_match
    [ (apps (Glob_no_univ c_mkRBranch) [Ignore(*T*);Ignore(*ls*);get 0;get 1],
       fun env_evm s ->
         let ptrn = Hashtbl.find s 0 in
         let template = Hashtbl.find s 1 in
         let (rptrn, bindings) = parse_pattern_ ptrn in
         let template = parse_template env_evm bindings template in
         { rule_pattern = rptrn
         ; rule_template = template })
    ; (get 0,
       fun _ s -> raise (ParseFailure (Hashtbl.find s 0, "branch")))
    ] env_evm trm

and parse_list_of_patterns env_evm trm =
  let open Term_match in
  trm_match
    [ (apps (Glob_no_univ Std.List.c_cons) [Ignore(*T*);get 0;get 1],
       fun env_evm s ->
         let b = parse_branch env_evm (Hashtbl.find s 0) in
         let r = Hashtbl.find s 1 in
         let rest = parse_list_of_patterns env_evm r in
         b :: rest)
    ; (apps (Glob_no_univ Std.List.c_nil) [Ignore(*T*)],
       fun _ s -> [])
    ; (get 0,
       fun _ s -> raise (ParseFailure (Hashtbl.find s 0, "pattern list")))
    ] env_evm trm

and parse_command_ env_evm =
  let rec parse_command ?normalized:(normalized=false) =
    let open Term_match in
    trm_match
      [ (apps (Glob_no_univ cmd_fix) [Ignore(*T*);get 0],
         fun env_evm s -> Fix (parse_command env_evm (Hashtbl.find s 0)))
      ; (apps (Glob_no_univ cmd_rec) [Ignore(*T*);get 0],
         fun _ s -> Rec (Std.Nat.of_nat (Hashtbl.find s 0)))
      ; (apps (Glob_no_univ cmd_patterns) [Ignore(*T*);get 0],
         fun _ s -> Patterns (Hashtbl.find s 0))
      ; (apps (Glob_no_univ cmd_pattern) [Ignore(*T*);get 0],
         fun env_evm s ->
           Pattern (parse_list_of_patterns env_evm (Hashtbl.find s 0)))
      ; (apps (Glob_no_univ cmd_app)
           [Ignore(*T*);Ignore(*T*);Ignore(*T*);get 0;get 1; get 2],
	 fun env_evm s ->
           let f = parse_command env_evm (Hashtbl.find s 0) in
           let x = parse_command env_evm (Hashtbl.find s 1) in
           App (f, x, Hashtbl.find s 2))
      ; (apps (Glob_no_univ cmd_var) [Ignore(*T*);get 0],
	 fun _ s -> Var (Hashtbl.find s 0))
      ; (apps (Glob_no_univ cmd_pi_meta) [get 0;Ignore(*T*);get 1],
	 fun env_evm s ->
           PiMeta (Hashtbl.find s 0, parse_command env_evm (Hashtbl.find s 1)))
      ; (apps (Glob_no_univ cmd_abs)
           [Ignore(*T*);Ignore(*T*);Ignore(*U*);get 1;get 0;get 2],
	 fun evn_evm s ->
           let ty = parse_command env_evm (Hashtbl.find s 1) in
           let body = parse_command env_evm (Hashtbl.find s 0) in
           Abs (ty, body,
                Hashtbl.find s 2))
      ; (apps (Glob_no_univ cmd_table) [Ignore(*T*);get 0],
	 fun _ s -> Table (Hashtbl.find s 0))
      ; (apps (Glob_no_univ cmd_typed_table)
	   [Ignore(*T*);Ignore(*Ty*);get 0;get 1(*tbl*)],
	 fun env_evm s ->
	   TypedTable (Hashtbl.find s 1,
                       parse_command env_evm (Hashtbl.find s 0)))
      ; (apps (Glob_no_univ cmd_map)
	   [Ignore(*T*);Ignore;get 1(*F*);get 0(*cmd*)],
	 fun env_evm s ->
	   let c = parse_command env_evm (Hashtbl.find s 0) in
	   Map (Hashtbl.find s 1, c))
      ; (apps (Glob_no_univ cmd_or) [Ignore; get 0; get 1],
         fun env_evm s ->
           Or (parse_command env_evm (Hashtbl.find s 0),
               parse_command env_evm (Hashtbl.find s 1)))
      ; (Glob_no_univ cmd_fail, fun _ _ -> Fail)
      ; (apps (Glob_no_univ cmd_call) [Ignore; get 0],
         fun env_evm s -> Call (Hashtbl.find s 0))
      ; (get 0,
         fun env_evm s ->
           let cmd = Hashtbl.find s 0 in
           if not normalized then
             begin
               let (env,evm) = env_evm in
               let reduced = Reductionops.whd_betadeltaiota
                   env evm cmd in
               parse_command ~normalized:true env_evm reduced
             end
           else raise (ParseFailure (cmd, "command")))
      ]
  in parse_command ~normalized:false env_evm

let parse_command a b c = parse_command_ (a,b) c

let parse_pattern env evd ptrn template =
  let (rptrn, num_bindings) = parse_pattern_ ptrn in
  let template = parse_template (env,evd) num_bindings template in
  { rule_pattern = rptrn
  ; rule_template = template }

let table_type = resolve_poly_symbol_no_univs pattern_mod "table"
let table_value = resolve_poly_symbol_no_univs pattern_mod "a_table"
let typed_table_type = resolve_poly_symbol_no_univs pattern_mod "typed_table"
let typed_table_value = resolve_poly_symbol_no_univs pattern_mod "a_typed_table"

let mk_var_map = resolve_poly_symbol_no_univs pattern_mod "mk_var_map"
let mk_dvar_map = resolve_poly_symbol_no_univs pattern_mod "mk_dvar_map"
let mk_dvar_map_abs = resolve_poly_symbol_no_univs pattern_mod "mk_dvar_map_abs"

let parse_table : Term.constr -> map_type =
  let open Term_match in
  matches ()
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
      fun _ s -> { table_name = Hashtbl.find s 0
		 ; table_elem_type = Hashtbl.find s 2
		 ; table_elem_ctor = Hashtbl.find s 1
		 ; table_scheme = TypedMapAbs (Hashtbl.find s 3) })
    ; (get 0,
       fun _ s ->
         raise (ParseFailure (Hashtbl.find s 0, "table")))
    ]

let rec parse_tables (tbls : Term.constr) : map_type list =
  let open Term_match in
  matches ()
    [ (Lam (0,get 0,get 1),
       fun _ s ->
	    parse_table (Hashtbl.find s 0)
         :: parse_tables (Hashtbl.find s 1))
    ; (Ignore, fun _ s -> [])
    ] tbls

let rec drop_calls trm =
  let open Term_match in
  trm_match
      [ (apps (Glob_no_univ cmd_call) [Ignore; get 0],
         fun env_evm s -> drop_calls (Hashtbl.find s 0))
      ; (get 0,
         fun env_evm s -> trm)
      ] () trm
