module Std : Plugin_utils.Coqstd.STD

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

type use_or_bind =
    Use
  | RBind
  | RSkip

type table_name = Term.constr

type command =
    Rec        of int
  | Fix        of command
  | Or         of command * command
  | Fail
  | Call       of Term.constr
  | Map        of Term.constr * command
  | App        of command * command * Term.constr
  | Abs        of command * command * Term.constr
  | Var        of Term.constr
  | PiMeta     of Term.constr * command
  | Patterns   of Term.constr
  | Pattern    of rule list
  | Table      of table_name
  | TypedTable of table_name * command (** To parse the type *)

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

exception ParseFailure of Term.constr * string

val parse_command : Environ.env -> Evd.evar_map -> Term.constr -> command

val parse_pattern : Environ.env -> Evd.evar_map -> Term.constr -> Term.constr -> rule

val parse_tables : Term.constr -> map_type list

val drop_calls : Term.constr -> Term.constr
