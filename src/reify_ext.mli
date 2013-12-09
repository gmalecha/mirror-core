open Reify_gen

module type EXPR_BUILDER =
sig
  type e_result
  type t_result
  val mkVar : int -> e_result
  val mkUVar : int -> e_result
  val mkAbs : t_result -> e_result -> e_result
  val mkApp : e_result -> e_result -> e_result
end

module ReifyType
  (M : MONAD)
  (R : REIFY with type 'a m = 'a M.m
             with type result = Term.constr)
  (Z : sig val under_type : bool -> 'a M.m -> 'a M.m
	   val lookup_type : int -> int M.m
       end)
  : REIFY with type 'a m = 'a M.m
    with type result = Term.constr

module ReifyExpr
  (M : MONAD)
  (E : READER with type env = Environ.env
              with type 'a m = 'a M.m)
  (EXPR : EXPR_BUILDER)
  (RT : REIFY with type 'a m = 'a M.m
              with type result = EXPR.t_result)
  (RE : REIFY with type 'a m = 'a M.m
              with type result = EXPR.e_result)
  (RA : REIFY_APP with type 'a m = 'a M.m
                  with type result = EXPR.e_result)
  : REIFY with type 'a m = 'a M.m
          with type result = EXPR.e_result

module REIFY_MONAD
: sig
  type 'a m

  val ret : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m

  val ask_env : Environ.env m
  val local_env : (Environ.env -> Environ.env) -> 'a m -> 'a m

  val ask_evar : Evd.evar_map m
  val local_evar : (Evd.evar_map -> Evd.evar_map) -> 'a m -> 'a m

  val under_type : bool -> 'a m -> 'a m
  val lookup_type : int -> int m

  val get_types : Term.constr option list m
  val put_types : Term.constr option list -> unit m

  val get_funcs : Term.constr option list m
  val put_funcs : Term.constr option list -> unit m

  val runM : 'a m -> Term.constr option list -> Term.constr option list
    -> Environ.env -> Evd.evar_map
    -> ('a * Term.constr option list * Term.constr option list)
end
