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

module ReifyType (M : MONAD)
                 (R : REIFY with type 'a m = 'a M.m
                            with type result = Term.constr)
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

  val get_types : Term.constr list m
  val put_types : Term.constr list -> unit m

  val get_funcs : Term.constr list m
  val put_funcs : Term.constr list -> unit m

  val runM : 'a m -> Term.constr list -> Term.constr list -> Environ.env
    -> ('a * Term.constr list * Term.constr list)
end