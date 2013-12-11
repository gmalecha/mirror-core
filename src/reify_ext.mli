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
  (REX : sig val reify_evar : Term.constr -> int M.m end)
  (RA : REIFY_APP with type 'a m = 'a M.m
                  with type result = EXPR.e_result)
  : REIFY with type 'a m = 'a M.m
          with type result = EXPR.e_result

module ReifyExtTypes
  (PARAM : sig type 'a m
	       val ret : 'a -> 'a m
	       val bind : 'a m -> ('a -> 'b m) -> 'b m
	       val put_types : Term.constr option list -> unit m
	       val get_types : Term.constr option list m
	       val under_type : bool -> 'a m -> 'a m
	       val lookup_type : int -> int m
           end)
  : REIFY with type 'a m = 'a PARAM.m
          with type result = Term.constr

module ExprBuilder
  (EXT : sig val ext_type : Term.constr Lazy.t end) :
sig
  type e_result = Term.constr
  type t_result = Term.constr

  val mkVar : int -> e_result
  val mkUVar : int -> e_result
  val mkAbs : t_result -> e_result -> e_result
  val mkApp : e_result -> e_result -> e_result
  val mkInj : Term.constr -> e_result
end
