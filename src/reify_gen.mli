val resolve_symbol : string -> string list -> string -> Term.constr

val to_positive : string -> int -> Term.constr
val to_N : string -> int -> Term.constr
val to_nat : string -> int -> Term.constr
val to_list : string -> Term.constr -> Term.constr list -> Term.constr

(** Monadic Interfaces **)
module type MONAD =
sig
  type 'a m

  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val ret : 'a -> 'a m
end

module type STATE =
sig
  type state
  type 'a m

  val get : state m
  val put : state -> unit m
end

module type READER =
sig
  type env
  type 'a m

  val ask : env m
  val local : (env -> env) -> 'a m -> 'a m
end

module type REIFY =
sig
  type result
  type 'a m

  val reify : Term.constr -> result m
end

module type REIFY_APP =
sig
  type result
  type 'a m

  val reify_app : (Term.constr -> result m) ->
                  (result -> result list -> result m) ->
                  Term.constr -> Term.constr array -> result m
end

module ReifyMap
  (R : REIFY)
  (F : sig type result
           val map : R.result R.m -> result R.m
       end)
  : REIFY with type result = F.result
          with type 'a m = 'a R.m

module ReifyEnv
  (M : MONAD)
  (S : STATE with type state = Term.constr list
             with type 'a m = 'a M.m)
  : REIFY with type 'a m = 'a M.m
          with type result = int

module SimpleReifyApp
  (M : MONAD)
  (R : sig type result end)
  : REIFY_APP with type 'a m = 'a M.m
              with type result = R.result