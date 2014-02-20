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

  val reify_app : result m Lazy.t ->
                  (Term.constr -> result m) ->
                  (result -> result list -> result m) ->
                  Term.constr -> Term.constr array -> result m
end

module type Checker =
sig
  type 'a m
  val is_eqb : Term.constr -> Term.constr -> bool m
end

module CheckEq (M : MONAD) : Checker with type 'a m = 'a M.m

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
  (CHK : Checker with type 'a m = 'a M.m)
  : REIFY with type 'a m = 'a M.m
          with type result = int

module ReifyEnvOption
  (M : MONAD)
  (S : STATE with type state = Term.constr option list
             with type 'a m = 'a M.m)
  (CHK : Checker with type 'a m = 'a M.m)
  : REIFY with type 'a m = 'a M.m
          with type result = int

module SimpleReifyApp
  (M : MONAD)
  (R : sig type result end)
  : REIFY_APP with type 'a m = 'a M.m
              with type result = R.result

module ReifyAppDep
  (M : MONAD)
  (V : READER with type 'a m = 'a M.m
              with type env = Environ.env)
  (VE : READER with type 'a m = 'a M.m
               with type env = Evd.evar_map)
  (R : REIFY with type 'a m = 'a M.m)
  : REIFY_APP with type 'a m = 'a M.m
              with type result = R.result
