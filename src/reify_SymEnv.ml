open Reify_gen
open Reify_ext
open Plugin_utils.Term_match

module Std = Plugin_utils.Coqstd.Std (struct let contrib_name = contrib_name end)

let to_positive = Std.to_positive

(** Reification of MirrorCore.SymEnv **)
let sym_env_pkg = ["MirrorCore";"SymEnv"]

let func = lazy (resolve_symbol sym_env_pkg "func")

module ReifySymEnv
  (M : MONAD)
  (S : STATE with type 'a m = 'a M.m
             with type state = Term.constr option list)
  (RT : REIFY with type 'a m = 'a M.m
              with type result = Term.constr)
  (E : READER with type 'a m = 'a M.m
              with type env = Environ.env)
  : REIFY with type 'a m = 'a M.m
          with type result = Term.constr =
struct
  type 'a m = 'a M.m
  type result = Term.constr

  module CHK = CheckEq (M)
  module RE = ReifyEnvOption (M) (S) (CHK)

  let reify (tm : Term.constr) : result m =
    M.bind (E.ask) (fun ctx ->
      matches ctx
	[ (Ignore,
	   fun _ ->
	     M.bind (RE.reify tm) (fun t ->
	       let idx = to_positive (1 + t) in
	       M.ret ( idx )))
	]
	tm)
end
