module Cmap = Map.Make
    (struct
      type t = Term.constr
      let compare = Term.constr_ord
    end)

module IntMap = Map.Make
    (struct
      type t = int
      let compare = Int.compare
    end)

exception ReificationFailure of (Term.constr Lazy.t)

type lazy_term =
  | Term of Term.constr
  | App of Term.constr * Term.constr array * int

let get_term (trm : lazy_term) =
  match trm with
    Term trm -> trm
  | App (trm,args,from) ->
    if from = -1 then trm
    else if from = Array.length args then
      Term.mkApp (trm, args)
    else Term.mkApp (trm, Array.sub args 0 (from+1))

type 'a environment =
  { mappings : 'a Cmap.t
  ; next     : int
  }

type reify_env =
  { env : Environ.env
  ; evm : Evd.evar_map
  ; bindings : Reify_Core.use_or_bind list
  ; typed_tables : (int * Term.constr) environment Cmap.t ref
  }

(** [reifier]s are the actual functions that get run **)
type 'a reifier =
  reify_env -> 'a

let reifier_bind (c : 'a reifier) (k : 'a -> 'b reifier) : 'b reifier =
  fun gl ->
    k (c gl) gl

let reifier_fmap (f : 'a -> 'b) (c : 'a reifier) : 'b reifier =
  fun gl -> f (c gl)

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

let reifier_under_binder ?name:(name=Names.Anonymous)
    (b : Reify_Core.use_or_bind) (t : Term.constr) (c : 'a reifier)
  : 'a reifier =
  fun gl -> c { gl with
                bindings = b :: gl.bindings
              ; env = Environ.push_rel (name, None, t) gl.env }

let reifier_run (c : 'a reifier) (gl : reify_env) = c gl
