Require Import Coq.Lists.List.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Reify.Reify.

Definition lambda_reify (typ func : Set)
           (reify_typ : Command typ)
           (reify_func : Command func)
: Command (expr typ func) :=
  CFix
    (CFirst (CMap (@ExprCore.Inj typ func) reify_func ::
             CApp (CRec 0) (CRec 0) (@ExprCore.App typ func) ::
             CAbs reify_typ (CRec 0) (@ExprCore.Abs typ func) ::
             CVar (@ExprCore.Var typ func) ::
             nil)).
