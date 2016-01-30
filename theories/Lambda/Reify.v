Require Import Coq.Lists.List.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Reify.Reify.

Definition lambda_reify (typ func : Type)
           (reify_typ : Command typ)
           (reify_func : Command func)
: Command (expr typ func) :=
  Patterns.CFirst (Patterns.CMap (@ExprCore.Inj typ func) reify_func ::
                   Patterns.CApp (@ExprCore.App typ func) ::
                   Patterns.CAbs reify_typ (@ExprCore.Abs typ func) ::
                   Patterns.CVar (@ExprCore.Var typ func) ::
                   nil).