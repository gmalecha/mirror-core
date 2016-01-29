Require Import Coq.Lists.List.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Reify.Reify.

Definition lambda_reify (typ func : Type) (reify_typ : Command typ)
: Command (expr typ func) :=
  Patterns.CFirst (Patterns.CApp (@ExprCore.App typ func) ::
                   Patterns.CAbs reify_typ (@ExprCore.Abs typ func) ::
                   Patterns.CVar (@ExprCore.Var typ func) ::
                   nil).