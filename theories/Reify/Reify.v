Require PluginUtils.PluginUtils.
Require Import MirrorCore.Reify.Patterns.

Declare ML Module "reify_Lambda_plugin".

Export MirrorCore.Reify.Patterns.
Require Import MirrorCore.Reify.ReifyClass.

Ltac reify_with_class X :=
  lazymatch goal with
  | |- ?T =>
    let cls := constr:(@reify_scheme T _) in
    tryif has_evar cls
    then fail "Failed to find reification scheme for" T
    else let cls := eval red in cls in
         let cls := eval red in cls in
         let k x := exact x in
         reify_expr cls k [[ True ]] [[ X ]]
  end.

Ltac reify_type_with_class X :=
  let x := type of X in
  reify_with_class x.

(** These are the notations for inline reification *)
Notation "'<<:' X ':>>'" :=
  ltac:(reify_with_class X) (at level 0, only parsing).
Notation "'<::' X '::>'" :=
  ltac:(reify_type_with_class X) (at level 0, only parsing).

Require Export MirrorCore.Reify.ReifyClass.