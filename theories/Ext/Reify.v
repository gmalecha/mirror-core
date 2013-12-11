(** TODO: This file should be renamed once I figure
 ** out the best way to organize reification and
 ** the rest of the code.
 **)
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.SymEnv.

Add ML Path "../../src/_build".
Declare ML Module "reify_Ext_SymEnv_plugin".

(** reify_expr : term -> (expr -> tactic) -> tactic **)

Definition eq_nat : nat -> nat -> Prop := @eq nat.

Ltac reify_goal :=
  match goal with
    | |- ?X =>
      let k t f us e := pose e in
      reify_expr X k
  end.

Goal eq_nat 0 0.
reify_goal.
reflexivity.
Qed.

Goal eq_nat (1 + 0) 1.
reify_goal.
reflexivity.
Qed.

Goal eq_nat 20 20.
reify_goal.
reflexivity.
Qed.

Goal 0 = 0.
reify_goal.
reflexivity.
Qed.

Goal exists x, x = 0.
eexists.
reify_goal.
reflexivity.
Qed.

Definition foo (t : bool) (tr fa : nat) := if t then tr else fa.

Goal 0 = foo true 0 1.
reify_goal.
reflexivity.
Qed.

Parameter trial : nat -> forall T, T -> Prop.

Goal trial 0 _ 0.
reify_goal.
admit.
Qed.