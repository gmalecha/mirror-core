(** TODO: This file should be renamed once I figure
 ** out the best way to organize reification and
 ** the rest of the code.
 **)
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.SymEnv.

Add ML Path "../../src".
Declare ML Module "reify_Ext_SymEnv_plugin".

(** reify_expr : term -> (expr -> tactic) -> tactic **)

Definition eq_nat : nat -> nat -> Prop := @eq nat.

Ltac reify_goal :=
  match goal with
    | |- ?X =>
      let k t e := pose t ; pose e in
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