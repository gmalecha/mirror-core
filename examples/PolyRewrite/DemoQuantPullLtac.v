Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.


Theorem pull_ex_and_left
: forall T P Q, Basics.flip Basics.impl ((@ex T P) /\ Q) (exists n, P n /\ Q).
Proof.
  do 2 red. intros.
  firstorder.
Qed.

Theorem pull_ex_and_right
: forall T P Q, Basics.flip Basics.impl (Q /\ (@ex T P)) (exists n, Q /\ P n).
Proof.
  do 2 red; firstorder.
Qed.

Hint Rewrite pull_ex_and_left : pulling.
Hint Rewrite pull_ex_and_right : pulling.

(* test cases pulled from
   DemoPolyQuantPullRtac. *)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.

Existing Instance RelDec_lt.
Fixpoint goal2_D mx n (acc : nat) : Prop :=
  match n with
  | 0 =>
    if acc ?[ lt ] mx then
      exists x : nat, 0 = 0
    else
      0 = 0
  | S n =>
    goal2_D mx n (acc * 2) /\ goal2_D mx n (acc * 2 + 1)
  end.

Fixpoint goal2_D' mx mx2 n (acc : nat) : Prop :=
  match n with
  | 0 =>
    if acc ?[ lt ] mx then
      exists x : nat, 0 = 0
    else if acc ?[lt] mx2 then
           exists b : bool, 0 = 0 else
           0 = 0
  | S n =>
    goal2_D' mx mx2 n (acc * 2) /\ goal2_D' mx mx2 n (acc * 2 + 1)
  end.

Set Printing Depth 5. (* To avoid printing large terms *)
(* original settings *)
(*Goal goal2_D' 2 4 5 0.*)
Goal goal2_D' 2 4 12 0. (* takes long time *)
  vm_compute.
  Time rewrite_strat (bottomup (hints pulling ; eval cbv beta)).
(* the reflection based one does it in a few seconds *)
(* rewrite_strat takes 20s *)
(*
Time repeat progress (repeat setoid_rewrite pull_ex_and_left in H;
                      repeat setoid_rewrite pull_ex_and_right in H).
*)
(*
Time repeat first [ setoid_rewrite pull_ex_and_left in H
                  | setoid_rewrite pull_ex_and_right in H ].
 *)
(*
repeat exists true;
repeat exists 0; tauto.
Qed.
*)