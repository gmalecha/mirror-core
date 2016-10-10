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

(* idea: maybe we want a standard way of setting mx and mx2
 *)

(* standardized way of calling goal2_D' *)

Definition goal2_D'' n : Prop :=
  let thirdn := Nat.div n 3 in
  goal2_D' thirdn (2 * thirdn) n 0.

Set Printing Depth 5. (* To avoid printing large terms *)

Ltac the_tac := rewrite_strat (bottomup (hints pulling ; eval cbv beta)).

(*
Goal goal2_D'' 12.
  vm_compute. Time the_tac.
*)

(* Data: keeping track of values for runs for different n
   we report time-out if any runs time out
   TODO we should also report QED times. these are tactic run times.

   3: .113, .109, .109, .109, .109
   4: .178, .18, .178, .177, .181
   5: .274, .278, .274, .278, .274
   6: .686, .691, .686, .687, .686
   7: 1.175, 1.172, 1.167, 1.167, 1.165
   8: 2.067, 2.074, 2.086, 2.071, 2.092
   9: 5.79, 5.81, 5.876, 5.786, 5.84
   10: 11.108, 11.793, 11.043, 11.038, 11.202
   11: 21.77, 21.601, 21.539, 21.581, 21.527
   12: 61.032, 59.672, 59.612, 59.505, 59.68
   13: time out (but not all runs)
   14: all runs time out
*)

(* original settings 4 2 5 0 provide a baseline *)
(*
Goal goal2_D' 2 4 5 0.
  vm_compute.   Time rewrite_strat (bottomup (hints pulling ; eval cbv beta)).
Abort.
*)

(* code for the new test bench *)
Module Demo.
  Ltac prep := vm_compute.
  Ltac run := rewrite_strat (bottomup (hints pulling ; eval cbv beta)).
  Ltac cleanup := repeat (first [exists 0 |exists true]); tauto.
  Definition goal := goal2_D''.
End Demo.