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

Fixpoint goal2 mx n (acc : nat) : Prop :=
  match n with
  | 0 =>
    if PeanoNat.Nat.ltb acc mx then
      exists x : nat, 0 = 0
    else
      0 = 0
  | S n =>
    goal2 mx n (acc * 2) /\ goal2 mx n (acc * 2 + 1)
  end.

Set Printing Depth 5. (* To avoid printing large terms *)
Goal goal2 10 8 0.
simpl.
Time rewrite_strat (bottomup (hints pulling ; eval cbv beta)).
(*
Time repeat progress (repeat setoid_rewrite pull_ex_and_left in H;
                      repeat setoid_rewrite pull_ex_and_right in H).
*)
(*
Time repeat first [ setoid_rewrite pull_ex_and_left in H
                  | setoid_rewrite pull_ex_and_right in H ].
*)
repeat exists 0; tauto.
Qed.
