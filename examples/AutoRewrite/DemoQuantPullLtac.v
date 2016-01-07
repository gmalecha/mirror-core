Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.


Theorem pull_ex_and_left
: forall T P Q, Basics.impl ((@ex T P) /\ Q) (exists n, P n /\ Q).
Proof.
  red. intros.
  destruct H. destruct H. eexists; split; eauto.
Qed.

Theorem pull_ex_and_right
: forall T P Q, Basics.impl (Q /\ (@ex T P)) (exists n, Q /\ P n).
Proof.
  destruct 1. destruct H0.
  eexists; split; eauto.
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
Goal goal2 10 8 0 -> True.
simpl. intro.
Time repeat rewrite_strat (bottomup (hints pulling ; any subterms (hints pulling))) in H.
(*
Time repeat progress (repeat setoid_rewrite pull_ex_and_left in H;
                      repeat setoid_rewrite pull_ex_and_right in H).
*)
(*
Time repeat first [ setoid_rewrite pull_ex_and_left in H
                  | setoid_rewrite pull_ex_and_right in H ].
*)
exact I.
Qed.
