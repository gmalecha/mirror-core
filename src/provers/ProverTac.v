Require Import List.
Require Import ExtLib.Tactics.Consider.
Require Import Expr.

Ltac t1 := 
  match goal with
    | _ => discriminate
    | _ => progress (hnf in *; simpl in *; intuition; subst)
    | [ x := _ : _ |- _ ] => subst x || (progress (unfold x in * ))
    | [ H : ex _ |- _ ] => destruct H
    | [ s : function _ |- _ ] => destruct s
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
    | [ H : _ = Some _ |- _ ] => rewrite H in *
    | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
      match X with
        | match _ with _ => _ end => fail 1
        | _ => consider X; try congruence
      end
    | [ H : Forall _ (_ :: _) |- _ ] =>
      rewrite Forall_cons in H
    | [ H : context [ expr_seq_dec ?A ?B ] |- _ ] =>
      generalize (expr_seq_dec_eq A B); destruct (expr_seq_dec A B); try congruence
  end.

Ltac t := repeat t1.
