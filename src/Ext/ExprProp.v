Require Import List.
Require Import ExprCore.
Require Import ExprFacts.

Set Implicit Arguments.
Set Strict Implicit.

Section semantic.
  Variable ts : types. 
  Variable fs : functions ts.
  Variable uvars : env ts.
  Variable vars : env ts.

  Definition Provable (e : expr ts) : Prop :=
    exists p, exprD fs uvars vars e tvProp = Some p.
  
  Definition AllProvable (es : exprs ts) := Forall Provable es.
End semantic.

Theorem AllProvable_weaken : forall ts (fs : functions ts) u ue v ve es,
  AllProvable fs u v es -> AllProvable fs (u ++ ue) (v ++ ve) es.
Proof.
  induction 1; constructor; eauto.
  { unfold Provable in *. destruct H.
    eapply exprD_weaken in H. destruct H. intuition. eauto. }
Qed.

Theorem Forall_cons : forall T (P : T -> Prop) x xs, 
  Forall P (x :: xs) <-> P x /\ Forall P xs.
Proof.
  intuition; inversion H; auto. 
Qed.

Theorem AllProvable_app : forall ts (fs : functions ts) u v es es',
  AllProvable fs u v (es ++ es') <-> AllProvable fs u v es /\ AllProvable fs u v es'.
Proof.
  unfold AllProvable.
  induction es; simpl; intros.
  { intuition. }
  { repeat rewrite Forall_cons. rewrite IHes. intuition. }
Qed.
