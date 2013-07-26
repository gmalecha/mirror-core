Require Import List.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section semantic.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Variable TI_prop : TypInstance0 typD Prop.
  Variable expr : Type.
  Context {Expr_expr : Expr typD expr}.

  Let tvProp := @typ0 _ _ _ TI_prop.

  Definition Provable uvars vars (e : expr) : Prop :=
    exists p, exprD uvars vars e tvProp = Some p.
  
  Definition AllProvable uvars vars (es : list expr) := 
    Forall (Provable uvars vars) es.
End semantic.

(*
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
*)
