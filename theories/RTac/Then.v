Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.

  Definition THEN (c1 c2 : rtac typ expr subst) : rtac typ expr subst :=
    fun ctx sub g =>
      match c1 ctx sub g with
        | More_ sub' g' => c2 ctx sub' g'
        | Solved sub => Solved sub
        | Fail => Fail
      end.

  Theorem THEN_sound
  : forall (tus tvs : list typ) (tac1 tac2 : rtac typ expr subst),
      rtac_sound tus tvs tac1 ->
      rtac_sound tus tvs tac2 ->
      rtac_sound tus tvs (THEN tac1 tac2).
  Proof.
    unfold THEN.
    intros.
    red. intros. subst.
    specialize (H ctx s g _ eq_refl).
    destruct (tac1 ctx s g); auto.
    specialize (H0 ctx s0 g0 _ eq_refl); auto.
    simpl in *.
    destruct (tac2 ctx s0 g0); auto.
    - simpl in *; intros; forward_reason.
      split; eauto.
      forward.
      firstorder.
    - simpl in *; intros; forward_reason.
      split; eauto.
      forward.
      firstorder.
  Qed.

End parameterized.