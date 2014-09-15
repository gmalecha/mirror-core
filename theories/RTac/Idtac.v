Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Definition IDTAC : rtac typ expr subst :=
    fun ctx sub gl => More sub (GGoal gl).

  Theorem IDTAC_sound
  : forall tus tvs, rtac_sound tus tvs IDTAC.
  Proof.
    unfold IDTAC, rtac_sound.
    intros; subst.
    split; auto.
    simpl.
    revert tus tvs.
    induction ctx; simpl; intros.
    + forward. inv_all; subst.
      tauto.
    + specialize (IHctx tus (tvs ++ t :: nil)).
      forward. eauto.
    + specialize (IHctx (tus ++ t :: nil) tvs).
      forward. eauto.
    + specialize (IHctx tus tvs).
      forward; eauto. inv_all; subst.
      eauto.
  Qed.

End parameterized.
