Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {subst : Type}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Definition TRY (tac : rtac typ expr subst) : rtac typ expr subst :=
    fun ctx s g => match tac ctx s g with
                     | Fail => More_ s g
                     | x => x
                   end.

  Theorem TRY_sound
  : forall tus tvs tac, rtac_sound tus tvs tac -> rtac_sound tus tvs (TRY tac).
  Proof.
    unfold TRY, rtac_sound.
    intros; subst.
    specialize (H ctx s g _ eq_refl).
    destruct (tac ctx s g); auto.
    + intros; split; auto.
      simpl.
      forward.
  Qed.

End parameterized.
