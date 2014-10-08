Require Import ExtLib.Data.Sum.
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

  Definition IDTAC : rtac typ expr subst :=
    fun ctx sub gl => More_ sub gl.

  Theorem IDTAC_sound
  : forall tus tvs, rtac_sound tus tvs IDTAC.
  Proof.
    unfold IDTAC, rtac_sound.
    intros; subst.
    split; auto.
    simpl. intros. forward.
  Qed.

End parameterized.
