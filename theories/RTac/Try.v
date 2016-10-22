Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Set}.
  Context {expr : Set}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Definition TRY (tac : rtac typ expr) : rtac typ expr :=
    fun ctx s g =>
      match tac ctx s g with
        | Fail => More_ s (GGoal g)
        | x => x
      end.

  Theorem TRY_sound
  : forall tac, rtac_sound tac -> rtac_sound (TRY tac).
  Proof.
    unfold TRY, rtac_sound.
    intros; subst.
    specialize (H ctx s g _ eq_refl).
    destruct (tac ctx s g); eauto using rtac_spec_More_.
  Qed.

End parameterized.

Hint Opaque TRY : typeclass_instances.
Typeclasses Opaque TRY.

Arguments TRY {_ _} _%rtac _ _ _.
